// =============================================================================
// SN-F (Slave Node) - Memory Interface Node
// =============================================================================
// Requirements: 6.1, 6.2, 6.4
// This module provides the interface between the coherent network and DDR/HBM
// memory controllers. It handles protocol conversion from CHI to memory
// controller protocols and supports multi-channel parallel access.
// =============================================================================

import coh_noc_pkg::*;

module sn_f #(
    parameter int NUM_CHANNELS = 4,        // Number of memory channels
    parameter logic [7:0] NODE_ID = 8'h10, // Node ID for this SN-F
    parameter int ADDR_WIDTH = 48,         // Address width
    parameter int DATA_WIDTH = 512         // Data width (matches CHI)
)(
    input logic clk,
    input logic rst_n,
    
    // Network Interface - REQ Channel Input
    xp_port_if.slave  req_in,
    
    // Network Interface - RSP Channel Output
    xp_port_if.master rsp_out,
    
    // Network Interface - DAT Channel Output
    xp_port_if.master dat_out,
    
    // DDR/HBM Memory Controller Interfaces (multi-channel)
    ddr_if.master ddr_ctrl[NUM_CHANNELS-1:0]
);

    // =============================================================================
    // Internal State and Transaction Tracking
    // =============================================================================
    
    // Transaction buffer to track outstanding memory requests
    typedef struct packed {
        logic         valid;
        logic [11:0]  txn_id;
        logic [7:0]   src_id;
        logic [7:0]   tgt_id;
        req_opcode_e  opcode;
        logic [47:0]  addr;
        logic [2:0]   size;
        logic [2:0]   channel_id;  // Which memory channel is handling this
        logic         is_read;
    } txn_buffer_entry_t;
    
    localparam int TXN_BUFFER_SIZE = 16;
    txn_buffer_entry_t txn_buffer[TXN_BUFFER_SIZE-1:0];
    
    // Channel allocation state
    logic [NUM_CHANNELS-1:0] channel_busy;
    logic [2:0] next_channel;
    
    // Enhanced load balancing metrics (Requirement 6.4)
    logic [7:0] channel_load[NUM_CHANNELS-1:0];  // Track outstanding requests per channel
    logic [2:0] least_loaded_channel;
    
    // =============================================================================
    // REQ Channel Processing (Requirements 6.1, 6.2)
    // =============================================================================
    
    // Decode incoming request
    logic req_is_read, req_is_write;
    logic [2:0] selected_channel;
    logic [TXN_BUFFER_SIZE-1:0] txn_buffer_free;
    logic [$clog2(TXN_BUFFER_SIZE)-1:0] free_txn_idx;
    
    always_comb begin
        // Determine if request is read or write
        req_is_read = 1'b0;
        req_is_write = 1'b0;
        
        if (req_in.valid) begin
            case (req_in.flit.req.opcode)
                REQ_READ_SHARED, REQ_READ_CLEAN, REQ_READ_ONCE,
                REQ_READ_NO_SNOOP, REQ_READ_UNIQUE:
                    req_is_read = 1'b1;
                    
                REQ_WRITE_BACK_FULL, REQ_WRITE_CLEAN_FULL,
                REQ_WRITE_UNIQUE_FULL, REQ_WRITE_UNIQUE_PTL,
                REQ_WRITE_NO_SNOOP_FULL, REQ_WRITE_NO_SNOOP_PTL:
                    req_is_write = 1'b1;
                    
                default: begin
                    req_is_read = 1'b0;
                    req_is_write = 1'b0;
                end
            endcase
        end
        
        // Find free transaction buffer entry
        txn_buffer_free = '0;
        for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
            txn_buffer_free[i] = ~txn_buffer[i].valid;
        end
        
        // Priority encoder to find first free entry
        free_txn_idx = 0;
        for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
            if (txn_buffer_free[i] && free_txn_idx == 0) begin
                free_txn_idx = i;
            end
        end
    end
    
    // =============================================================================
    // Multi-Channel Load Balancing and Scheduling (Requirement 6.4)
    // =============================================================================
    
    // Track load per channel - count outstanding transactions
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                channel_load[ch] <= '0;
            end
        end else begin
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                logic [7:0] new_load;
                new_load = channel_load[ch];
                
                // Increment when new request allocated to this channel
                if (req_in.valid && req_in.ready && selected_channel == ch) begin
                    new_load = new_load + 1;
                end
                
                // Decrement when transaction completes on this channel
                for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
                    if (txn_buffer[i].valid && txn_buffer[i].channel_id == ch) begin
                        if ((txn_buffer[i].is_read && 
                             ddr_ctrl[ch].rd_valid && 
                             ddr_ctrl[ch].rd_last &&
                             dat_out.ready) ||
                            (!txn_buffer[i].is_read &&
                             ddr_ctrl[ch].wr_valid &&
                             ddr_ctrl[ch].wr_last &&
                             ddr_ctrl[ch].wr_ready &&
                             rsp_out.ready)) begin
                            new_load = new_load - 1;
                        end
                    end
                end
                
                channel_load[ch] <= new_load;
            end
        end
    end
    
    // Find least loaded channel for better load balancing
    always_comb begin
        least_loaded_channel = 0;
        for (int ch = 1; ch < NUM_CHANNELS; ch++) begin
            if (channel_load[ch] < channel_load[least_loaded_channel]) begin
                least_loaded_channel = ch[2:0];
            end
        end
    end
    
    // Round-robin channel selection for fairness
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            next_channel <= '0;
        end else begin
            if (req_in.valid && req_in.ready) begin
                // Move to next channel in round-robin fashion
                if (next_channel == NUM_CHANNELS - 1)
                    next_channel <= '0;
                else
                    next_channel <= next_channel + 1;
            end
        end
    end
    
    // Enhanced channel selection with multiple strategies
    // Priority: 1) Address interleaving, 2) Least loaded, 3) Round-robin
    always_comb begin
        logic [2:0] addr_based_channel;
        logic [2:0] rr_channel;
        logic found_rr;
        
        // Use address bits for channel selection (interleaving)
        // This provides better load distribution for sequential accesses
        addr_based_channel = req_in.flit.req.addr[8:6] % NUM_CHANNELS;
        
        // Strategy selection based on channel availability
        if (!channel_busy[addr_based_channel] && 
            ddr_ctrl[addr_based_channel].cmd_ready) begin
            // Prefer address-based interleaving if channel is available
            selected_channel = addr_based_channel;
        end else if (!channel_busy[least_loaded_channel] &&
                     ddr_ctrl[least_loaded_channel].cmd_ready) begin
            // Use least loaded channel if address-based is busy
            selected_channel = least_loaded_channel;
        end else begin
            // Fall back to round-robin
            rr_channel = next_channel;
            found_rr = 1'b0;
            
            // Find next available channel in round-robin order
            for (int offset = 0; offset < NUM_CHANNELS; offset++) begin
                logic [2:0] candidate;
                candidate = (next_channel + offset) % NUM_CHANNELS;
                if (!channel_busy[candidate] && ddr_ctrl[candidate].cmd_ready && !found_rr) begin
                    rr_channel = candidate;
                    found_rr = 1'b1;
                end
            end
            
            selected_channel = rr_channel;
        end
    end
    
    // =============================================================================
    // Transaction Buffer Management
    // =============================================================================
    
    logic txn_buffer_has_space;
    assign txn_buffer_has_space = |txn_buffer_free;
    
    // Accept request if we have buffer space and selected channel is ready
    assign req_in.ready = txn_buffer_has_space && 
                          ddr_ctrl[selected_channel].cmd_ready &&
                          !channel_busy[selected_channel];
    
    // Allocate transaction buffer entry
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
                txn_buffer[i].valid <= 1'b0;
            end
        end else begin
            // Allocate new transaction
            if (req_in.valid && req_in.ready) begin
                txn_buffer[free_txn_idx].valid      <= 1'b1;
                txn_buffer[free_txn_idx].txn_id     <= req_in.flit.req.txn_id;
                txn_buffer[free_txn_idx].src_id     <= req_in.flit.req.src_id;
                txn_buffer[free_txn_idx].tgt_id     <= req_in.flit.req.tgt_id;
                txn_buffer[free_txn_idx].opcode     <= req_in.flit.req.opcode;
                txn_buffer[free_txn_idx].addr       <= req_in.flit.req.addr;
                txn_buffer[free_txn_idx].size       <= req_in.flit.req.size;
                txn_buffer[free_txn_idx].channel_id <= selected_channel;
                txn_buffer[free_txn_idx].is_read    <= req_is_read;
            end
            
            // Deallocate completed transactions
            for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
                if (txn_buffer[i].valid) begin
                    // Check if this transaction completed on any channel
                    for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                        if (txn_buffer[i].channel_id == ch) begin
                            if (txn_buffer[i].is_read && 
                                ddr_ctrl[ch].rd_valid && 
                                ddr_ctrl[ch].rd_last &&
                                dat_out.ready) begin
                                txn_buffer[i].valid <= 1'b0;
                            end else if (!txn_buffer[i].is_read &&
                                        ddr_ctrl[ch].wr_valid &&
                                        ddr_ctrl[ch].wr_last &&
                                        ddr_ctrl[ch].wr_ready &&
                                        rsp_out.ready) begin
                                txn_buffer[i].valid <= 1'b0;
                            end
                        end
                    end
                end
            end
        end
    end
    
    // =============================================================================
    // DDR Command Generation (Protocol Conversion)
    // =============================================================================
    
    genvar ch;
    generate
        for (ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_channel_ctrl
            
            // Command interface
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    ddr_ctrl[ch].cmd_valid <= 1'b0;
                    ddr_ctrl[ch].cmd_read  <= 1'b0;
                    ddr_ctrl[ch].cmd_addr  <= '0;
                    ddr_ctrl[ch].cmd_len   <= '0;
                    ddr_ctrl[ch].cmd_size  <= '0;
                    channel_busy[ch]       <= 1'b0;
                end else begin
                    // Issue command when request arrives for this channel
                    if (req_in.valid && req_in.ready && selected_channel == ch) begin
                        ddr_ctrl[ch].cmd_valid <= 1'b1;
                        ddr_ctrl[ch].cmd_read  <= req_is_read;
                        ddr_ctrl[ch].cmd_addr  <= req_in.flit.req.addr[ADDR_WIDTH-1:0];
                        ddr_ctrl[ch].cmd_len   <= 8'h00;  // Single beat
                        ddr_ctrl[ch].cmd_size  <= req_in.flit.req.size;
                        channel_busy[ch]       <= 1'b1;
                    end else if (ddr_ctrl[ch].cmd_valid && ddr_ctrl[ch].cmd_ready) begin
                        ddr_ctrl[ch].cmd_valid <= 1'b0;
                    end
                    
                    // Clear busy when transaction completes
                    if (channel_busy[ch]) begin
                        if ((ddr_ctrl[ch].rd_valid && ddr_ctrl[ch].rd_last && ddr_ctrl[ch].rd_ready) ||
                            (ddr_ctrl[ch].wr_valid && ddr_ctrl[ch].wr_last && ddr_ctrl[ch].wr_ready)) begin
                            channel_busy[ch] <= 1'b0;
                        end
                    end
                end
            end
            
        end
    endgenerate
    
    // =============================================================================
    // Write Data Handling
    // =============================================================================
    
    // For write requests, we need to receive data from the network
    // In a complete implementation, this would buffer write data from DAT channel
    // For now, we'll handle single-beat writes
    
    generate
        for (ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_write_data
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    ddr_ctrl[ch].wr_valid <= 1'b0;
                    ddr_ctrl[ch].wr_data  <= '0;
                    ddr_ctrl[ch].wr_strb  <= '0;
                    ddr_ctrl[ch].wr_last  <= 1'b0;
                end else begin
                    // Generate write data when command is issued for write
                    if (req_in.valid && req_in.ready && 
                        selected_channel == ch && req_is_write) begin
                        ddr_ctrl[ch].wr_valid <= 1'b1;
                        ddr_ctrl[ch].wr_data  <= req_in.flit.req.padding[511:0];  // Data from padding
                        ddr_ctrl[ch].wr_strb  <= '1;  // All bytes valid
                        ddr_ctrl[ch].wr_last  <= 1'b1;
                    end else if (ddr_ctrl[ch].wr_valid && ddr_ctrl[ch].wr_ready) begin
                        ddr_ctrl[ch].wr_valid <= 1'b0;
                        ddr_ctrl[ch].wr_last  <= 1'b0;
                    end
                end
            end
        end
    endgenerate
    
    // =============================================================================
    // Read Data Response Generation
    // =============================================================================
    
    // Find which transaction buffer entry matches the read data
    logic [$clog2(TXN_BUFFER_SIZE)-1:0] rd_txn_idx;
    logic rd_txn_found;
    logic [2:0] rd_channel;
    
    always_comb begin
        rd_txn_found = 1'b0;
        rd_txn_idx = 0;
        rd_channel = 0;
        
        // Search for matching read transaction
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            if (ddr_ctrl[ch].rd_valid && !rd_txn_found) begin
                for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
                    if (txn_buffer[i].valid && 
                        txn_buffer[i].is_read &&
                        txn_buffer[i].channel_id == ch &&
                        !rd_txn_found) begin
                        rd_txn_found = 1'b1;
                        rd_txn_idx = i;
                        rd_channel = ch[2:0];
                    end
                end
            end
        end
    end
    
    // Generate DAT response for read completion
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dat_out.valid <= 1'b0;
            dat_out.flit  <= '0;
            dat_out.vc_id <= VC_DAT;
            dat_out.channel_type <= 2'b10;  // DAT channel
        end else begin
            if (rd_txn_found && ddr_ctrl[rd_channel].rd_valid && dat_out.ready) begin
                dat_out.valid <= 1'b1;
                dat_out.vc_id <= VC_DAT;
                dat_out.channel_type <= 2'b10;
                
                // Pack DAT flit
                dat_out.flit.dat <= pack_dat_flit(
                    .opcode(DAT_COMP_DATA),
                    .txn_id(txn_buffer[rd_txn_idx].txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(txn_buffer[rd_txn_idx].src_id),
                    .home_node_id(NODE_ID),
                    .dbid(8'h00),
                    .data(ddr_ctrl[rd_channel].rd_data),
                    .be(64'hFFFFFFFFFFFFFFFF),
                    .data_id(3'b000),
                    .resp(ddr_ctrl[rd_channel].rd_resp)
                );
            end else if (dat_out.valid && dat_out.ready) begin
                dat_out.valid <= 1'b0;
            end
        end
    end
    
    // Connect read ready signals
    generate
        for (ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_rd_ready
            assign ddr_ctrl[ch].rd_ready = dat_out.ready || !dat_out.valid;
        end
    endgenerate
    
    // =============================================================================
    // Write Completion Response Generation
    // =============================================================================
    
    // Find which transaction buffer entry matches the write completion
    logic [$clog2(TXN_BUFFER_SIZE)-1:0] wr_txn_idx;
    logic wr_txn_found;
    logic [2:0] wr_channel;
    
    always_comb begin
        wr_txn_found = 1'b0;
        wr_txn_idx = 0;
        wr_channel = 0;
        
        // Search for matching write transaction
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            if (ddr_ctrl[ch].wr_valid && ddr_ctrl[ch].wr_last && !wr_txn_found) begin
                for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
                    if (txn_buffer[i].valid && 
                        !txn_buffer[i].is_read &&
                        txn_buffer[i].channel_id == ch &&
                        !wr_txn_found) begin
                        wr_txn_found = 1'b1;
                        wr_txn_idx = i;
                        wr_channel = ch[2:0];
                    end
                end
            end
        end
    end
    
    // Generate RSP response for write completion
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rsp_out.valid <= 1'b0;
            rsp_out.flit  <= '0;
            rsp_out.vc_id <= VC_RSP;
            rsp_out.channel_type <= 2'b01;  // RSP channel
        end else begin
            if (wr_txn_found && ddr_ctrl[wr_channel].wr_ready && rsp_out.ready) begin
                rsp_out.valid <= 1'b1;
                rsp_out.vc_id <= VC_RSP;
                rsp_out.channel_type <= 2'b01;
                
                // Pack RSP flit
                rsp_out.flit.rsp <= pack_rsp_flit(
                    .opcode(RSP_COMP),
                    .txn_id(txn_buffer[wr_txn_idx].txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(txn_buffer[wr_txn_idx].src_id),
                    .dbid(8'h00),
                    .resp(2'b00),  // OK response
                    .fwd_state(2'b00)
                );
            end else if (rsp_out.valid && rsp_out.ready) begin
                rsp_out.valid <= 1'b0;
            end
        end
    end
    
    // =============================================================================
    // Credit Flow Control
    // =============================================================================
    
    // Calculate available credits based on free transaction buffer entries
    logic [7:0] used_entries;
    always_comb begin
        used_entries = 0;
        for (int i = 0; i < TXN_BUFFER_SIZE; i++) begin
            if (txn_buffer[i].valid) begin
                used_entries = used_entries + 1;
            end
        end
    end
    
    assign req_in.credit_count = TXN_BUFFER_SIZE - used_entries;
    assign dat_out.credit_return = 1'b0;  // Not used for output
    assign rsp_out.credit_return = 1'b0;  // Not used for output

endmodule : sn_f
