// HN-F Top Level Module
import coh_noc_pkg::*;

module hn_f #(
    parameter int CACHE_SIZE = SLC_SIZE,
    parameter int NUM_WAYS = SLC_WAYS,
    parameter int DIRECTORY_ENTRIES = 4096,
    parameter int FILTER_ENTRIES = 1024,
    parameter int ADDR_WIDTH = 48,
    parameter int NODE_ID_WIDTH = 8,
    parameter int MAX_NODES = 16,
    parameter logic [NODE_ID_WIDTH-1:0] NODE_ID = 8'h00
)(
    input  logic clk,
    input  logic rst_n,
    
    // Network Interface
    xp_port_if.slave  req_in,
    xp_port_if.master req_out,
    xp_port_if.slave  rsp_in,
    xp_port_if.master rsp_out,
    xp_port_if.slave  dat_in,
    xp_port_if.master dat_out,
    xp_port_if.master snp_out,
    xp_port_if.slave  snp_in,
    
    // Memory Interface
    axi_if.master mem_if,
    
    // Configuration
    input  logic filter_enable,
    input  logic broadcast_mode,
    input  logic [3:0] filter_threshold,
    output logic [31:0] total_snoops,
    output logic [31:0] filtered_snoops,
    output logic [31:0] broadcast_snoops,
    output logic protocol_error,
    output logic [7:0] error_code
);

    // =============================================================================
    // Internal Signals and Interfaces
    // =============================================================================
    
    // SLC Cache Interface
    logic                    slc_req_valid;
    logic                    slc_req_ready;
    logic [ADDR_WIDTH-1:0]   slc_req_addr;
    logic                    slc_req_write;
    logic [511:0]            slc_req_wdata;
    logic [63:0]             slc_req_be;
    
    logic                    slc_rsp_valid;
    logic                    slc_rsp_ready;
    logic                    slc_rsp_hit;
    logic [511:0]            slc_rsp_rdata;
    logic                    slc_rsp_dirty;
    
    logic                    slc_wb_valid;
    logic                    slc_wb_ready;
    logic [ADDR_WIDTH-1:0]   slc_wb_addr;
    logic [511:0]            slc_wb_data;
    
    // Directory Manager Interface
    logic                    dir_query_valid;
    logic                    dir_query_ready;
    logic [ADDR_WIDTH-1:0]   dir_query_addr;
    logic                    dir_query_rsp_valid;
    logic                    dir_query_rsp_ready;
    directory_entry_t        dir_query_rsp_entry;
    logic                    dir_query_hit;
    
    logic                    dir_update_valid;
    logic                    dir_update_ready;
    logic [ADDR_WIDTH-1:0]   dir_update_addr;
    directory_entry_t        dir_update_entry;
    logic                    dir_update_allocate;
    
    // Snoop Filter Interface
    logic                    sf_snoop_req_valid;
    logic                    sf_snoop_req_ready;
    logic [ADDR_WIDTH-1:0]   sf_snoop_req_addr;
    snp_opcode_e             sf_snoop_req_opcode;
    logic [NODE_ID_WIDTH-1:0] sf_snoop_req_src;
    
    logic                    sf_filtered_snoop_valid;
    logic                    sf_filtered_snoop_ready;
    logic [ADDR_WIDTH-1:0]   sf_filtered_snoop_addr;
    snp_opcode_e             sf_filtered_snoop_opcode;
    logic [MAX_NODES-1:0]    sf_filtered_snoop_targets;
    logic [NODE_ID_WIDTH-1:0] sf_filtered_snoop_src;
    
    logic                    sf_track_valid;
    logic [ADDR_WIDTH-1:0]   sf_track_addr;
    logic [NODE_ID_WIDTH-1:0] sf_track_node_id;
    track_operation_e        sf_track_op;
    
    // MESI State Machine Interface
    logic                    mesi_req_valid;
    logic                    mesi_req_ready;
    logic [ADDR_WIDTH-1:0]   mesi_req_addr;
    logic [3:0]              mesi_req_event;
    logic [NODE_ID_WIDTH-1:0] mesi_req_node_id;
    directory_entry_t        mesi_current_state;
    
    logic                    mesi_rsp_valid;
    logic                    mesi_rsp_ready;
    directory_entry_t        mesi_new_state;
    logic [15:0]             mesi_required_actions;
    logic                    mesi_state_changed;
    
    logic                    mesi_snoop_valid;
    logic                    mesi_snoop_ready;
    logic [ADDR_WIDTH-1:0]   mesi_snoop_addr;
    snp_opcode_e             mesi_snoop_opcode;
    logic [15:0]             mesi_snoop_targets;
    
    // =============================================================================
    // Component Instantiations
    // =============================================================================
    
    // System Level Cache (SLC)
    slc_cache #(
        .CACHE_SIZE(CACHE_SIZE),
        .NUM_WAYS(NUM_WAYS),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_slc_cache (
        .clk(clk),
        .rst_n(rst_n),
        
        .req_valid(slc_req_valid),
        .req_ready(slc_req_ready),
        .req_addr(slc_req_addr),
        .req_write(slc_req_write),
        .req_wdata(slc_req_wdata),
        .req_be(slc_req_be),
        
        .rsp_valid(slc_rsp_valid),
        .rsp_ready(slc_rsp_ready),
        .rsp_hit(slc_rsp_hit),
        .rsp_rdata(slc_rsp_rdata),
        .rsp_dirty(slc_rsp_dirty),
        
        .wb_valid(slc_wb_valid),
        .wb_ready(slc_wb_ready),
        .wb_addr(slc_wb_addr),
        .wb_data(slc_wb_data)
    );
    
    // Directory Manager
    directory_manager #(
        .DIRECTORY_ENTRIES(DIRECTORY_ENTRIES),
        .ADDR_WIDTH(ADDR_WIDTH),
        .NODE_ID_WIDTH(NODE_ID_WIDTH)
    ) u_directory_manager (
        .clk(clk),
        .rst_n(rst_n),
        
        .query_valid(dir_query_valid),
        .query_ready(dir_query_ready),
        .query_addr(dir_query_addr),
        .query_rsp_valid(dir_query_rsp_valid),
        .query_rsp_ready(dir_query_rsp_ready),
        .query_rsp_entry(dir_query_rsp_entry),
        .query_hit(dir_query_hit),
        
        .update_valid(dir_update_valid),
        .update_ready(dir_update_ready),
        .update_addr(dir_update_addr),
        .update_entry(dir_update_entry),
        .update_allocate(dir_update_allocate),
        
        .op_valid(1'b0),
        .op_ready(),
        .op_addr('0),
        .op_node_id('0),
        .op_type('0),
        .op_rsp_valid(),
        .op_rsp_ready(1'b0),
        .op_rsp_entry(),
        .op_success(),
        
        .evict_valid(),
        .evict_ready(1'b1),
        .evict_addr(),
        .evict_entry()
    );
    
    // Snoop Filter
    snoop_filter #(
        .FILTER_ENTRIES(FILTER_ENTRIES),
        .ADDR_WIDTH(ADDR_WIDTH),
        .NODE_ID_WIDTH(NODE_ID_WIDTH),
        .MAX_NODES(MAX_NODES)
    ) u_snoop_filter (
        .clk(clk),
        .rst_n(rst_n),
        
        .snoop_req_valid(sf_snoop_req_valid),
        .snoop_req_ready(sf_snoop_req_ready),
        .snoop_req_addr(sf_snoop_req_addr),
        .snoop_req_opcode(sf_snoop_req_opcode),
        .snoop_req_src(sf_snoop_req_src),
        
        .filtered_snoop_valid(sf_filtered_snoop_valid),
        .filtered_snoop_ready(sf_filtered_snoop_ready),
        .filtered_snoop_addr(sf_filtered_snoop_addr),
        .filtered_snoop_opcode(sf_filtered_snoop_opcode),
        .filtered_snoop_targets(sf_filtered_snoop_targets),
        .filtered_snoop_src(sf_filtered_snoop_src),
        
        .track_valid(sf_track_valid),
        .track_addr(sf_track_addr),
        .track_node_id(sf_track_node_id),
        .track_op(sf_track_op),
        
        .total_snoops(total_snoops),
        .filtered_snoops(filtered_snoops),
        .broadcast_snoops(broadcast_snoops),
        
        .filter_enable(filter_enable),
        .broadcast_mode(broadcast_mode),
        .filter_threshold(filter_threshold)
    );
    
    // MESI State Machine
    mesi_state_machine #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .NODE_ID_WIDTH(NODE_ID_WIDTH)
    ) u_mesi_state_machine (
        .clk(clk),
        .rst_n(rst_n),
        
        .req_valid(mesi_req_valid),
        .req_ready(mesi_req_ready),
        .req_addr(mesi_req_addr),
        .req_event(mesi_req_event),
        .req_node_id(mesi_req_node_id),
        .current_state(mesi_current_state),
        
        .rsp_valid(mesi_rsp_valid),
        .rsp_ready(mesi_rsp_ready),
        .new_state(mesi_new_state),
        .required_actions(mesi_required_actions),
        .state_changed(mesi_state_changed),
        
        .snoop_valid(mesi_snoop_valid),
        .snoop_ready(mesi_snoop_ready),
        .snoop_addr(mesi_snoop_addr),
        .snoop_opcode(mesi_snoop_opcode),
        .snoop_targets(mesi_snoop_targets),
        
        .protocol_error(protocol_error),
        .error_code(error_code)
    );
    
    // =============================================================================
    // Request Processing State Machine
    // =============================================================================
    
    typedef enum logic [3:0] {
        REQ_IDLE,
        REQ_DIR_LOOKUP,
        REQ_SLC_ACCESS,
        REQ_MESI_PROCESS,
        REQ_SNOOP_SEND,
        REQ_MEM_ACCESS,
        REQ_RESPONSE,
        REQ_ERROR
    } req_state_e;
    
    req_state_e req_state, req_next_state;
    
    // Request processing registers
    logic [ADDR_WIDTH-1:0]   current_req_addr;
    logic [NODE_ID_WIDTH-1:0] current_req_src;
    logic [11:0]             current_req_txn_id;
    req_opcode_e             current_req_opcode;
    logic [2:0]              current_req_size;
    logic [511:0]            current_req_data;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_state <= REQ_IDLE;
        end else begin
            req_state <= req_next_state;
        end
    end
    
    // Request state machine logic
    always_comb begin
        req_next_state = req_state;
        
        case (req_state)
            REQ_IDLE: begin
                if (req_in.valid) begin
                    req_next_state = REQ_DIR_LOOKUP;
                end
            end
            
            REQ_DIR_LOOKUP: begin
                if (dir_query_rsp_valid) begin
                    req_next_state = REQ_SLC_ACCESS;
                end
            end
            
            REQ_SLC_ACCESS: begin
                if (slc_rsp_valid) begin
                    req_next_state = REQ_MESI_PROCESS;
                end
            end
            
            REQ_MESI_PROCESS: begin
                if (mesi_rsp_valid) begin
                    if (mesi_required_actions[0]) begin // send_snoop_*
                        req_next_state = REQ_SNOOP_SEND;
                    end else if (mesi_required_actions[3] || mesi_required_actions[4]) begin // send_mem_*
                        req_next_state = REQ_MEM_ACCESS;
                    end else begin
                        req_next_state = REQ_RESPONSE;
                    end
                end
            end
            
            REQ_SNOOP_SEND: begin
                if (sf_filtered_snoop_valid && snp_out.ready) begin
                    req_next_state = REQ_RESPONSE;
                end
            end
            
            REQ_MEM_ACCESS: begin
                if (mem_if.arready || mem_if.awready) begin
                    req_next_state = REQ_RESPONSE;
                end
            end
            
            REQ_RESPONSE: begin
                if (rsp_out.ready || dat_out.ready) begin
                    req_next_state = REQ_IDLE;
                end
            end
            
            REQ_ERROR: begin
                req_next_state = REQ_IDLE;
            end
        endcase
    end
    
    // =============================================================================
    // Interface Control Logic
    // =============================================================================
    
    // REQ Channel Input Processing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_req_addr <= '0;
            current_req_src <= '0;
            current_req_txn_id <= '0;
            current_req_opcode <= REQ_READ_SHARED;
            current_req_size <= '0;
            current_req_data <= '0;
        end else begin
            if (req_state == REQ_IDLE && req_in.valid) begin
                current_req_addr <= req_in.flit.req.addr;
                current_req_src <= req_in.flit.req.src_id;
                current_req_txn_id <= req_in.flit.req.txn_id;
                current_req_opcode <= req_opcode_e'(req_in.flit.req.opcode);
                current_req_size <= req_in.flit.req.size;
            end
        end
    end
    
    // Directory interface control
    assign dir_query_valid = (req_state == REQ_DIR_LOOKUP);
    assign dir_query_addr = current_req_addr;
    assign dir_query_rsp_ready = (req_state == REQ_DIR_LOOKUP);
    
    // SLC interface control
    assign slc_req_valid = (req_state == REQ_SLC_ACCESS);
    assign slc_req_addr = current_req_addr;
    assign slc_req_write = (current_req_opcode inside {REQ_WRITE_BACK_FULL, REQ_WRITE_CLEAN_FULL, 
                                                      REQ_WRITE_UNIQUE_FULL, REQ_WRITE_UNIQUE_PTL});
    assign slc_req_wdata = current_req_data;
    assign slc_req_be = '1; // Full cache line
    assign slc_rsp_ready = (req_state == REQ_SLC_ACCESS);
    
    // MESI state machine control
    assign mesi_req_valid = (req_state == REQ_MESI_PROCESS);
    assign mesi_req_addr = current_req_addr;
    assign mesi_req_node_id = current_req_src;
    assign mesi_current_state = dir_query_rsp_entry;
    assign mesi_rsp_ready = (req_state == REQ_MESI_PROCESS);
    
    // Convert request opcode to MESI event
    always_comb begin
        case (current_req_opcode)
            REQ_READ_SHARED, REQ_READ_CLEAN, REQ_READ_ONCE: begin
                mesi_req_event = 4'h0; // EVENT_CPU_READ
            end
            REQ_WRITE_UNIQUE_FULL, REQ_WRITE_UNIQUE_PTL: begin
                mesi_req_event = 4'h1; // EVENT_CPU_WRITE
            end
            REQ_WRITE_BACK_FULL, REQ_WRITE_CLEAN_FULL: begin
                mesi_req_event = 4'hD; // EVENT_WRITEBACK
            end
            default: begin
                mesi_req_event = 4'h0;
            end
        endcase
    end
    
    // Snoop filter control
    assign sf_snoop_req_valid = mesi_snoop_valid;
    assign sf_snoop_req_addr = mesi_snoop_addr;
    assign sf_snoop_req_opcode = mesi_snoop_opcode;
    assign sf_snoop_req_src = NODE_ID;
    assign mesi_snoop_ready = sf_snoop_req_ready;
    
    // Network interface ready signals
    assign req_in.ready = (req_state == REQ_IDLE);
    
    // Response generation
    assign rsp_out.valid = (req_state == REQ_RESPONSE) && 
                          !mesi_required_actions[6]; // Not sending data
    assign dat_out.valid = (req_state == REQ_RESPONSE) && 
                          mesi_required_actions[6]; // Sending data
    
    // Snoop output
    assign snp_out.valid = sf_filtered_snoop_valid;
    assign snp_out.flit.snp = pack_snp_flit(
        sf_filtered_snoop_opcode,
        sf_filtered_snoop_addr[47:3],
        current_req_txn_id,
        NODE_ID,
        8'h00, // fwd_txn_id
        8'h00  // fwd_node_id
    );
    assign sf_filtered_snoop_ready = snp_out.ready;
    
    // Memory interface (simplified)
    assign mem_if.arvalid = (req_state == REQ_MEM_ACCESS) && mesi_required_actions[3]; // send_mem_read
    assign mem_if.awvalid = (req_state == REQ_MEM_ACCESS) && mesi_required_actions[4]; // send_mem_write
    assign mem_if.araddr = current_req_addr;
    assign mem_if.awaddr = current_req_addr;
    
    // Directory update logic
    assign dir_update_valid = mesi_rsp_valid && mesi_state_changed;
    assign dir_update_addr = current_req_addr;
    assign dir_update_entry = mesi_new_state;
    assign dir_update_allocate = 1'b1;
    
    // Snoop filter tracking
    assign sf_track_valid = mesi_rsp_valid && mesi_state_changed;
    assign sf_track_addr = current_req_addr;
    assign sf_track_node_id = current_req_src;
    
    // Convert MESI state to tracking operation
    always_comb begin
        case (mesi_new_state.state)
            DIR_SHARED: sf_track_op = TRACK_ADD_SHARER;
            DIR_EXCLUSIVE: sf_track_op = TRACK_SET_EXCLUSIVE;
            DIR_MODIFIED: sf_track_op = TRACK_SET_MODIFIED;
            DIR_INVALID: sf_track_op = TRACK_INVALIDATE;
            default: sf_track_op = TRACK_ADD_SHARER;
        endcase
    end
    
    // Writeback handling
    assign slc_wb_ready = 1'b1; // Always ready to accept writebacks
    
    // Unused interface assignments
    assign req_out.valid = 1'b0;
    assign rsp_in.ready = 1'b1;
    assign dat_in.ready = 1'b1;
    assign snp_in.ready = 1'b1;
    
    // Memory interface defaults
    assign mem_if.arid = 8'h00;
    assign mem_if.arlen = 8'h00;
    assign mem_if.arsize = 3'b110; // 64 bytes
    assign mem_if.arburst = 2'b01; // INCR
    assign mem_if.arlock = 1'b0;
    assign mem_if.arcache = 4'b0000;
    assign mem_if.arprot = 3'b000;
    assign mem_if.arqos = 4'b0000;
    
    assign mem_if.awid = 8'h00;
    assign mem_if.awlen = 8'h00;
    assign mem_if.awsize = 3'b110; // 64 bytes
    assign mem_if.awburst = 2'b01; // INCR
    assign mem_if.awlock = 1'b0;
    assign mem_if.awcache = 4'b0000;
    assign mem_if.awprot = 3'b000;
    assign mem_if.awqos = 4'b0000;
    
    assign mem_if.wdata = slc_wb_data;
    assign mem_if.wstrb = '1;
    assign mem_if.wlast = 1'b1;
    assign mem_if.wvalid = slc_wb_valid;
    assign mem_if.bready = 1'b1;
    assign mem_if.rready = 1'b1;

endmodule : hn_f