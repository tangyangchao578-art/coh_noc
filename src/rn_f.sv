// =============================================================================
// RN-F (Request Node Fully-coherent) - CPU Request Proxy
// Requirements: 5.1, 5.2, 5.3, 5.4, 5.5
// =============================================================================

import coh_noc_pkg::*;

module rn_f #(
    parameter CACHE_SIZE = 64*1024,   // 64KB L1 Cache
    parameter NUM_WAYS = 4,
    parameter NODE_ID = 8'h00
)(
    input  logic clk,
    input  logic rst_n,
    
    // CPU Interface
    input  logic        cpu_req_valid,
    output logic        cpu_req_ready,
    input  logic        cpu_req_read,
    input  logic [47:0] cpu_req_addr,
    input  logic [3:0]  cpu_req_size,
    input  logic [511:0] cpu_req_data,
    input  logic [7:0]  cpu_req_qos,
    output logic        cpu_rsp_valid,
    input  logic        cpu_rsp_ready,
    output logic [511:0] cpu_rsp_data,
    output logic        cpu_rsp_error,
    output logic [11:0] cpu_rsp_txn_id,
    
    // Network Interface - REQ Channel
    output logic        req_out_valid,
    input  logic        req_out_ready,
    output flit_u       req_out_flit,
    output logic [1:0]  req_out_vc_id,
    output logic [1:0]  req_out_channel_type,
    output logic        req_out_credit_return,
    
    // Network Interface - RSP Channel
    input  logic        rsp_in_valid,
    output logic        rsp_in_ready,
    input  flit_u       rsp_in_flit,
    
    // Network Interface - DAT Channel
    input  logic        dat_in_valid,
    output logic        dat_in_ready,
    input  flit_u       dat_in_flit,
    
    // Network Interface - SNP Channel
    input  logic        snp_in_valid,
    output logic        snp_in_ready,
    input  flit_u       snp_in_flit,
    output logic        snp_rsp_out_valid,
    input  logic        snp_rsp_out_ready,
    output flit_u       snp_rsp_out_flit,
    output logic [1:0]  snp_rsp_out_vc_id,
    output logic [1:0]  snp_rsp_out_channel_type,
    output logic        snp_rsp_out_credit_return
);

    // =============================================================================
    // Internal Signals
    // =============================================================================
    
    // Transaction ID counter
    logic [11:0] txn_id_counter;
    
    // L1 Cache Interface
    logic        cache_access_valid;
    logic        cache_access_ready;
    logic        cache_access_read;
    logic [47:0] cache_access_addr;
    logic [511:0] cache_access_wdata;
    logic [63:0] cache_access_be;
    logic        cache_access_hit;
    logic [511:0] cache_access_rdata;
    logic [3:0]  cache_access_state;
    
    logic        cache_fill_valid;
    logic        cache_fill_ready;
    logic [47:0] cache_fill_addr;
    logic [511:0] cache_fill_data;
    logic [3:0]  cache_fill_state;
    
    logic        cache_evict_valid;
    logic        cache_evict_ready;
    logic [47:0] cache_evict_addr;
    logic [511:0] cache_evict_data;
    logic        cache_evict_dirty;
    
    logic        cache_snoop_valid;
    logic        cache_snoop_ready;
    logic [47:0] cache_snoop_addr;
    snp_opcode_e cache_snoop_opcode;
    logic        cache_snoop_hit;
    logic [3:0]  cache_snoop_state;
    logic [511:0] cache_snoop_data;
    
    // =============================================================================
    // L1 Cache Instance
    // =============================================================================
    
    l1_cache #(
        .CACHE_SIZE(CACHE_SIZE),
        .NUM_WAYS(NUM_WAYS),
        .LINE_SIZE(64)
    ) u_l1_cache (
        .clk(clk),
        .rst_n(rst_n),
        
        .access_valid(cache_access_valid),
        .access_ready(cache_access_ready),
        .access_read(cache_access_read),
        .access_addr(cache_access_addr),
        .access_wdata(cache_access_wdata),
        .access_be(cache_access_be),
        .access_hit(cache_access_hit),
        .access_rdata(cache_access_rdata),
        .access_state(cache_access_state),
        
        .fill_valid(cache_fill_valid),
        .fill_ready(cache_fill_ready),
        .fill_addr(cache_fill_addr),
        .fill_data(cache_fill_data),
        .fill_state(cache_fill_state),
        
        .evict_valid(cache_evict_valid),
        .evict_ready(cache_evict_ready),
        .evict_addr(cache_evict_addr),
        .evict_data(cache_evict_data),
        .evict_dirty(cache_evict_dirty),
        
        .snoop_valid(cache_snoop_valid),
        .snoop_ready(cache_snoop_ready),
        .snoop_addr(cache_snoop_addr),
        .snoop_opcode(cache_snoop_opcode),
        .snoop_hit(cache_snoop_hit),
        .snoop_state(cache_snoop_state),
        .snoop_data(cache_snoop_data)
    );
    
    // =============================================================================
    // CPU Request Processing State Machine
    // =============================================================================
    
    typedef enum logic [2:0] {
        CPU_IDLE,
        CPU_CACHE_ACCESS,
        CPU_SEND_REQ,
        CPU_WAIT_RSP,
        CPU_WAIT_DAT,
        CPU_SEND_EVICT,
        CPU_RESPOND
    } cpu_state_e;
    
    cpu_state_e cpu_state, cpu_state_next;
    
    // Transaction tracking
    logic [11:0] pending_txn_id;
    logic [47:0] pending_addr;
    logic        pending_read;
    logic [511:0] pending_wdata;
    logic [63:0] pending_be;
    logic [3:0]  pending_size;
    logic [7:0]  pending_qos;
    logic        pending_write_back;
    
    // =============================================================================
    // CPU Request FSM
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cpu_state <= CPU_IDLE;
            txn_id_counter <= '0;
        end else begin
            cpu_state <= cpu_state_next;
            if (cpu_state == CPU_SEND_REQ && req_out_valid && req_out_ready) begin
                txn_id_counter <= txn_id_counter + 1;
            end
        end
    end
    
    always_comb begin
        cpu_state_next = cpu_state;
        
        case (cpu_state)
            CPU_IDLE: begin
                if (cpu_req_valid) begin
                    cpu_state_next = CPU_CACHE_ACCESS;
                end
            end
            
            CPU_CACHE_ACCESS: begin
                if (cache_access_ready) begin
                    if (cache_access_hit) begin
                        // Cache hit - respond immediately
                        cpu_state_next = CPU_RESPOND;
                    end else begin
                        // Cache miss - need to send request to network
                        if (cache_evict_valid) begin
                            cpu_state_next = CPU_SEND_EVICT;
                        end else begin
                            cpu_state_next = CPU_SEND_REQ;
                        end
                    end
                end
            end
            
            CPU_SEND_EVICT: begin
                if (req_out_ready) begin
                    cpu_state_next = CPU_SEND_REQ;
                end
            end
            
            CPU_SEND_REQ: begin
                if (req_out_ready) begin
                    cpu_state_next = CPU_WAIT_RSP;
                end
            end
            
            CPU_WAIT_RSP: begin
                if (rsp_in_valid && rsp_in_flit.rsp.txn_id == pending_txn_id) begin
                    if (rsp_in_flit.rsp.opcode == RSP_COMP_DATA) begin
                        cpu_state_next = CPU_WAIT_DAT;
                    end else begin
                        cpu_state_next = CPU_RESPOND;
                    end
                end
            end
            
            CPU_WAIT_DAT: begin
                if (dat_in_valid && dat_in_flit.dat.txn_id == pending_txn_id) begin
                    cpu_state_next = CPU_RESPOND;
                end
            end
            
            CPU_RESPOND: begin
                if (cpu_rsp_ready) begin
                    cpu_state_next = CPU_IDLE;
                end
            end
        endcase
    end
    
    // =============================================================================
    // CPU Request Handling
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pending_txn_id <= '0;
            pending_addr <= '0;
            pending_read <= '0;
            pending_wdata <= '0;
            pending_be <= '0;
            pending_size <= '0;
            pending_qos <= '0;
            pending_write_back <= '0;
        end else begin
            if (cpu_state == CPU_IDLE && cpu_req_valid) begin
                pending_txn_id <= txn_id_counter;
                pending_addr <= cpu_req_addr;
                pending_read <= cpu_req_read;
                pending_wdata <= cpu_req_data;
                pending_be <= 64'hFFFFFFFFFFFFFFFF;  // Full line
                pending_size <= cpu_req_size[2:0];
                pending_qos <= cpu_req_qos[3:0];
                pending_write_back <= 1'b0;
            end
        end
    end
    
    // CPU interface signals
    assign cpu_req_ready = (cpu_state == CPU_IDLE);
    assign cpu_rsp_valid = (cpu_state == CPU_RESPOND);
    assign cpu_rsp_data = cache_access_hit ? cache_access_rdata : 
                              (dat_in_valid ? dat_in_flit.dat.data : '0);
    assign cpu_rsp_error = 1'b0;
    assign cpu_rsp_txn_id = pending_txn_id;
    
    // Cache access signals
    assign cache_access_valid = (cpu_state == CPU_CACHE_ACCESS);
    assign cache_access_read = pending_read;
    assign cache_access_addr = pending_addr;
    assign cache_access_wdata = pending_wdata;
    assign cache_access_be = pending_be;
    
    // Cache fill signals
    assign cache_fill_valid = (cpu_state == CPU_WAIT_DAT && dat_in_valid && 
                               dat_in_flit.dat.txn_id == pending_txn_id);
    assign cache_fill_addr = pending_addr;
    assign cache_fill_data = dat_in_flit.dat.data;
    assign cache_fill_state = pending_read ? 4'h1 : 4'h3;  // SHARED for read, MODIFIED for write
    
    // Cache eviction handling
    assign cache_evict_ready = (cpu_state == CPU_SEND_EVICT && req_out_ready);
    
    // =============================================================================
    // Network Request Generation (Requirements 5.1, 5.4)
    // =============================================================================
    
    req_flit_t req_out_flit_req;
    
    always_comb begin
        req_out_valid = 1'b0;
        req_out_flit_req = '0;
        req_out_vc_id = VC_REQ;
        req_out_channel_type = 2'b00;  // REQ channel
        req_out_credit_return = 1'b0;
        
        if (cpu_state == CPU_SEND_EVICT && cache_evict_valid) begin
            // Send write-back request for evicted dirty line
            req_out_valid = 1'b1;
            req_out_flit_req = pack_req_flit(
                .opcode(REQ_WRITE_BACK_FULL),
                .addr(cache_evict_addr),
                .txn_id(txn_id_counter),
                .src_id(NODE_ID),
                .tgt_id(8'h00),  // Home node
                .size(3'b110),   // 64 bytes
                .mem_attr(3'b000),
                .qos(4'h0),
                .ns(1'b0),
                .likely_shared(1'b0),
                .allow_retry(1'b0),
                .order(1'b0)
            );
        end else if (cpu_state == CPU_SEND_REQ) begin
            req_out_valid = 1'b1;
            
            if (pending_read) begin
                // Read request
                req_out_flit_req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(pending_addr),
                    .txn_id(pending_txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(8'h00),  // Home node
                    .size(pending_size),
                    .mem_attr(3'b000),
                    .qos(pending_qos),
                    .ns(1'b0),
                    .likely_shared(1'b1),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
            end else begin
                // Write request
                req_out_flit_req = pack_req_flit(
                    .opcode(REQ_WRITE_UNIQUE_FULL),
                    .addr(pending_addr),
                    .txn_id(pending_txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(8'h00),  // Home node
                    .size(pending_size),
                    .mem_attr(3'b000),
                    .qos(pending_qos),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
            end
        end
    end
    
    assign req_out_flit.req = req_out_flit_req;
    
    // =============================================================================
    // Snoop Request Handling (Requirement 5.3)
    // =============================================================================
    
    typedef enum logic [1:0] {
        SNP_IDLE,
        SNP_CACHE_LOOKUP,
        SNP_SEND_RSP,
        SNP_SEND_DAT
    } snoop_state_e;
    
    snoop_state_e snoop_state, snoop_state_next;
    
    logic [11:0] snoop_txn_id;
    logic [7:0]  snoop_src_id;
    logic [47:0] snoop_addr_reg;
    snp_opcode_e snoop_opcode_reg;
    logic        snoop_has_data;
    logic [3:0]  snoop_resp_state;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            snoop_state <= SNP_IDLE;
        end else begin
            snoop_state <= snoop_state_next;
        end
    end
    
    always_comb begin
        snoop_state_next = snoop_state;
        
        case (snoop_state)
            SNP_IDLE: begin
                if (snp_in_valid) begin
                    snoop_state_next = SNP_CACHE_LOOKUP;
                end
            end
            
            SNP_CACHE_LOOKUP: begin
                if (cache_snoop_ready) begin
                    if (cache_snoop_hit && (cache_snoop_state == 4'h3)) begin
                        // Modified data - need to send data
                        snoop_state_next = SNP_SEND_DAT;
                    end else begin
                        // Send response only
                        snoop_state_next = SNP_SEND_RSP;
                    end
                end
            end
            
            SNP_SEND_RSP: begin
                if (snp_rsp_out_ready) begin
                    snoop_state_next = SNP_IDLE;
                end
            end
            
            SNP_SEND_DAT: begin
                if (snp_rsp_out_ready) begin
                    snoop_state_next = SNP_IDLE;
                end
            end
        endcase
    end
    
    // Snoop transaction tracking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            snoop_txn_id <= '0;
            snoop_src_id <= '0;
            snoop_addr_reg <= '0;
            snoop_opcode_reg <= SNP_SHARED;
            snoop_has_data <= '0;
            snoop_resp_state <= '0;
        end else begin
            if (snoop_state == SNP_IDLE && snp_in_valid) begin
                snoop_txn_id <= snp_in_flit.snp.txn_id;
                snoop_src_id <= snp_in_flit.snp.src_id;
                snoop_addr_reg <= {snp_in_flit.snp.addr, 3'b000};
                snoop_opcode_reg <= snp_opcode_e'(snp_in_flit.snp.opcode);
            end
            
            if (snoop_state == SNP_CACHE_LOOKUP && cache_snoop_ready) begin
                snoop_has_data <= cache_snoop_hit && (cache_snoop_state == 4'h3);
                snoop_resp_state <= cache_snoop_state;
            end
        end
    end
    
    // Snoop interface signals
    assign snp_in_ready = (snoop_state == SNP_IDLE);
    
    assign cache_snoop_valid = (snoop_state == SNP_CACHE_LOOKUP);
    assign cache_snoop_addr = snoop_addr_reg;
    assign cache_snoop_opcode = snoop_opcode_reg;
    
    // Snoop response generation
    rsp_flit_t snp_rsp_out_flit_rsp;
    dat_flit_t snp_rsp_out_flit_dat;
    
    always_comb begin
        snp_rsp_out_valid = 1'b0;
        snp_rsp_out_flit_rsp = '0;
        snp_rsp_out_flit_dat = '0;
        snp_rsp_out_vc_id = VC_DAT;
        snp_rsp_out_channel_type = 2'b10;  // DAT channel
        snp_rsp_out_credit_return = 1'b0;
        
        if (snoop_state == SNP_SEND_RSP || snoop_state == SNP_SEND_DAT) begin
            snp_rsp_out_valid = 1'b1;
            
            if (snoop_has_data) begin
                // Send data response
                snp_rsp_out_flit_dat = pack_dat_flit(
                    .opcode(DAT_COPY_BACK_WR_DATA),
                    .txn_id(snoop_txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(snoop_src_id),
                    .home_node_id(8'h00),
                    .dbid(8'h00),
                    .data(cache_snoop_data),
                    .be(64'hFFFFFFFFFFFFFFFF),
                    .data_id(3'b000),
                    .resp(snoop_resp_state[1:0])
                );
            end else begin
                // Send response without data
                snp_rsp_out_vc_id = VC_RSP;
                snp_rsp_out_channel_type = 2'b01;  // RSP channel
                snp_rsp_out_flit_rsp = pack_rsp_flit(
                    .opcode(RSP_COMP),
                    .txn_id(snoop_txn_id),
                    .src_id(NODE_ID),
                    .tgt_id(snoop_src_id),
                    .dbid(8'h00),
                    .resp(snoop_resp_state[1:0]),
                    .fwd_state(2'b00)
                );
            end
        end
    end
    
    assign snp_rsp_out_flit.rsp = snp_rsp_out_flit_rsp;
    assign snp_rsp_out_flit.dat = snp_rsp_out_flit_dat;
    
    // RSP and DAT input ready signals
    assign rsp_in_ready = 1'b1;
    assign dat_in_ready = 1'b1;

endmodule : rn_f
