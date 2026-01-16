// =============================================================================
// CoH NoC System Top-Level Module
// Requirements: 1.1, 1.4
// =============================================================================
// This module integrates the 2D mesh network with HN-F, RN-F, and SN-F nodes
// to create a complete coherent network-on-chip system.
// =============================================================================

import coh_noc_pkg::*;

module coh_noc_system #(
    // Mesh Configuration
    parameter int MESH_SIZE_X = 3,
    parameter int MESH_SIZE_Y = 3,
    parameter int BUFFER_DEPTH = 16,
    parameter int NUM_VCS = 4,
    parameter int MAX_CREDITS = 16,
    
    // Node Configuration
    parameter int NUM_RN_F = 4,        // Number of RN-F (CPU) nodes
    parameter int NUM_HN_F = 2,        // Number of HN-F (Cache) nodes
    parameter int NUM_SN_F = 2,        // Number of SN-F (Memory) nodes
    parameter int SN_F_CHANNELS = 4,   // Memory channels per SN-F
    
    // Cache Configuration
    parameter int SLC_SIZE = 1024*1024,
    parameter int SLC_WAYS = 16,
    parameter int L1_SIZE = 64*1024,
    parameter int L1_WAYS = 4
)(
    input logic clk,
    input logic rst_n,
    
    // CPU Interfaces (for RN-F nodes)
    cpu_if.slave cpu[NUM_RN_F-1:0],
    
    // Memory Interfaces (for SN-F nodes)
    ddr_if.master mem[NUM_SN_F-1:0][SN_F_CHANNELS-1:0],
    
    // System Status
    output logic system_ready,
    output logic [31:0] total_transactions,
    output logic [31:0] active_transactions
);

    // =============================================================================
    // Node Placement Configuration
    // =============================================================================
    // Define where each node type is placed in the mesh
    // This is a simple placement strategy - can be made configurable
    
    // RN-F nodes at positions: (0,0), (1,0), (2,0), (0,1)
    // HN-F nodes at positions: (1,1), (2,1)
    // SN-F nodes at positions: (0,2), (1,2)
    
    typedef struct {
        logic [3:0] x;
        logic [3:0] y;
        logic [1:0] node_type;  // 0=None, 1=RN-F, 2=HN-F, 3=SN-F
        logic [3:0] node_idx;   // Index within node type
    } node_placement_t;
    
    // Node placement table
    node_placement_t node_map[MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    
    initial begin
        // Initialize all positions as empty
        for (int x = 0; x < MESH_SIZE_X; x++) begin
            for (int y = 0; y < MESH_SIZE_Y; y++) begin
                node_map[x][y].x = x;
                node_map[x][y].y = y;
                node_map[x][y].node_type = 2'b00;  // None
                node_map[x][y].node_idx = 4'h0;
            end
        end
        
        // Place RN-F nodes
        if (NUM_RN_F >= 1) begin
            node_map[0][0].node_type = 2'b01;  // RN-F
            node_map[0][0].node_idx = 0;
        end
        if (NUM_RN_F >= 2) begin
            node_map[1][0].node_type = 2'b01;
            node_map[1][0].node_idx = 1;
        end
        if (NUM_RN_F >= 3) begin
            node_map[2][0].node_type = 2'b01;
            node_map[2][0].node_idx = 2;
        end
        if (NUM_RN_F >= 4) begin
            node_map[0][1].node_type = 2'b01;
            node_map[0][1].node_idx = 3;
        end
        
        // Place HN-F nodes
        if (NUM_HN_F >= 1) begin
            node_map[1][1].node_type = 2'b10;  // HN-F
            node_map[1][1].node_idx = 0;
        end
        if (NUM_HN_F >= 2) begin
            node_map[2][1].node_type = 2'b10;
            node_map[2][1].node_idx = 1;
        end
        
        // Place SN-F nodes
        if (NUM_SN_F >= 1) begin
            node_map[0][2].node_type = 2'b11;  // SN-F
            node_map[0][2].node_idx = 0;
        end
        if (NUM_SN_F >= 2) begin
            node_map[1][2].node_type = 2'b11;
            node_map[1][2].node_idx = 1;
        end
    end
    
    // =============================================================================
    // Mesh Network Signals
    // =============================================================================
    
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_in_valid;
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_in_ready;
    flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_in_flit;
    logic [1:0] mesh_local_in_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_in_credit_return;
    
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_out_valid;
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_out_ready;
    flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_local_out_flit;
    logic [1:0] mesh_local_out_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    logic [CREDIT_COUNT_WIDTH-1:0] mesh_local_out_credit_count [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    
    // =============================================================================
    // 2D Mesh Network Instance
    // =============================================================================
    
    mesh_2d_network #(
        .MESH_SIZE_X(MESH_SIZE_X),
        .MESH_SIZE_Y(MESH_SIZE_Y),
        .BUFFER_DEPTH(BUFFER_DEPTH),
        .NUM_VCS(NUM_VCS),
        .MAX_CREDITS(MAX_CREDITS)
    ) u_mesh_network (
        .clk(clk),
        .rst_n(rst_n),
        
        .local_in_valid(mesh_local_in_valid),
        .local_in_ready(mesh_local_in_ready),
        .local_in_flit(mesh_local_in_flit),
        .local_in_vc_id(mesh_local_in_vc_id),
        .local_in_credit_return(mesh_local_in_credit_return),
        
        .local_out_valid(mesh_local_out_valid),
        .local_out_ready(mesh_local_out_ready),
        .local_out_flit(mesh_local_out_flit),
        .local_out_vc_id(mesh_local_out_vc_id),
        .local_out_credit_count(mesh_local_out_credit_count)
    );
    
    // =============================================================================
    // Node Interface Signals
    // =============================================================================
    
    // RN-F node signals
    logic [NUM_RN_F-1:0] rnf_req_out_valid;
    logic [NUM_RN_F-1:0] rnf_req_out_ready;
    flit_u [NUM_RN_F-1:0] rnf_req_out_flit;
    logic [1:0] rnf_req_out_vc_id [NUM_RN_F-1:0];
    
    logic [NUM_RN_F-1:0] rnf_rsp_in_valid;
    logic [NUM_RN_F-1:0] rnf_rsp_in_ready;
    flit_u [NUM_RN_F-1:0] rnf_rsp_in_flit;
    
    logic [NUM_RN_F-1:0] rnf_dat_in_valid;
    logic [NUM_RN_F-1:0] rnf_dat_in_ready;
    flit_u [NUM_RN_F-1:0] rnf_dat_in_flit;
    
    logic [NUM_RN_F-1:0] rnf_snp_in_valid;
    logic [NUM_RN_F-1:0] rnf_snp_in_ready;
    flit_u [NUM_RN_F-1:0] rnf_snp_in_flit;
    
    logic [NUM_RN_F-1:0] rnf_snp_rsp_out_valid;
    logic [NUM_RN_F-1:0] rnf_snp_rsp_out_ready;
    flit_u [NUM_RN_F-1:0] rnf_snp_rsp_out_flit;
    
    // HN-F node signals (simplified - using xp_port_if would be better)
    xp_port_if hnf_req_in[NUM_HN_F-1:0]();
    xp_port_if hnf_req_out[NUM_HN_F-1:0]();
    xp_port_if hnf_rsp_in[NUM_HN_F-1:0]();
    xp_port_if hnf_rsp_out[NUM_HN_F-1:0]();
    xp_port_if hnf_dat_in[NUM_HN_F-1:0]();
    xp_port_if hnf_dat_out[NUM_HN_F-1:0]();
    xp_port_if hnf_snp_out[NUM_HN_F-1:0]();
    xp_port_if hnf_snp_in[NUM_HN_F-1:0]();
    axi_if hnf_mem_if[NUM_HN_F-1:0]();
    
    // SN-F node signals
    xp_port_if snf_req_in[NUM_SN_F-1:0]();
    xp_port_if snf_rsp_out[NUM_SN_F-1:0]();
    xp_port_if snf_dat_out[NUM_SN_F-1:0]();
    
    // =============================================================================
    // RN-F Node Instances
    // =============================================================================
    
    genvar rn;
    generate
        for (rn = 0; rn < NUM_RN_F; rn++) begin : gen_rn_f_nodes
            rn_f #(
                .CACHE_SIZE(L1_SIZE),
                .NUM_WAYS(L1_WAYS),
                .NODE_ID(8'h00 + rn)
            ) u_rn_f (
                .clk(clk),
                .rst_n(rst_n),
                
                // CPU Interface
                .cpu_req_valid(cpu[rn].req_valid),
                .cpu_req_ready(cpu[rn].req_ready),
                .cpu_req_read(cpu[rn].req_read),
                .cpu_req_addr(cpu[rn].req_addr),
                .cpu_req_size(cpu[rn].req_size),
                .cpu_req_data(cpu[rn].req_data),
                .cpu_req_qos(cpu[rn].req_qos),
                .cpu_rsp_valid(cpu[rn].rsp_valid),
                .cpu_rsp_ready(cpu[rn].rsp_ready),
                .cpu_rsp_data(cpu[rn].rsp_data),
                .cpu_rsp_error(cpu[rn].rsp_error),
                .cpu_rsp_txn_id(cpu[rn].rsp_txn_id),
                
                // Network Interface
                .req_out_valid(rnf_req_out_valid[rn]),
                .req_out_ready(rnf_req_out_ready[rn]),
                .req_out_flit(rnf_req_out_flit[rn]),
                .req_out_vc_id(rnf_req_out_vc_id[rn]),
                .req_out_channel_type(),
                .req_out_credit_return(),
                
                .rsp_in_valid(rnf_rsp_in_valid[rn]),
                .rsp_in_ready(rnf_rsp_in_ready[rn]),
                .rsp_in_flit(rnf_rsp_in_flit[rn]),
                
                .dat_in_valid(rnf_dat_in_valid[rn]),
                .dat_in_ready(rnf_dat_in_ready[rn]),
                .dat_in_flit(rnf_dat_in_flit[rn]),
                
                .snp_in_valid(rnf_snp_in_valid[rn]),
                .snp_in_ready(rnf_snp_in_ready[rn]),
                .snp_in_flit(rnf_snp_in_flit[rn]),
                
                .snp_rsp_out_valid(rnf_snp_rsp_out_valid[rn]),
                .snp_rsp_out_ready(rnf_snp_rsp_out_ready[rn]),
                .snp_rsp_out_flit(rnf_snp_rsp_out_flit[rn]),
                .snp_rsp_out_vc_id(),
                .snp_rsp_out_channel_type(),
                .snp_rsp_out_credit_return()
            );
        end
    endgenerate
    
    // =============================================================================
    // HN-F Node Instances
    // =============================================================================
    
    genvar hn;
    generate
        for (hn = 0; hn < NUM_HN_F; hn++) begin : gen_hn_f_nodes
            hn_f #(
                .CACHE_SIZE(SLC_SIZE),
                .NUM_WAYS(SLC_WAYS),
                .NODE_ID(8'h10 + hn)
            ) u_hn_f (
                .clk(clk),
                .rst_n(rst_n),
                
                // Network Interface
                .req_in(hnf_req_in[hn]),
                .req_out(hnf_req_out[hn]),
                .rsp_in(hnf_rsp_in[hn]),
                .rsp_out(hnf_rsp_out[hn]),
                .dat_in(hnf_dat_in[hn]),
                .dat_out(hnf_dat_out[hn]),
                .snp_out(hnf_snp_out[hn]),
                .snp_in(hnf_snp_in[hn]),
                
                // Memory Interface
                .mem_if(hnf_mem_if[hn]),
                
                // Configuration
                .filter_enable(1'b1),
                .broadcast_mode(1'b0),
                .filter_threshold(4'h4),
                .total_snoops(),
                .filtered_snoops(),
                .broadcast_snoops(),
                .protocol_error(),
                .error_code()
            );
        end
    endgenerate
    
    // =============================================================================
    // SN-F Node Instances
    // =============================================================================
    
    genvar sn;
    generate
        for (sn = 0; sn < NUM_SN_F; sn++) begin : gen_sn_f_nodes
            sn_f #(
                .NUM_CHANNELS(SN_F_CHANNELS),
                .NODE_ID(8'h20 + sn)
            ) u_sn_f (
                .clk(clk),
                .rst_n(rst_n),
                
                // Network Interface
                .req_in(snf_req_in[sn]),
                .rsp_out(snf_rsp_out[sn]),
                .dat_out(snf_dat_out[sn]),
                
                // Memory Interface
                .ddr_ctrl(mem[sn])
            );
        end
    endgenerate
    
    // =============================================================================
    // Node-to-Mesh Connection Logic
    // =============================================================================
    
    // Connect nodes to mesh based on placement
    always_comb begin
        // Default: tie off all mesh local ports
        for (int x = 0; x < MESH_SIZE_X; x++) begin
            for (int y = 0; y < MESH_SIZE_Y; y++) begin
                mesh_local_in_valid[x][y] = 1'b0;
                mesh_local_in_flit[x][y] = '0;
                mesh_local_in_vc_id[x][y] = 2'b00;
                mesh_local_in_credit_return[x][y] = 1'b0;
                mesh_local_out_ready[x][y] = 1'b0;
            end
        end
        
        // Connect RN-F nodes
        for (int i = 0; i < NUM_RN_F; i++) begin
            for (int x = 0; x < MESH_SIZE_X; x++) begin
                for (int y = 0; y < MESH_SIZE_Y; y++) begin
                    if (node_map[x][y].node_type == 2'b01 && node_map[x][y].node_idx == i) begin
                        // Connect RN-F to mesh
                        mesh_local_in_valid[x][y] = rnf_req_out_valid[i];
                        mesh_local_in_flit[x][y] = rnf_req_out_flit[i];
                        mesh_local_in_vc_id[x][y] = rnf_req_out_vc_id[i];
                        rnf_req_out_ready[i] = mesh_local_in_ready[x][y];
                        
                        // Demux mesh output to appropriate RN-F channel
                        rnf_rsp_in_valid[i] = mesh_local_out_valid[x][y] && 
                                              (mesh_local_out_vc_id[x][y] == VC_RSP);
                        rnf_dat_in_valid[i] = mesh_local_out_valid[x][y] && 
                                              (mesh_local_out_vc_id[x][y] == VC_DAT);
                        rnf_snp_in_valid[i] = mesh_local_out_valid[x][y] && 
                                              (mesh_local_out_vc_id[x][y] == VC_SNP);
                        
                        rnf_rsp_in_flit[i] = mesh_local_out_flit[x][y];
                        rnf_dat_in_flit[i] = mesh_local_out_flit[x][y];
                        rnf_snp_in_flit[i] = mesh_local_out_flit[x][y];
                        
                        mesh_local_out_ready[x][y] = (mesh_local_out_vc_id[x][y] == VC_RSP) ? rnf_rsp_in_ready[i] :
                                                     (mesh_local_out_vc_id[x][y] == VC_DAT) ? rnf_dat_in_ready[i] :
                                                     (mesh_local_out_vc_id[x][y] == VC_SNP) ? rnf_snp_in_ready[i] : 1'b0;
                    end
                end
            end
        end
        
        // Connect HN-F nodes (simplified - would need proper channel muxing)
        for (int i = 0; i < NUM_HN_F; i++) begin
            for (int x = 0; x < MESH_SIZE_X; x++) begin
                for (int y = 0; y < MESH_SIZE_Y; y++) begin
                    if (node_map[x][y].node_type == 2'b10 && node_map[x][y].node_idx == i) begin
                        // Connect HN-F REQ input from mesh
                        hnf_req_in[i].valid = mesh_local_out_valid[x][y] && 
                                              (mesh_local_out_vc_id[x][y] == VC_REQ);
                        hnf_req_in[i].flit = mesh_local_out_flit[x][y];
                        hnf_req_in[i].vc_id = mesh_local_out_vc_id[x][y];
                        
                        // For now, tie off other HN-F inputs
                        hnf_rsp_in[i].valid = 1'b0;
                        hnf_dat_in[i].valid = 1'b0;
                        hnf_snp_in[i].valid = 1'b0;
                    end
                end
            end
        end
        
        // Connect SN-F nodes
        for (int i = 0; i < NUM_SN_F; i++) begin
            for (int x = 0; x < MESH_SIZE_X; x++) begin
                for (int y = 0; y < MESH_SIZE_Y; y++) begin
                    if (node_map[x][y].node_type == 2'b11 && node_map[x][y].node_idx == i) begin
                        // Connect SN-F REQ input from mesh
                        snf_req_in[i].valid = mesh_local_out_valid[x][y] && 
                                              (mesh_local_out_vc_id[x][y] == VC_REQ);
                        snf_req_in[i].flit = mesh_local_out_flit[x][y];
                        snf_req_in[i].vc_id = mesh_local_out_vc_id[x][y];
                        
                        mesh_local_out_ready[x][y] = snf_req_in[i].ready;
                        
                        // Connect SN-F outputs to mesh (RSP and DAT)
                        // This is simplified - would need proper arbitration
                        mesh_local_in_valid[x][y] = snf_rsp_out[i].valid || snf_dat_out[i].valid;
                        mesh_local_in_flit[x][y] = snf_rsp_out[i].valid ? snf_rsp_out[i].flit : snf_dat_out[i].flit;
                        mesh_local_in_vc_id[x][y] = snf_rsp_out[i].valid ? VC_RSP : VC_DAT;
                    end
                end
            end
        end
    end
    
    // =============================================================================
    // System Status
    // =============================================================================
    
    assign system_ready = rst_n;
    assign total_transactions = 32'h0;  // TODO: Implement transaction counting
    assign active_transactions = 32'h0;

endmodule : coh_noc_system
