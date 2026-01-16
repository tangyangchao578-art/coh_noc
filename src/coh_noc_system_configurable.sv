// =============================================================================
// CoH NoC Configurable System Top-Level Module
// Requirements: 1.1, 1.4
// =============================================================================
// This is an enhanced version of the system that supports runtime configuration
// of mesh size, node placement, and system parameters.
// =============================================================================

import coh_noc_pkg::*;

module coh_noc_system_configurable #(
    parameter int MAX_MESH_SIZE_X = 8,
    parameter int MAX_MESH_SIZE_Y = 8,
    parameter int MAX_NODES = 32,
    parameter int MAX_RN_F = 16,
    parameter int MAX_HN_F = 8,
    parameter int MAX_SN_F = 8,
    parameter int SN_F_CHANNELS = 4
)(
    input logic clk,
    input logic rst_n,
    
    // Configuration Interface
    input  logic        cfg_write,
    input  logic [15:0] cfg_addr,
    input  logic [31:0] cfg_wdata,
    output logic [31:0] cfg_rdata,
    output logic        cfg_ready,
    
    // CPU Interfaces (for RN-F nodes)
    cpu_if.slave cpu[MAX_RN_F-1:0],
    
    // Memory Interfaces (for SN-F nodes)
    ddr_if.master mem[MAX_SN_F-1:0][SN_F_CHANNELS-1:0],
    
    // System Status
    output logic system_ready,
    output logic config_valid,
    output logic config_locked,
    output logic [31:0] total_transactions,
    output logic [31:0] active_transactions
);

    // =============================================================================
    // Configuration Signals
    // =============================================================================
    
    logic [3:0]  cfg_mesh_size_x;
    logic [3:0]  cfg_mesh_size_y;
    logic [7:0]  cfg_num_rn_f;
    logic [7:0]  cfg_num_hn_f;
    logic [7:0]  cfg_num_sn_f;
    logic [3:0]  cfg_sn_f_channels;
    logic [7:0]  cfg_buffer_depth;
    logic [2:0]  cfg_num_vcs;
    logic [7:0]  cfg_max_credits;
    
    logic [3:0]  cfg_node_x_coord[MAX_NODES-1:0];
    logic [3:0]  cfg_node_y_coord[MAX_NODES-1:0];
    logic [1:0]  cfg_node_type[MAX_NODES-1:0];
    logic [7:0]  cfg_node_id[MAX_NODES-1:0];
    
    // =============================================================================
    // Configuration Module Instance
    // =============================================================================
    
    coh_noc_config #(
        .MAX_MESH_SIZE_X(MAX_MESH_SIZE_X),
        .MAX_MESH_SIZE_Y(MAX_MESH_SIZE_Y),
        .MAX_NODES(MAX_NODES)
    ) u_config (
        .clk(clk),
        .rst_n(rst_n),
        
        .cfg_write(cfg_write),
        .cfg_addr(cfg_addr),
        .cfg_wdata(cfg_wdata),
        .cfg_rdata(cfg_rdata),
        .cfg_ready(cfg_ready),
        
        .mesh_size_x(cfg_mesh_size_x),
        .mesh_size_y(cfg_mesh_size_y),
        .num_rn_f(cfg_num_rn_f),
        .num_hn_f(cfg_num_hn_f),
        .num_sn_f(cfg_num_sn_f),
        .sn_f_channels(cfg_sn_f_channels),
        .buffer_depth(cfg_buffer_depth),
        .num_vcs(cfg_num_vcs),
        .max_credits(cfg_max_credits),
        
        .node_x_coord(cfg_node_x_coord),
        .node_y_coord(cfg_node_y_coord),
        .node_type(cfg_node_type),
        .node_id(cfg_node_id),
        
        .config_valid(config_valid),
        .config_locked(config_locked)
    );
    
    // =============================================================================
    // System Status
    // =============================================================================
    
    assign system_ready = rst_n && config_valid;
    
    // Transaction counters (simplified)
    logic [31:0] txn_counter;
    logic [31:0] active_txn_counter;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_counter <= 32'h0;
            active_txn_counter <= 32'h0;
        end else begin
            // Count CPU requests as new transactions
            for (int i = 0; i < MAX_RN_F; i++) begin
                if (cpu[i].req_valid && cpu[i].req_ready) begin
                    txn_counter <= txn_counter + 1;
                    active_txn_counter <= active_txn_counter + 1;
                end
                if (cpu[i].rsp_valid && cpu[i].rsp_ready) begin
                    if (active_txn_counter > 0) begin
                        active_txn_counter <= active_txn_counter - 1;
                    end
                end
            end
        end
    end
    
    assign total_transactions = txn_counter;
    assign active_transactions = active_txn_counter;
    
    // =============================================================================
    // Note: Actual System Instantiation
    // =============================================================================
    // In a complete implementation, we would instantiate the mesh network and
    // nodes here based on the configuration parameters. This would require:
    // 1. Dynamic mesh generation based on cfg_mesh_size_x/y
    // 2. Dynamic node instantiation based on cfg_num_*
    // 3. Dynamic connection routing based on cfg_node_*_coord
    //
    // For now, this module provides the configuration infrastructure.
    // The static coh_noc_system module should be used for fixed configurations.
    // =============================================================================

endmodule : coh_noc_system_configurable
