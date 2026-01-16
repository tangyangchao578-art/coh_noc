// =============================================================================
// CoH NoC Configuration Module
// Requirements: 1.4
// =============================================================================
// This module provides a configuration interface for the coherent NoC system,
// allowing runtime configuration of mesh size, node placement, and system
// parameters.
// =============================================================================

import coh_noc_pkg::*;

module coh_noc_config #(
    parameter int MAX_MESH_SIZE_X = 8,
    parameter int MAX_MESH_SIZE_Y = 8,
    parameter int MAX_NODES = 32
)(
    input logic clk,
    input logic rst_n,
    
    // Configuration Interface (simple register-based)
    input  logic        cfg_write,
    input  logic [15:0] cfg_addr,
    input  logic [31:0] cfg_wdata,
    output logic [31:0] cfg_rdata,
    output logic        cfg_ready,
    
    // Configuration Outputs
    output logic [3:0]  mesh_size_x,
    output logic [3:0]  mesh_size_y,
    output logic [7:0]  num_rn_f,
    output logic [7:0]  num_hn_f,
    output logic [7:0]  num_sn_f,
    output logic [3:0]  sn_f_channels,
    output logic [7:0]  buffer_depth,
    output logic [2:0]  num_vcs,
    output logic [7:0]  max_credits,
    
    // Node Placement Configuration
    output logic [3:0]  node_x_coord[MAX_NODES-1:0],
    output logic [3:0]  node_y_coord[MAX_NODES-1:0],
    output logic [1:0]  node_type[MAX_NODES-1:0],     // 0=None, 1=RN-F, 2=HN-F, 3=SN-F
    output logic [7:0]  node_id[MAX_NODES-1:0],
    
    // Status
    output logic        config_valid,
    output logic        config_locked
);

    // =============================================================================
    // Configuration Register Map
    // =============================================================================
    // 0x0000: System Control
    // 0x0004: Mesh Size (X in [7:0], Y in [15:8])
    // 0x0008: Node Counts (RN-F[7:0], HN-F[15:8], SN-F[23:16])
    // 0x000C: Buffer Configuration (Depth[7:0], VCs[10:8], Credits[23:16])
    // 0x0010: SN-F Configuration (Channels[3:0])
    // 0x0100-0x01FF: Node Placement Table (8 bytes per node)
    //   +0: X[3:0], Y[7:4], Type[9:8], Reserved[15:10]
    //   +4: Node ID[7:0]
    
    // =============================================================================
    // Configuration Registers
    // =============================================================================
    
    logic [31:0] sys_ctrl_reg;
    logic [31:0] mesh_size_reg;
    logic [31:0] node_count_reg;
    logic [31:0] buffer_config_reg;
    logic [31:0] snf_config_reg;
    
    // Node placement table
    logic [31:0] node_placement_reg0[MAX_NODES-1:0];  // X, Y, Type
    logic [31:0] node_placement_reg1[MAX_NODES-1:0];  // Node ID
    
    // Control bits
    logic cfg_lock;
    logic cfg_reset;
    logic cfg_enable;
    
    assign cfg_lock = sys_ctrl_reg[0];
    assign cfg_reset = sys_ctrl_reg[1];
    assign cfg_enable = sys_ctrl_reg[2];
    assign config_locked = cfg_lock;
    assign config_valid = cfg_enable && !cfg_reset;
    
    // =============================================================================
    // Configuration Register Write Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sys_ctrl_reg <= 32'h00000000;
            mesh_size_reg <= 32'h00030003;      // Default 3x3 mesh
            node_count_reg <= 32'h00020204;     // Default 4 RN-F, 2 HN-F, 2 SN-F
            buffer_config_reg <= 32'h00100410;  // Default 16 depth, 4 VCs, 16 credits
            snf_config_reg <= 32'h00000004;     // Default 4 channels
            
            for (int i = 0; i < MAX_NODES; i++) begin
                node_placement_reg0[i] <= 32'h00000000;
                node_placement_reg1[i] <= 32'h00000000;
            end
        end else begin
            if (cfg_write && !cfg_lock) begin
                case (cfg_addr)
                    16'h0000: sys_ctrl_reg <= cfg_wdata;
                    16'h0004: mesh_size_reg <= cfg_wdata;
                    16'h0008: node_count_reg <= cfg_wdata;
                    16'h000C: buffer_config_reg <= cfg_wdata;
                    16'h0010: snf_config_reg <= cfg_wdata;
                    default: begin
                        // Node placement table
                        if (cfg_addr >= 16'h0100 && cfg_addr < 16'h0200) begin
                            logic [7:0] node_idx;
                            logic [2:0] reg_offset;
                            node_idx = (cfg_addr - 16'h0100) >> 3;  // 8 bytes per node
                            reg_offset = cfg_addr[2:0];
                            
                            if (node_idx < MAX_NODES) begin
                                if (reg_offset == 3'h0) begin
                                    node_placement_reg0[node_idx] <= cfg_wdata;
                                end else if (reg_offset == 3'h4) begin
                                    node_placement_reg1[node_idx] <= cfg_wdata;
                                end
                            end
                        end
                    end
                endcase
            end
        end
    end
    
    // =============================================================================
    // Configuration Register Read Logic
    // =============================================================================
    
    always_comb begin
        cfg_rdata = 32'h00000000;
        cfg_ready = 1'b1;
        
        case (cfg_addr)
            16'h0000: cfg_rdata = sys_ctrl_reg;
            16'h0004: cfg_rdata = mesh_size_reg;
            16'h0008: cfg_rdata = node_count_reg;
            16'h000C: cfg_rdata = buffer_config_reg;
            16'h0010: cfg_rdata = snf_config_reg;
            default: begin
                // Node placement table
                if (cfg_addr >= 16'h0100 && cfg_addr < 16'h0200) begin
                    logic [7:0] node_idx;
                    logic [2:0] reg_offset;
                    node_idx = (cfg_addr - 16'h0100) >> 3;
                    reg_offset = cfg_addr[2:0];
                    
                    if (node_idx < MAX_NODES) begin
                        if (reg_offset == 3'h0) begin
                            cfg_rdata = node_placement_reg0[node_idx];
                        end else if (reg_offset == 3'h4) begin
                            cfg_rdata = node_placement_reg1[node_idx];
                        end
                    end
                end
            end
        endcase
    end
    
    // =============================================================================
    // Configuration Output Assignments
    // =============================================================================
    
    assign mesh_size_x = mesh_size_reg[3:0];
    assign mesh_size_y = mesh_size_reg[11:8];
    
    assign num_rn_f = node_count_reg[7:0];
    assign num_hn_f = node_count_reg[15:8];
    assign num_sn_f = node_count_reg[23:16];
    
    assign buffer_depth = buffer_config_reg[7:0];
    assign num_vcs = buffer_config_reg[10:8];
    assign max_credits = buffer_config_reg[23:16];
    
    assign sn_f_channels = snf_config_reg[3:0];
    
    // Node placement outputs
    genvar i;
    generate
        for (i = 0; i < MAX_NODES; i++) begin : gen_node_placement
            assign node_x_coord[i] = node_placement_reg0[i][3:0];
            assign node_y_coord[i] = node_placement_reg0[i][7:4];
            assign node_type[i] = node_placement_reg0[i][9:8];
            assign node_id[i] = node_placement_reg1[i][7:0];
        end
    endgenerate
    
    // =============================================================================
    // Configuration Validation
    // =============================================================================
    
    // Validate configuration parameters
    logic config_error;
    
    always_comb begin
        config_error = 1'b0;
        
        // Check mesh size is within bounds
        if (mesh_size_x == 0 || mesh_size_x > MAX_MESH_SIZE_X ||
            mesh_size_y == 0 || mesh_size_y > MAX_MESH_SIZE_Y) begin
            config_error = 1'b1;
        end
        
        // Check node counts are reasonable
        if (num_rn_f + num_hn_f + num_sn_f > MAX_NODES) begin
            config_error = 1'b1;
        end
        
        // Check buffer parameters
        if (buffer_depth == 0 || num_vcs == 0 || max_credits == 0) begin
            config_error = 1'b1;
        end
        
        // Check SN-F channels
        if (sn_f_channels == 0 || sn_f_channels > 8) begin
            config_error = 1'b1;
        end
    end

endmodule : coh_noc_config
