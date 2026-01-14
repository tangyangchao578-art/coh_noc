// =============================================================================
// Virtual Channel Buffer Manager - Manages Multiple VC Buffers
// Requirements: 3.5, 8.3
// =============================================================================

import coh_noc_pkg::*;

module vc_buffer_manager #(
    parameter int BUFFER_DEPTH = 16,
    parameter int NUM_VCS = 4  // REQ, RSP, DAT, SNP
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Write interface
    input  logic        wr_en,
    input  logic [1:0]  wr_vc_id,
    input  flit_u       wr_data,
    output logic [3:0]  vc_full,
    output logic [3:0]  vc_almost_full,
    
    // Read interface
    input  logic        rd_en,
    input  logic [1:0]  rd_vc_id,
    output flit_u       rd_data,
    output logic [3:0]  vc_empty,
    output logic [3:0]  vc_almost_empty,
    
    // Status signals per VC
    output logic [7:0]  vc_count [0:NUM_VCS-1],
    output logic [7:0]  vc_free_slots [0:NUM_VCS-1]
);

    // =============================================================================
    // Per-VC Signals
    // =============================================================================
    
    logic [NUM_VCS-1:0] vc_wr_en;
    logic [NUM_VCS-1:0] vc_rd_en;
    flit_u vc_rd_data [0:NUM_VCS-1];
    
    // =============================================================================
    // Write Demultiplexer
    // =============================================================================
    
    always_comb begin
        vc_wr_en = '0;
        if (wr_en) begin
            vc_wr_en[wr_vc_id] = 1'b1;
        end
    end
    
    // =============================================================================
    // Read Demultiplexer
    // =============================================================================
    
    always_comb begin
        vc_rd_en = '0;
        if (rd_en) begin
            vc_rd_en[rd_vc_id] = 1'b1;
        end
    end
    
    // =============================================================================
    // Read Data Multiplexer
    // =============================================================================
    
    always_comb begin
        rd_data = vc_rd_data[rd_vc_id];
    end
    
    // =============================================================================
    // Instantiate VC Buffers
    // =============================================================================
    
    genvar i;
    generate
        for (i = 0; i < NUM_VCS; i++) begin : gen_vc_buffers
            vc_buffer #(
                .BUFFER_DEPTH(BUFFER_DEPTH),
                .VC_ID(i)
            ) vc_buf_inst (
                .clk(clk),
                .rst_n(rst_n),
                
                // Write interface
                .wr_en(vc_wr_en[i]),
                .wr_data(wr_data),
                .full(vc_full[i]),
                .almost_full(vc_almost_full[i]),
                
                // Read interface
                .rd_en(vc_rd_en[i]),
                .rd_data(vc_rd_data[i]),
                .empty(vc_empty[i]),
                .almost_empty(vc_almost_empty[i]),
                
                // Status signals
                .count(vc_count[i]),
                .free_slots(vc_free_slots[i])
            );
        end
    endgenerate
    
    // =============================================================================
    // Assertions for Verification (commented out for iverilog compatibility)
    // =============================================================================
    
    // synthesis translate_off
    /*
    // Assert that VC ID is valid for write
    property valid_wr_vc_id;
        @(posedge clk) disable iff (!rst_n)
        wr_en |-> (wr_vc_id < NUM_VCS);
    endproperty
    assert property (valid_wr_vc_id) else $error("Invalid write VC ID: %0d", wr_vc_id);
    
    // Assert that VC ID is valid for read
    property valid_rd_vc_id;
        @(posedge clk) disable iff (!rst_n)
        rd_en |-> (rd_vc_id < NUM_VCS);
    endproperty
    assert property (valid_rd_vc_id) else $error("Invalid read VC ID: %0d", rd_vc_id);
    
    // Assert that only one VC write enable is active at a time
    property single_vc_write;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(vc_wr_en);
    endproperty
    assert property (single_vc_write) else $error("Multiple VC write enables active");
    
    // Assert that only one VC read enable is active at a time
    property single_vc_read;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(vc_rd_en);
    endproperty
    assert property (single_vc_read) else $error("Multiple VC read enables active");
    */
    // synthesis translate_on

endmodule : vc_buffer_manager
