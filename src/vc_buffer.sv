// =============================================================================
// Virtual Channel Buffer - Independent VC FIFO Buffer Management
// Requirements: 3.5, 8.3
// =============================================================================

import coh_noc_pkg::*;

module vc_buffer #(
    parameter int BUFFER_DEPTH = 16,
    parameter int VC_ID = 0
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Write interface
    input  logic        wr_en,
    input  flit_u       wr_data,
    output logic        full,
    output logic        almost_full,
    
    // Read interface
    input  logic        rd_en,
    output flit_u       rd_data,
    output logic        empty,
    output logic        almost_empty,
    
    // Status signals
    output logic [7:0]  count,
    output logic [7:0]  free_slots
);

    // =============================================================================
    // FIFO Storage
    // =============================================================================
    
    flit_u buffer_mem [0:BUFFER_DEPTH-1];
    
    // =============================================================================
    // Pointers and Counters
    // =============================================================================
    
    logic [$clog2(BUFFER_DEPTH)-1:0] wr_ptr;
    logic [$clog2(BUFFER_DEPTH)-1:0] rd_ptr;
    logic [7:0] entry_count;
    
    // =============================================================================
    // Status Signals
    // =============================================================================
    
    assign count = entry_count;
    assign free_slots = BUFFER_DEPTH - entry_count;
    assign empty = (entry_count == 0);
    assign full = (entry_count == BUFFER_DEPTH);
    assign almost_full = (entry_count >= BUFFER_DEPTH - 2);
    assign almost_empty = (entry_count <= 2);
    
    // =============================================================================
    // Write Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else begin
            if (wr_en && !full) begin
                buffer_mem[wr_ptr] <= wr_data;
                wr_ptr <= (wr_ptr + 1) % BUFFER_DEPTH;
            end
        end
    end
    
    // =============================================================================
    // Read Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
            rd_data <= '0;
        end else begin
            if (rd_en && !empty) begin
                rd_data <= buffer_mem[rd_ptr];
                rd_ptr <= (rd_ptr + 1) % BUFFER_DEPTH;
            end
        end
    end
    
    // =============================================================================
    // Entry Counter
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            entry_count <= '0;
        end else begin
            case ({wr_en && !full, rd_en && !empty})
                2'b10: entry_count <= entry_count + 1;  // Write only
                2'b01: entry_count <= entry_count - 1;  // Read only
                2'b11: entry_count <= entry_count;      // Both (no change)
                default: entry_count <= entry_count;    // Neither
            endcase
        end
    end
    
    // =============================================================================
    // Assertions for Verification (commented out for iverilog compatibility)
    // =============================================================================
    
    // synthesis translate_off
    /*
    // Assert that count never exceeds buffer depth
    property count_within_bounds;
        @(posedge clk) disable iff (!rst_n)
        entry_count <= BUFFER_DEPTH;
    endproperty
    assert property (count_within_bounds) else $error("VC%0d: Entry count exceeds buffer depth", VC_ID);
    
    // Assert that full flag is correct
    property full_flag_correct;
        @(posedge clk) disable iff (!rst_n)
        full == (entry_count == BUFFER_DEPTH);
    endproperty
    assert property (full_flag_correct) else $error("VC%0d: Full flag incorrect", VC_ID);
    
    // Assert that empty flag is correct
    property empty_flag_correct;
        @(posedge clk) disable iff (!rst_n)
        empty == (entry_count == 0);
    endproperty
    assert property (empty_flag_correct) else $error("VC%0d: Empty flag incorrect", VC_ID);
    */
    // synthesis translate_on

endmodule : vc_buffer
