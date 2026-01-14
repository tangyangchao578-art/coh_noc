// =============================================================================
// Credit-Based Flow Control Module
// Requirements: 3.2, 8.1, 8.2
// =============================================================================

import coh_noc_pkg::*;

module credit_flow_control #(
    parameter int MAX_CREDITS = 16,
    parameter int NUM_VCS = 4
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Credit tracking per VC
    output logic [CREDIT_COUNT_WIDTH-1:0] credit_count [0:NUM_VCS-1],
    output logic [NUM_VCS-1:0]            credit_available,
    
    // Credit consumption (when sending flit)
    input  logic        consume_credit,
    input  logic [1:0]  consume_vc_id,
    
    // Credit return (when receiving flit from downstream)
    input  logic        return_credit,
    input  logic [1:0]  return_vc_id,
    
    // Backpressure signals
    output logic [NUM_VCS-1:0] backpressure
);

    // =============================================================================
    // Credit Counters per VC
    // =============================================================================
    
    logic [CREDIT_COUNT_WIDTH-1:0] credits [0:NUM_VCS-1];
    
    // Assign outputs
    genvar i;
    generate
        for (i = 0; i < NUM_VCS; i++) begin : gen_credit_outputs
            assign credit_count[i] = credits[i];
            assign credit_available[i] = (credits[i] > 0);
            assign backpressure[i] = (credits[i] == 0);
        end
    endgenerate
    
    // =============================================================================
    // Credit Management Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize all VCs with maximum credits
            for (int v = 0; v < NUM_VCS; v++) begin
                credits[v] <= MAX_CREDITS;
            end
        end else begin
            // Handle credit consumption and return for each VC
            for (int v = 0; v < NUM_VCS; v++) begin
                case ({consume_credit && (consume_vc_id == v), return_credit && (return_vc_id == v)})
                    2'b10: begin
                        // Consume credit only
                        if (credits[v] > 0) begin
                            credits[v] <= credits[v] - 1;
                        end
                    end
                    2'b01: begin
                        // Return credit only
                        if (credits[v] < MAX_CREDITS) begin
                            credits[v] <= credits[v] + 1;
                        end
                    end
                    2'b11: begin
                        // Both consume and return (no net change)
                        credits[v] <= credits[v];
                    end
                    default: begin
                        // No change
                        credits[v] <= credits[v];
                    end
                endcase
            end
        end
    end
    
    // =============================================================================
    // Overflow/Underflow Protection (commented out for iverilog compatibility)
    // =============================================================================
    
    // synthesis translate_off
    /*
    // Check for credit underflow
    always_ff @(posedge clk) begin
        if (rst_n) begin
            for (int v = 0; v < NUM_VCS; v++) begin
                if (consume_credit && (consume_vc_id == v) && (credits[v] == 0)) begin
                    $error("Credit underflow on VC%0d", v);
                end
            end
        end
    end
    
    // Check for credit overflow
    always_ff @(posedge clk) begin
        if (rst_n) begin
            for (int v = 0; v < NUM_VCS; v++) begin
                if (return_credit && (return_vc_id == v) && (credits[v] == MAX_CREDITS)) begin
                    $error("Credit overflow on VC%0d", v);
                end
            end
        end
    end
    */
    // synthesis translate_on

endmodule : credit_flow_control
