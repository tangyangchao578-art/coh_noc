// =============================================================================
// Transaction Timeout Handler - Manages Transaction Timeouts and Recovery
// Task 13.2: Implement transaction timeout handling
// =============================================================================

import coh_noc_pkg::*;

module transaction_timeout_handler #(
    parameter int MAX_TRANSACTIONS = 256,
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int WARNING_CYCLES = 800
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Transaction start interface
    input  logic        txn_start,
    input  logic [11:0] txn_id,
    input  logic [7:0]  txn_src_id,
    input  logic [7:0]  txn_tgt_id,
    input  logic [47:0] txn_addr,
    
    // Transaction completion interface
    input  logic        txn_complete,
    input  logic [11:0] txn_complete_id,
    
    // Timeout detection outputs
    output logic        timeout_detected,
    output logic [11:0] timeout_txn_id,
    output logic [7:0]  timeout_src_id,
    output logic [7:0]  timeout_tgt_id,
    output logic [47:0] timeout_addr,
    
    // Warning outputs (before actual timeout)
    output logic        timeout_warning,
    output logic [11:0] warning_txn_id,
    
    // Recovery action interface
    input  logic        recovery_action,
    input  logic [11:0] recovery_txn_id,
    
    // Statistics
    output logic [15:0] active_txn_count,
    output logic [15:0] timeout_count,
    output logic [15:0] recovered_count
);

    // =============================================================================
    // Transaction Tracking Entry
    // =============================================================================
    
    typedef struct packed {
        logic        valid;
        logic [11:0] txn_id;
        logic [7:0]  src_id;
        logic [7:0]  tgt_id;
        logic [47:0] addr;
        logic [15:0] timer;
        logic        warning_issued;
    } txn_track_entry_t;
    
    // Transaction tracking table
    txn_track_entry_t txn_table [MAX_TRANSACTIONS-1:0];
    
    // Statistics counters
    logic [15:0] active_count;
    logic [15:0] timeout_cnt;
    logic [15:0] recovered_cnt;
    
    assign active_txn_count = active_count;
    assign timeout_count = timeout_cnt;
    assign recovered_count = recovered_cnt;
    
    // =============================================================================
    // Helper Functions
    // =============================================================================
    
    // Find free entry for new transaction
    function automatic int find_free_entry();
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (!txn_table[i].valid) return i;
        end
        return -1;  // No free entry
    endfunction
    
    // Find entry by transaction ID
    function automatic int find_txn_entry(input logic [11:0] id);
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (txn_table[i].valid && txn_table[i].txn_id == id) return i;
        end
        return -1;  // Not found
    endfunction
    
    // =============================================================================
    // Transaction Tracking Logic
    // =============================================================================
    
    integer free_idx, complete_idx, recovery_idx;
    logic timeout_found, warning_found;
    logic [11:0] found_timeout_id, found_warning_id;
    logic [7:0] found_timeout_src, found_timeout_tgt;
    logic [47:0] found_timeout_addr;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all transaction entries
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                txn_table[i].valid <= 1'b0;
                txn_table[i].txn_id <= 12'h0;
                txn_table[i].src_id <= 8'h0;
                txn_table[i].tgt_id <= 8'h0;
                txn_table[i].addr <= 48'h0;
                txn_table[i].timer <= 16'h0;
                txn_table[i].warning_issued <= 1'b0;
            end
            
            active_count <= 16'h0;
            timeout_cnt <= 16'h0;
            recovered_cnt <= 16'h0;
            
            timeout_detected <= 1'b0;
            timeout_txn_id <= 12'h0;
            timeout_src_id <= 8'h0;
            timeout_tgt_id <= 8'h0;
            timeout_addr <= 48'h0;
            
            timeout_warning <= 1'b0;
            warning_txn_id <= 12'h0;
        end else begin
            timeout_found = 1'b0;
            warning_found = 1'b0;
            found_timeout_id = 12'h0;
            found_warning_id = 12'h0;
            found_timeout_src = 8'h0;
            found_timeout_tgt = 8'h0;
            found_timeout_addr = 48'h0;
            
            // Start new transaction tracking
            if (txn_start) begin
                free_idx = find_free_entry();
                if (free_idx >= 0) begin
                    txn_table[free_idx].valid <= 1'b1;
                    txn_table[free_idx].txn_id <= txn_id;
                    txn_table[free_idx].src_id <= txn_src_id;
                    txn_table[free_idx].tgt_id <= txn_tgt_id;
                    txn_table[free_idx].addr <= txn_addr;
                    txn_table[free_idx].timer <= 16'h0;
                    txn_table[free_idx].warning_issued <= 1'b0;
                    
                    active_count <= active_count + 1;
                end
            end
            
            // Complete transaction
            if (txn_complete) begin
                complete_idx = find_txn_entry(txn_complete_id);
                if (complete_idx >= 0) begin
                    txn_table[complete_idx].valid <= 1'b0;
                    if (active_count > 0) begin
                        active_count <= active_count - 1;
                    end
                end
            end
            
            // Handle recovery action
            if (recovery_action) begin
                recovery_idx = find_txn_entry(recovery_txn_id);
                if (recovery_idx >= 0) begin
                    // Reset timer to give more time
                    txn_table[recovery_idx].timer <= 16'h0;
                    txn_table[recovery_idx].warning_issued <= 1'b0;
                    recovered_cnt <= recovered_cnt + 1;
                end
            end
            
            // Update timers and check for timeouts/warnings
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (txn_table[i].valid) begin
                    txn_table[i].timer <= txn_table[i].timer + 1;
                    
                    // Check for timeout
                    if (txn_table[i].timer >= TIMEOUT_CYCLES) begin
                        timeout_found = 1'b1;
                        found_timeout_id = txn_table[i].txn_id;
                        found_timeout_src = txn_table[i].src_id;
                        found_timeout_tgt = txn_table[i].tgt_id;
                        found_timeout_addr = txn_table[i].addr;
                        
                        // Clear the timed-out transaction
                        txn_table[i].valid <= 1'b0;
                        if (active_count > 0) begin
                            active_count <= active_count - 1;
                        end
                        timeout_cnt <= timeout_cnt + 1;
                    end
                    // Check for warning threshold
                    else if (txn_table[i].timer >= WARNING_CYCLES && 
                             !txn_table[i].warning_issued) begin
                        warning_found = 1'b1;
                        found_warning_id = txn_table[i].txn_id;
                        txn_table[i].warning_issued <= 1'b1;
                    end
                end
            end
            
            // Update timeout outputs
            timeout_detected <= timeout_found;
            timeout_txn_id <= found_timeout_id;
            timeout_src_id <= found_timeout_src;
            timeout_tgt_id <= found_timeout_tgt;
            timeout_addr <= found_timeout_addr;
            
            // Update warning outputs
            timeout_warning <= warning_found;
            warning_txn_id <= found_warning_id;
        end
    end
    
    // =============================================================================
    // Debug and Monitoring
    // =============================================================================
    
    // Synthesis translate_off
    // Assertions for debugging
    
    // Check for transaction ID conflicts
    always @(posedge clk) begin
        if (rst_n && txn_start) begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (txn_table[i].valid && txn_table[i].txn_id == txn_id) begin
                    $display("WARNING: Transaction ID %h already active at time %t", 
                             txn_id, $time);
                end
            end
        end
    end
    
    // Monitor timeout events
    always @(posedge clk) begin
        if (rst_n && timeout_detected) begin
            $display("TIMEOUT: Transaction %h from node %h to node %h timed out at time %t",
                     timeout_txn_id, timeout_src_id, timeout_tgt_id, $time);
        end
    end
    
    // Monitor warning events
    always @(posedge clk) begin
        if (rst_n && timeout_warning) begin
            $display("WARNING: Transaction %h approaching timeout at time %t",
                     warning_txn_id, $time);
        end
    end
    
    // synthesis translate_on

endmodule : transaction_timeout_handler
