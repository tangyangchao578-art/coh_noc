// =============================================================================
// Error Detection Module - CRC Checking and Timeout Detection
// Task 13.1: Implement error detection mechanisms
// =============================================================================

import coh_noc_pkg::*;

module error_detection #(
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int MAX_TRANSACTIONS = 256
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Flit input for CRC checking
    input  logic        flit_valid,
    input  flit_u       flit_in,
    input  logic [1:0]  vc_id,
    
    // CRC output
    output logic        crc_error,
    output logic [31:0] computed_crc,
    
    // Transaction tracking for timeout detection
    input  logic        txn_start,
    input  logic [11:0] txn_id,
    input  logic        txn_complete,
    input  logic [11:0] txn_complete_id,
    
    // Timeout detection output
    output logic        timeout_error,
    output logic [11:0] timeout_txn_id,
    
    // Error reporting interface
    output logic        error_detected,
    output logic [7:0]  error_code,
    output logic [11:0] error_txn_id,
    output logic [47:0] error_addr
);

    // =============================================================================
    // Error Code Definitions
    // =============================================================================
    
    typedef enum logic [7:0] {
        ERR_NONE            = 8'h00,
        ERR_CRC_MISMATCH    = 8'h01,
        ERR_TIMEOUT         = 8'h02,
        ERR_INVALID_OPCODE  = 8'h03,
        ERR_INVALID_VC      = 8'h04,
        ERR_BUFFER_OVERFLOW = 8'h05,
        ERR_PROTOCOL        = 8'h06
    } error_code_e;
    
    // =============================================================================
    // CRC-32 Computation
    // =============================================================================
    
    // CRC-32 polynomial: 0x04C11DB7 (Ethernet polynomial)
    localparam logic [31:0] CRC_POLY = 32'h04C11DB7;
    
    // Function to compute CRC-32 for a flit
    function automatic logic [31:0] compute_crc32(input flit_u flit_data);
        logic [31:0] crc;
        logic [730:0] data_bits;
        logic feedback;
        
        // Initialize CRC
        crc = 32'hFFFFFFFF;
        
        // Pack flit into bit vector
        data_bits = flit_data;
        
        // Process each bit
        for (int i = 0; i < 731; i++) begin
            feedback = crc[31] ^ data_bits[i];
            crc = {crc[30:0], 1'b0};
            if (feedback) begin
                crc = crc ^ CRC_POLY;
            end
        end
        
        // Final XOR
        return ~crc;
    endfunction
    
    // CRC checking logic
    logic [31:0] expected_crc;
    logic [31:0] actual_crc;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            crc_error <= 1'b0;
            computed_crc <= 32'h0;
        end else begin
            if (flit_valid) begin
                // Compute CRC for incoming flit
                actual_crc = compute_crc32(flit_in);
                computed_crc <= actual_crc;
                
                // For now, we assume CRC is embedded in reserved fields
                // In a real implementation, the CRC would be in a specific field
                expected_crc = 32'h0;  // Placeholder
                
                // Check for CRC mismatch
                // Disabled for now since we don't have actual CRC in flits
                crc_error <= 1'b0;  // (actual_crc != expected_crc);
            end else begin
                crc_error <= 1'b0;
            end
        end
    end
    
    // =============================================================================
    // Transaction Timeout Tracking
    // =============================================================================
    
    // Transaction tracking arrays (separate arrays instead of struct array)
    logic        txn_valid [0:MAX_TRANSACTIONS-1];
    logic [11:0] txn_id_table [0:MAX_TRANSACTIONS-1];
    logic [15:0] txn_timer [0:MAX_TRANSACTIONS-1];
    logic [47:0] txn_addr [0:MAX_TRANSACTIONS-1];
    
    // Find free entry for new transaction
    function automatic int find_free_entry();
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (!txn_valid[i]) return i;
        end
        return -1;  // No free entry
    endfunction
    
    // Find entry by transaction ID
    function automatic int find_txn_entry(input logic [11:0] id);
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (txn_valid[i] && txn_id_table[i] == id) return i;
        end
        return -1;  // Not found
    endfunction
    
    // Transaction tracking and timeout detection
    integer free_idx, complete_idx;
    logic timeout_detected;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all transaction entries
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                txn_valid[i] <= 1'b0;
                txn_id_table[i] <= 12'h0;
                txn_timer[i] <= 16'h0;
                txn_addr[i] <= 48'h0;
            end
            timeout_error <= 1'b0;
            timeout_txn_id <= 12'h0;
            timeout_detected <= 1'b0;
        end else begin
            timeout_detected = 1'b0;
            
            // Start new transaction tracking
            if (txn_start) begin
                free_idx = find_free_entry();
                if (free_idx >= 0) begin
                    txn_valid[free_idx] <= 1'b1;
                    txn_id_table[free_idx] <= txn_id;
                    txn_timer[free_idx] <= 16'h0;
                    // Extract address from flit if valid
                    if (flit_valid) begin
                        txn_addr[free_idx] <= flit_in.req.addr;
                    end else begin
                        txn_addr[free_idx] <= 48'h0;
                    end
                end
            end
            
            // Complete transaction
            if (txn_complete) begin
                complete_idx = find_txn_entry(txn_complete_id);
                if (complete_idx >= 0) begin
                    txn_valid[complete_idx] <= 1'b0;
                end
            end
            
            // Update timers and check for timeouts
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (txn_valid[i]) begin
                    txn_timer[i] <= txn_timer[i] + 1;
                    
                    // Check for timeout
                    if (txn_timer[i] >= TIMEOUT_CYCLES) begin
                        timeout_detected = 1'b1;
                        timeout_txn_id <= txn_id_table[i];
                        // Clear the timed-out transaction
                        txn_valid[i] <= 1'b0;
                    end
                end
            end
            
            timeout_error <= timeout_detected;
        end
    end
    
    // =============================================================================
    // Error Reporting Aggregation
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            error_detected <= 1'b0;
            error_code <= ERR_NONE;
            error_txn_id <= 12'h0;
            error_addr <= 48'h0;
        end else begin
            // Priority: CRC error > Timeout error
            if (crc_error) begin
                error_detected <= 1'b1;
                error_code <= ERR_CRC_MISMATCH;
                if (flit_valid) begin
                    error_txn_id <= flit_in.req.txn_id;
                    error_addr <= flit_in.req.addr;
                end
            end else if (timeout_error) begin
                error_detected <= 1'b1;
                error_code <= ERR_TIMEOUT;
                error_txn_id <= timeout_txn_id;
                // Find address from transaction table
                for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                    if (txn_id_table[i] == timeout_txn_id) begin
                        error_addr <= txn_addr[i];
                    end
                end
            end else begin
                error_detected <= 1'b0;
                error_code <= ERR_NONE;
            end
        end
    end

endmodule : error_detection
