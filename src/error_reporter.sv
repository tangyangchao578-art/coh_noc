// =============================================================================
// Error Reporter Module - Centralized Error Reporting Interface
// Task 13.1: Implement error reporting interface
// =============================================================================

import coh_noc_pkg::*;

module error_reporter #(
    parameter int MAX_ERROR_LOG = 64
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Error input from multiple sources
    input  logic        error_valid,
    input  logic [7:0]  error_code,
    input  logic [11:0] error_txn_id,
    input  logic [47:0] error_addr,
    input  logic [7:0]  error_source_id,
    
    // Error log interface
    output logic        log_full,
    output logic [7:0]  error_count,
    
    // Error query interface
    input  logic        query_enable,
    input  logic [5:0]  query_index,
    output logic        query_valid,
    output logic [7:0]  query_error_code,
    output logic [11:0] query_txn_id,
    output logic [47:0] query_addr,
    output logic [7:0]  query_source_id,
    output logic [31:0] query_timestamp,
    
    // Error statistics
    output logic [15:0] total_errors,
    output logic [15:0] crc_errors,
    output logic [15:0] timeout_errors,
    output logic [15:0] protocol_errors
);

    // =============================================================================
    // Error Log Entry Storage (separate arrays for iverilog compatibility)
    // =============================================================================
    
    // Error log storage using separate arrays
    logic        error_log_valid [0:MAX_ERROR_LOG-1];
    logic [7:0]  error_log_code [0:MAX_ERROR_LOG-1];
    logic [11:0] error_log_txn_id [0:MAX_ERROR_LOG-1];
    logic [47:0] error_log_addr [0:MAX_ERROR_LOG-1];
    logic [7:0]  error_log_source_id [0:MAX_ERROR_LOG-1];
    logic [31:0] error_log_timestamp [0:MAX_ERROR_LOG-1];
    
    // Write pointer for circular buffer
    logic [5:0] write_ptr;
    logic [7:0] entry_count;
    
    // Timestamp counter
    logic [31:0] timestamp_counter;
    
    // =============================================================================
    // Error Code Definitions (matching error_detection.sv)
    // =============================================================================
    
    localparam logic [7:0] ERR_NONE            = 8'h00;
    localparam logic [7:0] ERR_CRC_MISMATCH    = 8'h01;
    localparam logic [7:0] ERR_TIMEOUT         = 8'h02;
    localparam logic [7:0] ERR_INVALID_OPCODE  = 8'h03;
    localparam logic [7:0] ERR_INVALID_VC      = 8'h04;
    localparam logic [7:0] ERR_BUFFER_OVERFLOW = 8'h05;
    localparam logic [7:0] ERR_PROTOCOL        = 8'h06;
    
    // =============================================================================
    // Timestamp Counter
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            timestamp_counter <= 32'h0;
        end else begin
            timestamp_counter <= timestamp_counter + 1;
        end
    end
    
    // =============================================================================
    // Error Logging Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            write_ptr <= 6'h0;
            entry_count <= 8'h0;
            
            // Clear error log
            for (int i = 0; i < MAX_ERROR_LOG; i++) begin
                error_log_valid[i] <= 1'b0;
                error_log_code[i] <= 8'h0;
                error_log_txn_id[i] <= 12'h0;
                error_log_addr[i] <= 48'h0;
                error_log_source_id[i] <= 8'h0;
                error_log_timestamp[i] <= 32'h0;
            end
        end else begin
            // Log new error
            if (error_valid && error_code != ERR_NONE) begin
                error_log_valid[write_ptr] <= 1'b1;
                error_log_code[write_ptr] <= error_code;
                error_log_txn_id[write_ptr] <= error_txn_id;
                error_log_addr[write_ptr] <= error_addr;
                error_log_source_id[write_ptr] <= error_source_id;
                error_log_timestamp[write_ptr] <= timestamp_counter;
                
                // Update write pointer (circular buffer)
                write_ptr <= write_ptr + 1;
                
                // Update entry count (saturate at MAX_ERROR_LOG)
                if (entry_count < MAX_ERROR_LOG) begin
                    entry_count <= entry_count + 1;
                end
            end
        end
    end
    
    // Log full indicator
    assign log_full = (entry_count >= MAX_ERROR_LOG);
    assign error_count = entry_count;
    
    // =============================================================================
    // Error Query Interface
    // =============================================================================
    
    always_comb begin
        if (query_enable && query_index < MAX_ERROR_LOG) begin
            query_valid = error_log_valid[query_index];
            query_error_code = error_log_code[query_index];
            query_txn_id = error_log_txn_id[query_index];
            query_addr = error_log_addr[query_index];
            query_source_id = error_log_source_id[query_index];
            query_timestamp = error_log_timestamp[query_index];
        end else begin
            query_valid = 1'b0;
            query_error_code = 8'h0;
            query_txn_id = 12'h0;
            query_addr = 48'h0;
            query_source_id = 8'h0;
            query_timestamp = 32'h0;
        end
    end
    
    // =============================================================================
    // Error Statistics
    // =============================================================================
    
    logic [15:0] total_err_cnt;
    logic [15:0] crc_err_cnt;
    logic [15:0] timeout_err_cnt;
    logic [15:0] protocol_err_cnt;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            total_err_cnt <= 16'h0;
            crc_err_cnt <= 16'h0;
            timeout_err_cnt <= 16'h0;
            protocol_err_cnt <= 16'h0;
        end else begin
            if (error_valid && error_code != ERR_NONE) begin
                // Increment total error count
                total_err_cnt <= total_err_cnt + 1;
                
                // Increment specific error type counters
                case (error_code)
                    ERR_CRC_MISMATCH: crc_err_cnt <= crc_err_cnt + 1;
                    ERR_TIMEOUT: timeout_err_cnt <= timeout_err_cnt + 1;
                    ERR_INVALID_OPCODE,
                    ERR_INVALID_VC,
                    ERR_PROTOCOL: protocol_err_cnt <= protocol_err_cnt + 1;
                    default: ;
                endcase
            end
        end
    end
    
    assign total_errors = total_err_cnt;
    assign crc_errors = crc_err_cnt;
    assign timeout_errors = timeout_err_cnt;
    assign protocol_errors = protocol_err_cnt;

endmodule : error_reporter
