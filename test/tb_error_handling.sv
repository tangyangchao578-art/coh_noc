// =============================================================================
// Error Handling Testbench - Tests Error Detection and Recovery
// Task 13.3: Test error handling mechanisms
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;
`include "coh_noc_types.sv"

module tb_error_handling;

    // =============================================================================
    // Clock and Reset
    // =============================================================================
    
    logic clk;
    logic rst_n;
    
    // Clock generation (100MHz)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // DUT Signals - Error Detection
    // =============================================================================
    
    logic        ed_flit_valid;
    flit_u       ed_flit_in;
    logic [1:0]  ed_vc_id;
    logic        ed_crc_error;
    logic [31:0] ed_computed_crc;
    logic        ed_txn_start;
    logic [11:0] ed_txn_id;
    logic        ed_txn_complete;
    logic [11:0] ed_txn_complete_id;
    logic        ed_timeout_error;
    logic [11:0] ed_timeout_txn_id;
    logic        ed_error_detected;
    logic [7:0]  ed_error_code;
    logic [11:0] ed_error_txn_id;
    logic [47:0] ed_error_addr;
    
    // =============================================================================
    // DUT Signals - Error Reporter
    // =============================================================================
    
    logic        er_error_valid;
    logic [7:0]  er_error_code;
    logic [11:0] er_error_txn_id;
    logic [47:0] er_error_addr;
    logic [7:0]  er_error_source_id;
    logic        er_log_full;
    logic [7:0]  er_error_count;
    logic        er_query_enable;
    logic [5:0]  er_query_index;
    logic        er_query_valid;
    logic [7:0]  er_query_error_code;
    logic [11:0] er_query_txn_id;
    logic [47:0] er_query_addr;
    logic [7:0]  er_query_source_id;
    logic [31:0] er_query_timestamp;
    logic [15:0] er_total_errors;
    logic [15:0] er_crc_errors;
    logic [15:0] er_timeout_errors;
    logic [15:0] er_protocol_errors;
    
    // =============================================================================
    // DUT Signals - Retransmit Controller
    // =============================================================================
    
    logic        rc_tx_valid;
    flit_u       rc_tx_flit;
    logic [1:0]  rc_tx_vc_id;
    logic        rc_tx_ready;
    logic        rc_net_tx_valid;
    flit_u       rc_net_tx_flit;
    logic [1:0]  rc_net_tx_vc_id;
    logic        rc_net_tx_ready;
    logic        rc_error_detected;
    logic [11:0] rc_error_txn_id;
    logic [7:0]  rc_error_code;
    logic        rc_ack_valid;
    logic [11:0] rc_ack_txn_id;
    logic        rc_retransmit_active;
    logic [7:0]  rc_pending_count;
    logic [7:0]  rc_retry_count;
    
    // =============================================================================
    // DUT Signals - Transaction Timeout Handler
    // =============================================================================
    
    logic        th_txn_start;
    logic [11:0] th_txn_id;
    logic [7:0]  th_txn_src_id;
    logic [7:0]  th_txn_tgt_id;
    logic [47:0] th_txn_addr;
    logic        th_txn_complete;
    logic [11:0] th_txn_complete_id;
    logic        th_timeout_detected;
    logic [11:0] th_timeout_txn_id;
    logic [7:0]  th_timeout_src_id;
    logic [7:0]  th_timeout_tgt_id;
    logic [47:0] th_timeout_addr;
    logic        th_timeout_warning;
    logic [11:0] th_warning_txn_id;
    logic        th_recovery_action;
    logic [11:0] th_recovery_txn_id;
    logic [15:0] th_active_txn_count;
    logic [15:0] th_timeout_count;
    logic [15:0] th_recovered_count;
    
    // =============================================================================
    // DUT Instantiations
    // =============================================================================
    
    error_detection #(
        .TIMEOUT_CYCLES(100),
        .MAX_TRANSACTIONS(16)
    ) dut_error_detection (
        .clk(clk),
        .rst_n(rst_n),
        .flit_valid(ed_flit_valid),
        .flit_in(ed_flit_in),
        .vc_id(ed_vc_id),
        .crc_error(ed_crc_error),
        .computed_crc(ed_computed_crc),
        .txn_start(ed_txn_start),
        .txn_id(ed_txn_id),
        .txn_complete(ed_txn_complete),
        .txn_complete_id(ed_txn_complete_id),
        .timeout_error(ed_timeout_error),
        .timeout_txn_id(ed_timeout_txn_id),
        .error_detected(ed_error_detected),
        .error_code(ed_error_code),
        .error_txn_id(ed_error_txn_id),
        .error_addr(ed_error_addr)
    );
    
    error_reporter #(
        .MAX_ERROR_LOG(64)
    ) dut_error_reporter (
        .clk(clk),
        .rst_n(rst_n),
        .error_valid(er_error_valid),
        .error_code(er_error_code),
        .error_txn_id(er_error_txn_id),
        .error_addr(er_error_addr),
        .error_source_id(er_error_source_id),
        .log_full(er_log_full),
        .error_count(er_error_count),
        .query_enable(er_query_enable),
        .query_index(er_query_index),
        .query_valid(er_query_valid),
        .query_error_code(er_query_error_code),
        .query_txn_id(er_query_txn_id),
        .query_addr(er_query_addr),
        .query_source_id(er_query_source_id),
        .query_timestamp(er_query_timestamp),
        .total_errors(er_total_errors),
        .crc_errors(er_crc_errors),
        .timeout_errors(er_timeout_errors),
        .protocol_errors(er_protocol_errors)
    );
    
    retransmit_controller #(
        .BUFFER_DEPTH(16),
        .MAX_RETRIES(3),
        .RETRY_TIMEOUT(50)
    ) dut_retransmit (
        .clk(clk),
        .rst_n(rst_n),
        .tx_valid(rc_tx_valid),
        .tx_flit(rc_tx_flit),
        .tx_vc_id(rc_tx_vc_id),
        .tx_ready(rc_tx_ready),
        .net_tx_valid(rc_net_tx_valid),
        .net_tx_flit(rc_net_tx_flit),
        .net_tx_vc_id(rc_net_tx_vc_id),
        .net_tx_ready(rc_net_tx_ready),
        .error_detected(rc_error_detected),
        .error_txn_id(rc_error_txn_id),
        .error_code(rc_error_code),
        .ack_valid(rc_ack_valid),
        .ack_txn_id(rc_ack_txn_id),
        .retransmit_active(rc_retransmit_active),
        .pending_count(rc_pending_count),
        .retry_count(rc_retry_count)
    );
    
    transaction_timeout_handler #(
        .MAX_TRANSACTIONS(16),
        .TIMEOUT_CYCLES(100),
        .WARNING_CYCLES(80)
    ) dut_timeout_handler (
        .clk(clk),
        .rst_n(rst_n),
        .txn_start(th_txn_start),
        .txn_id(th_txn_id),
        .txn_src_id(th_txn_src_id),
        .txn_tgt_id(th_txn_tgt_id),
        .txn_addr(th_txn_addr),
        .txn_complete(th_txn_complete),
        .txn_complete_id(th_txn_complete_id),
        .timeout_detected(th_timeout_detected),
        .timeout_txn_id(th_timeout_txn_id),
        .timeout_src_id(th_timeout_src_id),
        .timeout_tgt_id(th_timeout_tgt_id),
        .timeout_addr(th_timeout_addr),
        .timeout_warning(th_timeout_warning),
        .warning_txn_id(th_warning_txn_id),
        .recovery_action(th_recovery_action),
        .recovery_txn_id(th_recovery_txn_id),
        .active_txn_count(th_active_txn_count),
        .timeout_count(th_timeout_count),
        .recovered_count(th_recovered_count)
    );
    
    // =============================================================================
    // Test Variables
    // =============================================================================
    
    int test_pass_count = 0;
    int test_fail_count = 0;
    
    // =============================================================================
    // Helper Tasks
    // =============================================================================
    
    task reset_system();
        rst_n = 0;
        
        // Initialize all inputs
        ed_flit_valid = 0;
        ed_flit_in = '0;
        ed_vc_id = 0;
        ed_txn_start = 0;
        ed_txn_id = 0;
        ed_txn_complete = 0;
        ed_txn_complete_id = 0;
        
        er_error_valid = 0;
        er_error_code = 0;
        er_error_txn_id = 0;
        er_error_addr = 0;
        er_error_source_id = 0;
        er_query_enable = 0;
        er_query_index = 0;
        
        rc_tx_valid = 0;
        rc_tx_flit = '0;
        rc_tx_vc_id = 0;
        rc_net_tx_ready = 0;
        rc_error_detected = 0;
        rc_error_txn_id = 0;
        rc_error_code = 0;
        rc_ack_valid = 0;
        rc_ack_txn_id = 0;
        
        th_txn_start = 0;
        th_txn_id = 0;
        th_txn_src_id = 0;
        th_txn_tgt_id = 0;
        th_txn_addr = 0;
        th_txn_complete = 0;
        th_txn_complete_id = 0;
        th_recovery_action = 0;
        th_recovery_txn_id = 0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);
    endtask
    
    task send_flit(input logic [11:0] txn_id, input logic [47:0] addr);
        req_flit_t req_flit;
        
        req_flit = pack_req_flit(
            REQ_READ_SHARED,
            addr,
            txn_id,
            8'h01,  // src_id
            8'h02,  // tgt_id
            3'b110, // size (64 bytes)
            3'b000, // mem_attr
            4'h0,   // qos
            1'b0,   // ns
            1'b0,   // likely_shared
            1'b1,   // allow_retry
            1'b0    // order
        );
        
        ed_flit_in.req = req_flit;
        ed_flit_valid = 1;
        ed_vc_id = VC_REQ;
        
        @(posedge clk);
        ed_flit_valid = 0;
    endtask
    
    // =============================================================================
    // Test Cases
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Error Handling Testbench");
        $display("=============================================================================");
        
        reset_system();
        
        // =========================================================================
        // Test 1: Transaction Timeout Detection
        // =========================================================================
        $display("\n[TEST 1] Transaction Timeout Detection");
        
        // Start a transaction
        th_txn_start = 1;
        th_txn_id = 12'h123;
        th_txn_src_id = 8'h01;
        th_txn_tgt_id = 8'h02;
        th_txn_addr = 48'h1000;
        @(posedge clk);
        th_txn_start = 0;
        
        // Wait for warning
        repeat(85) @(posedge clk);
        
        if (th_timeout_warning && th_warning_txn_id == 12'h123) begin
            $display("  PASS: Timeout warning detected for transaction 0x123");
            test_pass_count++;
        end else begin
            $display("  FAIL: Timeout warning not detected");
            test_fail_count++;
        end
        
        // Wait for actual timeout
        repeat(20) @(posedge clk);
        
        if (th_timeout_detected && th_timeout_txn_id == 12'h123) begin
            $display("  PASS: Timeout detected for transaction 0x123");
            test_pass_count++;
        end else begin
            $display("  FAIL: Timeout not detected");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 2: Transaction Completion (No Timeout)
        // =========================================================================
        $display("\n[TEST 2] Transaction Completion (No Timeout)");
        
        // Start a transaction
        th_txn_start = 1;
        th_txn_id = 12'h456;
        th_txn_src_id = 8'h03;
        th_txn_tgt_id = 8'h04;
        th_txn_addr = 48'h2000;
        @(posedge clk);
        th_txn_start = 0;
        
        // Complete it before timeout
        repeat(50) @(posedge clk);
        th_txn_complete = 1;
        th_txn_complete_id = 12'h456;
        @(posedge clk);
        th_txn_complete = 0;
        
        // Wait and verify no timeout
        repeat(60) @(posedge clk);
        
        if (!th_timeout_detected) begin
            $display("  PASS: No timeout for completed transaction");
            test_pass_count++;
        end else begin
            $display("  FAIL: Unexpected timeout");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 3: Error Reporter Logging
        // =========================================================================
        $display("\n[TEST 3] Error Reporter Logging");
        
        // Log multiple errors
        for (int i = 0; i < 5; i++) begin
            er_error_valid = 1;
            er_error_code = 8'h01 + i;  // Different error codes
            er_error_txn_id = 12'h100 + i;
            er_error_addr = 48'h3000 + (i * 64);
            er_error_source_id = 8'h10 + i;
            @(posedge clk);
        end
        er_error_valid = 0;
        
        repeat(5) @(posedge clk);
        
        if (er_error_count == 5) begin
            $display("  PASS: Error count correct (5 errors logged)");
            test_pass_count++;
        end else begin
            $display("  FAIL: Error count incorrect (expected 5, got %0d)", er_error_count);
            test_fail_count++;
        end
        
        // Query logged errors
        er_query_enable = 1;
        er_query_index = 0;
        @(posedge clk);
        
        if (er_query_valid && er_query_error_code == 8'h01 && er_query_txn_id == 12'h100) begin
            $display("  PASS: Error query returned correct data");
            test_pass_count++;
        end else begin
            $display("  FAIL: Error query returned incorrect data");
            test_fail_count++;
        end
        
        er_query_enable = 0;
        
        // =========================================================================
        // Test 4: Retransmit Controller - Normal Transmission
        // =========================================================================
        $display("\n[TEST 4] Retransmit Controller - Normal Transmission");
        
        // Send a flit
        rc_tx_valid = 1;
        rc_tx_flit.req = pack_req_flit(
            REQ_READ_SHARED, 48'h4000, 12'h789, 8'h05, 8'h06,
            3'b110, 3'b000, 4'h0, 1'b0, 1'b0, 1'b1, 1'b0
        );
        rc_tx_vc_id = VC_REQ;
        rc_net_tx_ready = 1;
        
        @(posedge clk);
        
        if (rc_net_tx_valid && rc_tx_ready) begin
            $display("  PASS: Flit transmitted successfully");
            test_pass_count++;
        end else begin
            $display("  FAIL: Flit transmission failed");
            test_fail_count++;
        end
        
        rc_tx_valid = 0;
        
        // Send acknowledgment
        repeat(5) @(posedge clk);
        rc_ack_valid = 1;
        rc_ack_txn_id = 12'h789;
        @(posedge clk);
        rc_ack_valid = 0;
        
        repeat(5) @(posedge clk);
        
        // =========================================================================
        // Test 5: Retransmit Controller - Error and Retry
        // =========================================================================
        $display("\n[TEST 5] Retransmit Controller - Error and Retry");
        
        // Send a flit
        rc_tx_valid = 1;
        rc_tx_flit.req = pack_req_flit(
            REQ_READ_SHARED, 48'h5000, 12'hABC, 8'h07, 8'h08,
            3'b110, 3'b000, 4'h0, 1'b0, 1'b0, 1'b1, 1'b0
        );
        rc_tx_vc_id = VC_REQ;
        rc_net_tx_ready = 1;
        
        @(posedge clk);
        rc_tx_valid = 0;
        
        // Simulate error
        repeat(10) @(posedge clk);
        rc_error_detected = 1;
        rc_error_txn_id = 12'hABC;
        rc_error_code = 8'h01;  // CRC error
        @(posedge clk);
        rc_error_detected = 0;
        
        // Wait for retransmission
        repeat(5) @(posedge clk);
        
        if (rc_retransmit_active) begin
            $display("  PASS: Retransmission activated");
            test_pass_count++;
        end else begin
            $display("  FAIL: Retransmission not activated");
            test_fail_count++;
        end
        
        // Allow retransmission
        rc_net_tx_ready = 1;
        repeat(10) @(posedge clk);
        
        if (rc_retry_count > 0) begin
            $display("  PASS: Retry count incremented");
            test_pass_count++;
        end else begin
            $display("  FAIL: Retry count not incremented");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 6: Multiple Concurrent Errors
        // =========================================================================
        $display("\n[TEST 6] Multiple Concurrent Errors");
        
        reset_system();
        
        // Start multiple transactions
        for (int i = 0; i < 3; i++) begin
            th_txn_start = 1;
            th_txn_id = 12'h200 + i;
            th_txn_src_id = 8'h10 + i;
            th_txn_tgt_id = 8'h20 + i;
            th_txn_addr = 48'h6000 + (i * 64);
            @(posedge clk);
        end
        th_txn_start = 0;
        
        // Wait for all to timeout
        repeat(110) @(posedge clk);
        
        if (th_timeout_count >= 3) begin
            $display("  PASS: Multiple timeouts detected (count=%0d)", th_timeout_count);
            test_pass_count++;
        end else begin
            $display("  FAIL: Not all timeouts detected (count=%0d)", th_timeout_count);
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 7: Error Reporter Statistics
        // =========================================================================
        $display("\n[TEST 7] Error Reporter Statistics");
        
        reset_system();
        
        // Generate different types of errors
        // CRC errors
        for (int i = 0; i < 3; i++) begin
            er_error_valid = 1;
            er_error_code = 8'h01;  // CRC error
            er_error_txn_id = 12'h300 + i;
            er_error_addr = 48'h7000 + (i * 64);
            er_error_source_id = 8'h30 + i;
            @(posedge clk);
        end
        
        // Timeout errors
        for (int i = 0; i < 2; i++) begin
            er_error_valid = 1;
            er_error_code = 8'h02;  // Timeout error
            er_error_txn_id = 12'h400 + i;
            er_error_addr = 48'h8000 + (i * 64);
            er_error_source_id = 8'h40 + i;
            @(posedge clk);
        end
        
        // Protocol errors
        for (int i = 0; i < 1; i++) begin
            er_error_valid = 1;
            er_error_code = 8'h06;  // Protocol error
            er_error_txn_id = 12'h500 + i;
            er_error_addr = 48'h9000 + (i * 64);
            er_error_source_id = 8'h50 + i;
            @(posedge clk);
        end
        
        er_error_valid = 0;
        repeat(5) @(posedge clk);
        
        if (er_total_errors == 6) begin
            $display("  PASS: Total error count correct (6)");
            test_pass_count++;
        end else begin
            $display("  FAIL: Total error count incorrect (expected 6, got %0d)", er_total_errors);
            test_fail_count++;
        end
        
        if (er_crc_errors == 3) begin
            $display("  PASS: CRC error count correct (3)");
            test_pass_count++;
        end else begin
            $display("  FAIL: CRC error count incorrect (expected 3, got %0d)", er_crc_errors);
            test_fail_count++;
        end
        
        if (er_timeout_errors == 2) begin
            $display("  PASS: Timeout error count correct (2)");
            test_pass_count++;
        end else begin
            $display("  FAIL: Timeout error count incorrect (expected 2, got %0d)", er_timeout_errors);
            test_fail_count++;
        end
        
        if (er_protocol_errors == 1) begin
            $display("  PASS: Protocol error count correct (1)");
            test_pass_count++;
        end else begin
            $display("  FAIL: Protocol error count incorrect (expected 1, got %0d)", er_protocol_errors);
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 8: Recovery Action
        // =========================================================================
        $display("\n[TEST 8] Recovery Action");
        
        reset_system();
        
        // Start a transaction
        th_txn_start = 1;
        th_txn_id = 12'h600;
        th_txn_src_id = 8'h60;
        th_txn_tgt_id = 8'h61;
        th_txn_addr = 48'hA000;
        @(posedge clk);
        th_txn_start = 0;
        
        // Wait for warning
        repeat(85) @(posedge clk);
        
        if (th_timeout_warning) begin
            $display("  PASS: Warning detected before timeout");
            test_pass_count++;
        end else begin
            $display("  FAIL: Warning not detected");
            test_fail_count++;
        end
        
        // Issue recovery action
        th_recovery_action = 1;
        th_recovery_txn_id = 12'h600;
        @(posedge clk);
        th_recovery_action = 0;
        
        // Wait and verify no timeout occurs
        repeat(30) @(posedge clk);
        
        if (!th_timeout_detected) begin
            $display("  PASS: Recovery action prevented timeout");
            test_pass_count++;
        end else begin
            $display("  FAIL: Timeout occurred despite recovery");
            test_fail_count++;
        end
        
        if (th_recovered_count > 0) begin
            $display("  PASS: Recovery count incremented");
            test_pass_count++;
        end else begin
            $display("  FAIL: Recovery count not incremented");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 9: Maximum Retry Limit
        // =========================================================================
        $display("\n[TEST 9] Maximum Retry Limit");
        
        reset_system();
        
        // Send a flit that will fail multiple times
        rc_tx_valid = 1;
        rc_tx_flit.req = pack_req_flit(
            REQ_READ_SHARED, 48'hB000, 12'h700, 8'h70, 8'h71,
            3'b110, 3'b000, 4'h0, 1'b0, 1'b0, 1'b1, 1'b0
        );
        rc_tx_vc_id = VC_REQ;
        rc_net_tx_ready = 1;
        
        @(posedge clk);
        rc_tx_valid = 0;
        
        // Simulate multiple errors (exceeding MAX_RETRIES)
        for (int i = 0; i < 4; i++) begin
            repeat(10) @(posedge clk);
            rc_error_detected = 1;
            rc_error_txn_id = 12'h700;
            rc_error_code = 8'h01;
            @(posedge clk);
            rc_error_detected = 0;
            
            // Allow retransmission attempt
            rc_net_tx_ready = 1;
            repeat(10) @(posedge clk);
        end
        
        // Verify retry limit was enforced
        repeat(20) @(posedge clk);
        
        if (rc_retry_count <= 3) begin  // MAX_RETRIES = 3
            $display("  PASS: Retry limit enforced (retry_count=%0d)", rc_retry_count);
            test_pass_count++;
        end else begin
            $display("  FAIL: Retry limit exceeded (retry_count=%0d)", rc_retry_count);
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 10: Error Log Full Condition
        // =========================================================================
        $display("\n[TEST 10] Error Log Full Condition");
        
        reset_system();
        
        // Fill the error log (MAX_ERROR_LOG = 64)
        for (int i = 0; i < 65; i++) begin
            er_error_valid = 1;
            er_error_code = 8'h01;
            er_error_txn_id = 12'h800 + i;
            er_error_addr = 48'hC000 + (i * 64);
            er_error_source_id = 8'h80;
            @(posedge clk);
        end
        er_error_valid = 0;
        
        repeat(5) @(posedge clk);
        
        if (er_log_full) begin
            $display("  PASS: Error log full flag set");
            test_pass_count++;
        end else begin
            $display("  FAIL: Error log full flag not set");
            test_fail_count++;
        end
        
        if (er_error_count == 64) begin
            $display("  PASS: Error count saturated at maximum (64)");
            test_pass_count++;
        end else begin
            $display("  FAIL: Error count incorrect (expected 64, got %0d)", er_error_count);
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 11: Timeout-Based Retransmission
        // =========================================================================
        $display("\n[TEST 11] Timeout-Based Retransmission");
        
        reset_system();
        
        // Send a flit without acknowledgment
        rc_tx_valid = 1;
        rc_tx_flit.req = pack_req_flit(
            REQ_READ_SHARED, 48'hD000, 12'h900, 8'h90, 8'h91,
            3'b110, 3'b000, 4'h0, 1'b0, 1'b0, 1'b1, 1'b0
        );
        rc_tx_vc_id = VC_REQ;
        rc_net_tx_ready = 1;
        
        @(posedge clk);
        rc_tx_valid = 0;
        rc_net_tx_ready = 1;
        
        // Wait for retry timeout (RETRY_TIMEOUT = 50)
        repeat(55) @(posedge clk);
        
        if (rc_retransmit_active) begin
            $display("  PASS: Timeout-based retransmission activated");
            test_pass_count++;
        end else begin
            $display("  FAIL: Timeout-based retransmission not activated");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test 12: Successful Acknowledgment Path
        // =========================================================================
        $display("\n[TEST 12] Successful Acknowledgment Path");
        
        reset_system();
        
        // Send a flit
        rc_tx_valid = 1;
        rc_tx_flit.req = pack_req_flit(
            REQ_READ_SHARED, 48'hE000, 12'hA00, 8'hA0, 8'hA1,
            3'b110, 3'b000, 4'h0, 1'b0, 1'b0, 1'b1, 1'b0
        );
        rc_tx_vc_id = VC_REQ;
        rc_net_tx_ready = 1;
        
        @(posedge clk);
        rc_tx_valid = 0;
        
        // Send acknowledgment quickly
        repeat(5) @(posedge clk);
        rc_ack_valid = 1;
        rc_ack_txn_id = 12'hA00;
        @(posedge clk);
        rc_ack_valid = 0;
        
        // Wait and verify no retransmission
        repeat(60) @(posedge clk);
        
        if (!rc_retransmit_active) begin
            $display("  PASS: No retransmission after acknowledgment");
            test_pass_count++;
        end else begin
            $display("  FAIL: Unexpected retransmission after acknowledgment");
            test_fail_count++;
        end
        
        // =========================================================================
        // Test Summary
        // =========================================================================
        repeat(20) @(posedge clk);
        
        $display("\n=============================================================================");
        $display("Test Summary");
        $display("=============================================================================");
        $display("Tests Passed: %0d", test_pass_count);
        $display("Tests Failed: %0d", test_fail_count);
        
        if (test_fail_count == 0) begin
            $display("\nALL TESTS PASSED!");
        end else begin
            $display("\nSOME TESTS FAILED!");
        end
        
        $display("=============================================================================\n");
        
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #100000;
        $display("ERROR: Simulation timeout!");
        $finish;
    end

endmodule : tb_error_handling
