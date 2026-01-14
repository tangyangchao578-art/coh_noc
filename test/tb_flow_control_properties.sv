// =============================================================================
// Property-Based Test for Credit Flow Control
// Feature: coh-noc-architecture, Property 6: 信用流控机制
// Feature: coh-noc-architecture, Property 8: 缓冲区背压机制
// Validates: Requirements 3.2, 8.1, 8.2, 8.4
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_flow_control_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int MAX_CREDITS = 16;
    parameter int NUM_VCS = 4;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // Test result tracking
    string test_name;
    logic test_passed;
    
    // DUT signals
    logic        clk;
    logic        rst_n;
    
    logic [CREDIT_COUNT_WIDTH-1:0] credit_count [0:NUM_VCS-1];
    logic [NUM_VCS-1:0]            credit_available;
    logic        consume_credit;
    logic [1:0]  consume_vc_id;
    logic        return_credit;
    logic [1:0]  return_vc_id;
    logic [NUM_VCS-1:0] backpressure;
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    credit_flow_control #(
        .MAX_CREDITS(MAX_CREDITS),
        .NUM_VCS(NUM_VCS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .credit_count(credit_count),
        .credit_available(credit_available),
        .consume_credit(consume_credit),
        .consume_vc_id(consume_vc_id),
        .return_credit(return_credit),
        .return_vc_id(return_vc_id),
        .backpressure(backpressure)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 6: Credit Flow Control Mechanism
    // Property 8: Buffer Backpressure Mechanism
    // For any network load situation, the system should correctly maintain
    // credit counts and prevent buffer overflow and underflow
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: Credit Flow Control and Backpressure");
        $display("Feature: coh-noc-architecture, Property 6 & 8");
        $display("Validates: Requirements 3.2, 8.1, 8.2, 8.4");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("Max Credits: %0d", MAX_CREDITS);
        $display("Number of VCs: %0d", NUM_VCS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        consume_credit = 0;
        return_credit = 0;
        consume_vc_id = 0;
        return_vc_id = 0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_credit_initialization();
        test_credit_consumption();
        test_credit_return();
        test_credit_bounds();
        test_backpressure_mechanism();
        test_concurrent_operations();
        
        // Print summary
        $display("\n=============================================================================");
        $display("Test Summary");
        $display("=============================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("=============================================================================\n");
        
        if (fail_count == 0) begin
            $display("*** ALL TESTS PASSED ***\n");
            $finish(0);
        end else begin
            $display("*** SOME TESTS FAILED ***\n");
            $finish(1);
        end
    end
    
    // =============================================================================
    // Test Credit Initialization - Requirement 8.1
    // =============================================================================
    task test_credit_initialization();
        $display("Testing Credit Initialization - Requirement 8.1");
        $display("--------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Credit_Init_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset the system
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            // Verify all VCs initialized with MAX_CREDITS
            for (int v = 0; v < NUM_VCS; v++) begin
                if (credit_count[v] != MAX_CREDITS) begin
                    $display("  [FAIL] %s: VC%0d credit count = %0d, expected %0d", 
                             test_name, v, credit_count[v], MAX_CREDITS);
                    test_passed = 1'b0;
                end
                
                if (!credit_available[v]) begin
                    $display("  [FAIL] %s: VC%0d credit not available after init", test_name, v);
                    test_passed = 1'b0;
                end
                
                if (backpressure[v]) begin
                    $display("  [FAIL] %s: VC%0d backpressure active after init", test_name, v);
                    test_passed = 1'b0;
                end
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Credit Init: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Credit Consumption - Requirement 8.1
    // =============================================================================
    task test_credit_consumption();
        int local_fail_start;
        int target_vc;
        logic [CREDIT_COUNT_WIDTH-1:0] initial_credit;
        
        local_fail_start = fail_count;
        
        $display("Testing Credit Consumption - Requirement 8.1");
        $display("-----------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Credit_Consume_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            // Select random VC
            target_vc = $urandom_range(0, NUM_VCS-1);
            initial_credit = credit_count[target_vc];
            
            // Consume a credit
            consume_vc_id = target_vc;
            consume_credit = 1;
            @(posedge clk);
            consume_credit = 0;
            @(posedge clk);
            
            // Verify credit decreased
            if (credit_count[target_vc] != initial_credit - 1) begin
                $display("  [FAIL] %s: VC%0d credit = %0d, expected %0d", 
                         test_name, target_vc, credit_count[target_vc], initial_credit - 1);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC%0d credit consumed", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Credit Consume: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Credit Return - Requirement 8.1
    // =============================================================================
    task test_credit_return();
        int local_fail_start;
        int target_vc;
        logic [CREDIT_COUNT_WIDTH-1:0] current_credit;
        
        local_fail_start = fail_count;
        
        $display("Testing Credit Return - Requirement 8.1");
        $display("------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Credit_Return_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            // Select random VC and consume some credits
            target_vc = $urandom_range(0, NUM_VCS-1);
            consume_vc_id = target_vc;
            
            // Consume 5 credits
            for (int c = 0; c < 5; c++) begin
                consume_credit = 1;
                @(posedge clk);
                consume_credit = 0;
            end
            @(posedge clk);
            
            current_credit = credit_count[target_vc];
            
            // Return a credit
            return_vc_id = target_vc;
            return_credit = 1;
            @(posedge clk);
            return_credit = 0;
            @(posedge clk);
            
            // Verify credit increased
            if (credit_count[target_vc] != current_credit + 1) begin
                $display("  [FAIL] %s: VC%0d credit = %0d, expected %0d", 
                         test_name, target_vc, credit_count[target_vc], current_credit + 1);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC%0d credit returned", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Credit Return: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Credit Bounds - Requirement 8.1, 8.2
    // =============================================================================
    task test_credit_bounds();
        int local_fail_start;
        int target_vc;
        
        local_fail_start = fail_count;
        
        $display("Testing Credit Bounds - Requirements 8.1, 8.2");
        $display("-------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Credit_Bounds_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            target_vc = $urandom_range(0, NUM_VCS-1);
            consume_vc_id = target_vc;
            
            // Consume all credits
            for (int c = 0; c < MAX_CREDITS; c++) begin
                consume_credit = 1;
                @(posedge clk);
                consume_credit = 0;
            end
            @(posedge clk);
            
            // Verify credit is 0
            if (credit_count[target_vc] != 0) begin
                $display("  [FAIL] %s: VC%0d credit = %0d after consuming all, expected 0", 
                         test_name, target_vc, credit_count[target_vc]);
                test_passed = 1'b0;
            end
            
            // Verify credit_available is false
            if (credit_available[target_vc]) begin
                $display("  [FAIL] %s: VC%0d credit_available should be false", test_name, target_vc);
                test_passed = 1'b0;
            end
            
            // Return all credits
            return_vc_id = target_vc;
            for (int c = 0; c < MAX_CREDITS; c++) begin
                return_credit = 1;
                @(posedge clk);
                return_credit = 0;
            end
            @(posedge clk);
            
            // Verify credit is MAX_CREDITS
            if (credit_count[target_vc] != MAX_CREDITS) begin
                $display("  [FAIL] %s: VC%0d credit = %0d after returning all, expected %0d", 
                         test_name, target_vc, credit_count[target_vc], MAX_CREDITS);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC%0d credit bounds maintained", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Credit Bounds: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Backpressure Mechanism - Requirement 8.2, 8.4
    // =============================================================================
    task test_backpressure_mechanism();
        int local_fail_start;
        int target_vc;
        
        local_fail_start = fail_count;
        
        $display("Testing Backpressure Mechanism - Requirements 8.2, 8.4");
        $display("----------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Backpressure_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            target_vc = $urandom_range(0, NUM_VCS-1);
            consume_vc_id = target_vc;
            
            // Consume all credits
            for (int c = 0; c < MAX_CREDITS; c++) begin
                consume_credit = 1;
                @(posedge clk);
                consume_credit = 0;
            end
            @(posedge clk);
            
            // Verify backpressure is active
            if (!backpressure[target_vc]) begin
                $display("  [FAIL] %s: VC%0d backpressure should be active when credits=0", test_name, target_vc);
                test_passed = 1'b0;
            end
            
            // Return one credit
            return_vc_id = target_vc;
            return_credit = 1;
            @(posedge clk);
            return_credit = 0;
            @(posedge clk);
            
            // Verify backpressure is inactive
            if (backpressure[target_vc]) begin
                $display("  [FAIL] %s: VC%0d backpressure should be inactive when credits>0", test_name, target_vc);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC%0d backpressure works correctly", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Backpressure: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Concurrent Operations - Requirement 8.1
    // =============================================================================
    task test_concurrent_operations();
        int local_fail_start;
        int target_vc;
        logic [CREDIT_COUNT_WIDTH-1:0] initial_credit;
        
        local_fail_start = fail_count;
        
        $display("Testing Concurrent Operations - Requirement 8.1");
        $display("--------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Concurrent_Op_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset
            rst_n = 0;
            @(posedge clk);
            rst_n = 1;
            @(posedge clk);
            
            target_vc = $urandom_range(0, NUM_VCS-1);
            
            // Consume some credits first
            consume_vc_id = target_vc;
            for (int c = 0; c < 5; c++) begin
                consume_credit = 1;
                @(posedge clk);
                consume_credit = 0;
            end
            @(posedge clk);
            
            initial_credit = credit_count[target_vc];
            
            // Concurrent consume and return (should cancel out)
            consume_vc_id = target_vc;
            return_vc_id = target_vc;
            consume_credit = 1;
            return_credit = 1;
            @(posedge clk);
            consume_credit = 0;
            return_credit = 0;
            @(posedge clk);
            
            // Verify credit unchanged
            if (credit_count[target_vc] != initial_credit) begin
                $display("  [FAIL] %s: VC%0d credit = %0d, expected %0d (concurrent ops should cancel)", 
                         test_name, target_vc, credit_count[target_vc], initial_credit);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC%0d concurrent ops handled correctly", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Concurrent Ops: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask

endmodule
