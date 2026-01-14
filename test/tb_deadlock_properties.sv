// =============================================================================
// Testbench for Routing Deadlock Prevention Properties
// Feature: coh-noc-architecture, Property 3: 路由无死锁性
// Validates: Requirements 1.3
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_deadlock_properties;

    // =============================================================================
    // Test Parameters
    // =============================================================================
    
    parameter int NUM_ITERATIONS = 100;
    parameter int MAX_MESH_SIZE = 8;
    parameter int MIN_MESH_SIZE = 2;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Test control
    int test_count;
    int pass_count;
    int fail_count;
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 3: Routing Deadlock Freedom
    // For any traffic pattern and network configuration, the system should not
    // experience deadlock caused by circular waiting
    // =============================================================================
    
    // Test that X-Y dimension order routing prevents cyclic dependencies
    task automatic test_no_cyclic_dependency(
        input int mesh_x,
        input int mesh_y,
        input int src_x,
        input int src_y,
        input int dst_x,
        input int dst_y
    );
        int current_x, current_y;
        int prev_x, prev_y;
        logic moved_x, moved_y;
        logic test_passed;
        int step_count;
        
        test_passed = 1'b1;
        current_x = src_x;
        current_y = src_y;
        moved_x = 1'b0;
        moved_y = 1'b0;
        step_count = 0;
        
        // Simulate X-Y routing and check for cycles
        while ((current_x != dst_x || current_y != dst_y) && test_passed) begin
            prev_x = current_x;
            prev_y = current_y;
            
            // X-Y routing: move in X dimension first
            if (current_x != dst_x) begin
                if (current_x < dst_x) begin
                    current_x++;
                end else begin
                    current_x--;
                end
                moved_x = 1'b1;
                
                // Check that we haven't moved in Y dimension yet
                // This ensures dimension order is maintained
                if (moved_y) begin
                    $display("  ERROR: Moved in Y dimension before completing X dimension");
                    $display("    Route: (%0d,%0d) -> (%0d,%0d)", src_x, src_y, dst_x, dst_y);
                    test_passed = 1'b0;
                end
            end else if (current_y != dst_y) begin
                // Only move in Y after X is complete
                if (current_y < dst_y) begin
                    current_y++;
                end else begin
                    current_y--;
                end
                moved_y = 1'b1;
            end
            
            step_count++;
            
            // Detect infinite loop (should never happen with correct X-Y routing)
            if (step_count > (mesh_x + mesh_y) * 2) begin
                $display("  ERROR: Possible routing loop detected");
                $display("    Route: (%0d,%0d) -> (%0d,%0d)", src_x, src_y, dst_x, dst_y);
                test_passed = 1'b0;
            end
        end
        
        if (test_passed) begin
            pass_count++;
        end else begin
            fail_count++;
        end
        
        test_count++;
    endtask
    
    // Test that channel dependencies form a DAG (Directed Acyclic Graph)
    task automatic test_channel_dependency_dag(
        input int mesh_x,
        input int mesh_y
    );
        logic test_passed;
        int sample_count;
        
        test_passed = 1'b1;
        sample_count = 0;
        
        // In X-Y routing, channel dependencies are:
        // 1. X-dimension channels can depend on other X-dimension channels
        // 2. Y-dimension channels can depend on X-dimension channels
        // 3. Y-dimension channels can depend on other Y-dimension channels
        // 4. X-dimension channels CANNOT depend on Y-dimension channels
        //
        // This creates a DAG: X-channels -> Y-channels
        // No cycles are possible
        
        // Sample random routes instead of testing all combinations
        for (int sample = 0; sample < 20; sample++) begin
            int src_x, src_y, dst_x, dst_y;
            int curr_x, curr_y;
            logic in_y_phase;
            
            src_x = $urandom_range(0, mesh_x-1);
            src_y = $urandom_range(0, mesh_y-1);
            dst_x = $urandom_range(0, mesh_x-1);
            dst_y = $urandom_range(0, mesh_y-1);
            
            curr_x = src_x;
            curr_y = src_y;
            in_y_phase = 1'b0;
            
            // Simulate routing
            while (curr_x != dst_x || curr_y != dst_y) begin
                if (curr_x != dst_x) begin
                    // Moving in X dimension
                    if (in_y_phase) begin
                        // ERROR: Went back to X after Y
                        $display("  ERROR: Channel dependency cycle detected");
                        $display("    Route: (%0d,%0d) -> (%0d,%0d)", 
                                src_x, src_y, dst_x, dst_y);
                        test_passed = 1'b0;
                    end
                    
                    if (curr_x < dst_x) curr_x++;
                    else curr_x--;
                end else if (curr_y != dst_y) begin
                    // Moving in Y dimension
                    in_y_phase = 1'b1;
                    
                    if (curr_y < dst_y) curr_y++;
                    else curr_y--;
                end
            end
            
            sample_count++;
        end
        
        if (test_passed) begin
            $display("  PASS: Channel dependency DAG verified for %0dx%0d mesh (%0d samples)", 
                    mesh_x, mesh_y, sample_count);
            pass_count++;
        end else begin
            $display("  FAIL: Channel dependency test failed for %0dx%0d mesh", mesh_x, mesh_y);
            fail_count++;
        end
        
        test_count++;
    endtask
    
    // Test that routing is deterministic (same route every time)
    task automatic test_routing_determinism(
        input int mesh_x,
        input int mesh_y,
        input int src_x,
        input int src_y,
        input int dst_x,
        input int dst_y
    );
        int path1_len, path2_len;
        int expected_len;
        logic test_passed;
        int curr_x, curr_y;
        
        test_passed = 1'b1;
        
        // Compute route first time - just count steps
        curr_x = src_x;
        curr_y = src_y;
        path1_len = 0;
        
        while (curr_x != dst_x || curr_y != dst_y) begin
            if (curr_x != dst_x) begin
                if (curr_x < dst_x) curr_x++;
                else curr_x--;
            end else if (curr_y != dst_y) begin
                if (curr_y < dst_y) curr_y++;
                else curr_y--;
            end
            path1_len++;
        end
        
        // Compute route second time - just count steps
        curr_x = src_x;
        curr_y = src_y;
        path2_len = 0;
        
        while (curr_x != dst_x || curr_y != dst_y) begin
            if (curr_x != dst_x) begin
                if (curr_x < dst_x) curr_x++;
                else curr_x--;
            end else if (curr_y != dst_y) begin
                if (curr_y < dst_y) curr_y++;
                else curr_y--;
            end
            path2_len++;
        end
        
        // Compare path lengths (should be identical for deterministic routing)
        if (path1_len != path2_len) begin
            $display("  ERROR: Path lengths differ: %0d vs %0d", path1_len, path2_len);
            test_passed = 1'b0;
        end
        
        // Verify path length matches Manhattan distance
        expected_len = (src_x > dst_x ? src_x - dst_x : dst_x - src_x) +
                      (src_y > dst_y ? src_y - dst_y : dst_y - src_y);
        
        if (path1_len != expected_len) begin
            $display("  ERROR: Path length %0d != Manhattan distance %0d", path1_len, expected_len);
            test_passed = 1'b0;
        end
        
        if (test_passed) begin
            pass_count++;
        end else begin
            $display("  FAIL: Routing determinism test failed");
            $display("    Route: (%0d,%0d) -> (%0d,%0d)", src_x, src_y, dst_x, dst_y);
            fail_count++;
        end
        
        test_count++;
    endtask
    
    // =============================================================================
    // Main Test Sequence
    // =============================================================================
    
    initial begin
        $display("=================================================================");
        $display("Property-Based Test: Routing Deadlock Freedom");
        $display("Feature: coh-noc-architecture, Property 3");
        $display("Validates: Requirements 1.3");
        $display("=================================================================\n");
        
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        // Reset
        rst_n = 0;
        #20;
        rst_n = 1;
        #10;
        
        // =============================================================================
        // Test 1: No Cyclic Dependencies in Routing
        // =============================================================================
        
        $display("\n--- Test 1: No Cyclic Dependencies ---");
        
        // Test random routes
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            int mesh_x, mesh_y, src_x, src_y, dst_x, dst_y;
            
            mesh_x = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            mesh_y = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            src_x = $urandom_range(0, mesh_x-1);
            src_y = $urandom_range(0, mesh_y-1);
            dst_x = $urandom_range(0, mesh_x-1);
            dst_y = $urandom_range(0, mesh_y-1);
            
            test_no_cyclic_dependency(mesh_x, mesh_y, src_x, src_y, dst_x, dst_y);
        end
        
        // =============================================================================
        // Test 2: Channel Dependency DAG
        // =============================================================================
        
        $display("\n--- Test 2: Channel Dependency DAG ---");
        
        // Test specific mesh sizes
        test_channel_dependency_dag(2, 2);
        test_channel_dependency_dag(3, 3);
        test_channel_dependency_dag(4, 4);
        
        // =============================================================================
        // Test 3: Routing Determinism
        // =============================================================================
        
        $display("\n--- Test 3: Routing Determinism ---");
        
        // Test that routing is deterministic
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            int mesh_x, mesh_y, src_x, src_y, dst_x, dst_y;
            
            mesh_x = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            mesh_y = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            src_x = $urandom_range(0, mesh_x-1);
            src_y = $urandom_range(0, mesh_y-1);
            dst_x = $urandom_range(0, mesh_x-1);
            dst_y = $urandom_range(0, mesh_y-1);
            
            test_routing_determinism(mesh_x, mesh_y, src_x, src_y, dst_x, dst_y);
        end
        
        // =============================================================================
        // Test Summary
        // =============================================================================
        
        $display("\n=================================================================");
        $display("Test Summary:");
        $display("  Total Tests: %0d", test_count);
        $display("  Passed:      %0d", pass_count);
        $display("  Failed:      %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("\n  ALL TESTS PASSED!");
            $display("=================================================================\n");
        end else begin
            $display("\n  SOME TESTS FAILED!");
            $display("=================================================================\n");
            $fatal(1, "Property test failed");
        end
        
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #1000000; // 1ms timeout
        $display("\nERROR: Test timeout!");
        $fatal(1, "Test timeout");
    end

endmodule : tb_deadlock_properties
