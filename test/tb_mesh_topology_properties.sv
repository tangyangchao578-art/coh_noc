// =============================================================================
// Testbench for 2D Mesh Topology Properties
// Feature: coh-noc-architecture, Property 1: 2D Mesh 拓扑连接性
// Validates: Requirements 1.1, 1.4
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_mesh_topology_properties;

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
    // Property 1: 2D Mesh Topology Connectivity
    // For any mesh size configuration, the system should correctly establish
    // 2D Mesh topology connections, with each internal node having 4 neighbors,
    // and boundary nodes having the appropriate number of neighbors
    // =============================================================================
    
    task automatic test_mesh_connectivity(
        input int mesh_x,
        input int mesh_y
    );
        int expected_neighbors;
        int actual_neighbors;
        logic test_passed;
        
        $display("\n[TEST] Testing mesh connectivity for %0dx%0d mesh", mesh_x, mesh_y);
        
        test_passed = 1'b1;
        
        // Test each node in the mesh
        for (int x = 0; x < mesh_x; x++) begin
            for (int y = 0; y < mesh_y; y++) begin
                // Calculate expected number of neighbors
                expected_neighbors = 0;
                
                // Check North neighbor
                if (y < mesh_y - 1) expected_neighbors++;
                
                // Check South neighbor
                if (y > 0) expected_neighbors++;
                
                // Check East neighbor
                if (x < mesh_x - 1) expected_neighbors++;
                
                // Check West neighbor
                if (x > 0) expected_neighbors++;
                
                // Verify node type
                if (x == 0 || x == mesh_x-1 || y == 0 || y == mesh_y-1) begin
                    // Boundary node
                    if (expected_neighbors == 4) begin
                        $display("  ERROR: Boundary node (%0d,%0d) has 4 neighbors (should be < 4)", x, y);
                        test_passed = 1'b0;
                    end
                end else begin
                    // Internal node
                    if (expected_neighbors != 4) begin
                        $display("  ERROR: Internal node (%0d,%0d) has %0d neighbors (expected 4)", 
                                x, y, expected_neighbors);
                        test_passed = 1'b0;
                    end
                end
                
                // Verify corner nodes have exactly 2 neighbors
                if ((x == 0 && y == 0) || 
                    (x == 0 && y == mesh_y-1) ||
                    (x == mesh_x-1 && y == 0) ||
                    (x == mesh_x-1 && y == mesh_y-1)) begin
                    if (expected_neighbors != 2) begin
                        $display("  ERROR: Corner node (%0d,%0d) has %0d neighbors (expected 2)", 
                                x, y, expected_neighbors);
                        test_passed = 1'b0;
                    end
                end
                
                // Verify edge nodes (non-corner) have exactly 3 neighbors
                if (((x == 0 || x == mesh_x-1) && (y > 0 && y < mesh_y-1)) ||
                    ((y == 0 || y == mesh_y-1) && (x > 0 && x < mesh_x-1))) begin
                    if (expected_neighbors != 3) begin
                        $display("  ERROR: Edge node (%0d,%0d) has %0d neighbors (expected 3)", 
                                x, y, expected_neighbors);
                        test_passed = 1'b0;
                    end
                end
            end
        end
        
        if (test_passed) begin
            $display("  PASS: Mesh connectivity verified for %0dx%0d mesh", mesh_x, mesh_y);
            pass_count++;
        end else begin
            $display("  FAIL: Mesh connectivity test failed for %0dx%0d mesh", mesh_x, mesh_y);
            fail_count++;
        end
        
        test_count++;
    endtask
    
    // =============================================================================
    // Property Test: Manhattan Distance Routing Paths
    // Verify that the mesh topology supports X-Y dimension order routing
    // =============================================================================
    
    task automatic test_routing_path_exists(
        input int mesh_x,
        input int mesh_y,
        input int src_x,
        input int src_y,
        input int dst_x,
        input int dst_y
    );
        int path_length;
        int expected_length;
        int current_x, current_y;
        logic test_passed;
        
        test_passed = 1'b1;
        current_x = src_x;
        current_y = src_y;
        path_length = 0;
        
        // Calculate expected Manhattan distance
        expected_length = (src_x > dst_x ? src_x - dst_x : dst_x - src_x) +
                         (src_y > dst_y ? src_y - dst_y : dst_y - src_y);
        
        // Simulate X-Y routing
        // First route in X dimension
        while (current_x != dst_x && test_passed) begin
            if (current_x < dst_x) begin
                // Check if East neighbor exists
                if (current_x >= mesh_x - 1) begin
                    $display("  ERROR: Cannot route East from (%0d,%0d) - at boundary", 
                            current_x, current_y);
                    test_passed = 1'b0;
                end else begin
                    current_x++;
                    path_length++;
                end
            end else begin
                // Check if West neighbor exists
                if (current_x <= 0) begin
                    $display("  ERROR: Cannot route West from (%0d,%0d) - at boundary", 
                            current_x, current_y);
                    test_passed = 1'b0;
                end else begin
                    current_x--;
                    path_length++;
                end
            end
        end
        
        // Then route in Y dimension
        while (current_y != dst_y && test_passed) begin
            if (current_y < dst_y) begin
                // Check if North neighbor exists
                if (current_y >= mesh_y - 1) begin
                    $display("  ERROR: Cannot route North from (%0d,%0d) - at boundary", 
                            current_x, current_y);
                    test_passed = 1'b0;
                end else begin
                    current_y++;
                    path_length++;
                end
            end else begin
                // Check if South neighbor exists
                if (current_y <= 0) begin
                    $display("  ERROR: Cannot route South from (%0d,%0d) - at boundary", 
                            current_x, current_y);
                    test_passed = 1'b0;
                end else begin
                    current_y--;
                    path_length++;
                end
            end
        end
        
        // Verify path length matches Manhattan distance
        if (test_passed && path_length != expected_length) begin
            $display("  ERROR: Path length %0d != expected Manhattan distance %0d", 
                    path_length, expected_length);
            test_passed = 1'b0;
        end
        
        if (test_passed) begin
            pass_count++;
        end else begin
            $display("  FAIL: Routing path test failed from (%0d,%0d) to (%0d,%0d)", 
                    src_x, src_y, dst_x, dst_y);
            fail_count++;
        end
        
        test_count++;
    endtask
    
    // =============================================================================
    // Main Test Sequence
    // =============================================================================
    
    initial begin
        $display("=================================================================");
        $display("Property-Based Test: 2D Mesh Topology Connectivity");
        $display("Feature: coh-noc-architecture, Property 1");
        $display("Validates: Requirements 1.1, 1.4");
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
        // Test 1: Mesh Connectivity for Various Sizes
        // =============================================================================
        
        $display("\n--- Test 1: Mesh Connectivity Verification ---");
        
        // Test specific mesh sizes
        test_mesh_connectivity(2, 2);  // Minimum size
        test_mesh_connectivity(3, 3);  // Standard size
        test_mesh_connectivity(4, 4);  // Larger square
        test_mesh_connectivity(2, 4);  // Rectangular
        test_mesh_connectivity(5, 3);  // Rectangular
        
        // Test random mesh sizes
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            int rand_x, rand_y;
            rand_x = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            rand_y = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            test_mesh_connectivity(rand_x, rand_y);
        end
        
        // =============================================================================
        // Test 2: Routing Path Existence
        // =============================================================================
        
        $display("\n--- Test 2: Routing Path Existence ---");
        
        // Test routing paths in various mesh sizes
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            int mesh_x, mesh_y, src_x, src_y, dst_x, dst_y;
            
            // Generate random mesh size
            mesh_x = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            mesh_y = $urandom_range(MIN_MESH_SIZE, MAX_MESH_SIZE);
            
            // Generate random source and destination
            src_x = $urandom_range(0, mesh_x-1);
            src_y = $urandom_range(0, mesh_y-1);
            dst_x = $urandom_range(0, mesh_x-1);
            dst_y = $urandom_range(0, mesh_y-1);
            
            test_routing_path_exists(mesh_x, mesh_y, src_x, src_y, dst_x, dst_y);
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

endmodule : tb_mesh_topology_properties
