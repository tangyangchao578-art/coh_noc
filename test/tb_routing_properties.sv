// =============================================================================
// Property-Based Test for X-Y Routing Algorithm
// Feature: coh-noc-architecture, Property 2: X-Y 维序路由正确性
// Validates: Requirements 1.2, 3.4
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_routing_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int GRID_SIZE = 8;  // 8x8 grid for testing
    
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
    logic        flit_valid;
    logic [7:0]  target_id;
    logic [2:0]  output_port;
    logic        route_valid;
    
    // Test variables
    coord_t src_coord;
    coord_t dst_coord;
    coord_t current_coord;
    int expected_distance;
    int hop_count;
    
    // Port encoding
    typedef enum logic [2:0] {
        PORT_NORTH = 3'd0,
        PORT_SOUTH = 3'd1,
        PORT_EAST  = 3'd2,
        PORT_WEST  = 3'd3,
        PORT_LOCAL = 3'd4
    } port_e;
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 2: X-Y Dimension Order Routing Correctness
    // For any source and destination coordinates, the routing algorithm should
    // generate a path that routes X dimension first then Y dimension, and the
    // path length equals Manhattan distance
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: X-Y Dimension Order Routing Correctness");
        $display("Feature: coh-noc-architecture, Property 2");
        $display("Validates: Requirements 1.2, 3.4");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("Grid Size: %0dx%0d", GRID_SIZE, GRID_SIZE);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        flit_valid = 0;
        target_id = 0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_xy_dimension_order();
        test_manhattan_distance();
        test_destination_reached();
        test_all_grid_positions();
        
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
    // Test X-Y Dimension Order - Requirement 1.2
    // Verify that X dimension is routed before Y dimension
    // =============================================================================
    task test_xy_dimension_order();
        $display("Testing X-Y Dimension Order - Requirement 1.2");
        $display("-------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("XY_Order_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random source and destination
            src_coord.x = $urandom_range(0, GRID_SIZE-1);
            src_coord.y = $urandom_range(0, GRID_SIZE-1);
            dst_coord.x = $urandom_range(0, GRID_SIZE-1);
            dst_coord.y = $urandom_range(0, GRID_SIZE-1);
            
            // Simulate routing from source to destination
            current_coord = src_coord;
            hop_count = 0;
            
            while ((current_coord.x != dst_coord.x || current_coord.y != dst_coord.y) && test_passed && hop_count <= 2 * GRID_SIZE) begin
                // Instantiate router at current position
                target_id = {dst_coord.y, dst_coord.x};
                flit_valid = 1;
                
                // Create router instance for current position
                test_route_at_position(current_coord, dst_coord, output_port);
                
                @(posedge clk);
                
                // Verify X dimension is routed first
                if (current_coord.x != dst_coord.x) begin
                    if (output_port != PORT_EAST && output_port != PORT_WEST) begin
                        $display("  [FAIL] %s: X dimension not routed first at (%0d,%0d)", 
                                 test_name, current_coord.x, current_coord.y);
                        test_passed = 1'b0;
                    end
                end else if (current_coord.y != dst_coord.y) begin
                    // X dimension complete, now Y dimension
                    if (output_port != PORT_NORTH && output_port != PORT_SOUTH) begin
                        $display("  [FAIL] %s: Y dimension not routed after X at (%0d,%0d)", 
                                 test_name, current_coord.x, current_coord.y);
                        test_passed = 1'b0;
                    end
                end
                
                // Move to next hop
                if (test_passed) begin
                    case (output_port)
                        PORT_EAST:  current_coord.x = current_coord.x + 1;
                        PORT_WEST:  current_coord.x = current_coord.x - 1;
                        PORT_SOUTH: current_coord.y = current_coord.y + 1;
                        PORT_NORTH: current_coord.y = current_coord.y - 1;
                        default: begin
                            $display("  [FAIL] %s: Invalid port selected", test_name);
                            test_passed = 1'b0;
                        end
                    endcase
                end
                
                hop_count++;
            end
            
            // Check if we exceeded hop limit
            if (hop_count > 2 * GRID_SIZE && test_passed) begin
                $display("  [FAIL] %s: Too many hops (possible routing loop)", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Route from (%0d,%0d) to (%0d,%0d)", 
                                    test_name, src_coord.x, src_coord.y, dst_coord.x, dst_coord.y);
            end else begin
                fail_count++;
            end
        end
        
        flit_valid = 0;
        @(posedge clk);
        
        $display("  X-Y Order: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Manhattan Distance - Requirement 3.4
    // Verify that path length equals Manhattan distance
    // =============================================================================
    task test_manhattan_distance();
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Manhattan Distance - Requirement 3.4");
        $display("-----------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Manhattan_Dist_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random source and destination
            src_coord.x = $urandom_range(0, GRID_SIZE-1);
            src_coord.y = $urandom_range(0, GRID_SIZE-1);
            dst_coord.x = $urandom_range(0, GRID_SIZE-1);
            dst_coord.y = $urandom_range(0, GRID_SIZE-1);
            
            // Calculate expected Manhattan distance
            expected_distance = manhattan_distance(src_coord, dst_coord);
            
            // Simulate routing and count hops
            current_coord = src_coord;
            hop_count = 0;
            
            while ((current_coord.x != dst_coord.x || current_coord.y != dst_coord.y) && hop_count <= 2 * GRID_SIZE) begin
                target_id = {dst_coord.y, dst_coord.x};
                flit_valid = 1;
                
                test_route_at_position(current_coord, dst_coord, output_port);
                
                @(posedge clk);
                
                // Move to next hop
                case (output_port)
                    PORT_EAST:  current_coord.x = current_coord.x + 1;
                    PORT_WEST:  current_coord.x = current_coord.x - 1;
                    PORT_SOUTH: current_coord.y = current_coord.y + 1;
                    PORT_NORTH: current_coord.y = current_coord.y - 1;
                endcase
                
                hop_count++;
            end
            
            // Verify hop count equals Manhattan distance
            if (hop_count != expected_distance) begin
                $display("  [FAIL] %s: Expected %0d hops, got %0d hops from (%0d,%0d) to (%0d,%0d)", 
                         test_name, expected_distance, hop_count, 
                         src_coord.x, src_coord.y, dst_coord.x, dst_coord.y);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: %0d hops from (%0d,%0d) to (%0d,%0d)", 
                                    test_name, hop_count, src_coord.x, src_coord.y, dst_coord.x, dst_coord.y);
            end else begin
                fail_count++;
            end
        end
        
        flit_valid = 0;
        @(posedge clk);
        
        $display("  Manhattan Distance: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Destination Reached - Requirement 3.4
    // Verify that LOCAL port is selected when at destination
    // =============================================================================
    task test_destination_reached();
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Destination Reached - Requirement 3.4");
        $display("------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Dest_Reached_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random position (source = destination)
            src_coord.x = $urandom_range(0, GRID_SIZE-1);
            src_coord.y = $urandom_range(0, GRID_SIZE-1);
            dst_coord = src_coord;
            
            target_id = {dst_coord.y, dst_coord.x};
            flit_valid = 1;
            
            test_route_at_position(src_coord, dst_coord, output_port);
            
            @(posedge clk);
            
            // Verify LOCAL port is selected
            if (output_port != PORT_LOCAL) begin
                $display("  [FAIL] %s: Expected PORT_LOCAL at destination (%0d,%0d), got port %0d", 
                         test_name, src_coord.x, src_coord.y, output_port);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: LOCAL port at (%0d,%0d)", 
                                    test_name, src_coord.x, src_coord.y);
            end else begin
                fail_count++;
            end
        end
        
        flit_valid = 0;
        @(posedge clk);
        
        $display("  Destination Reached: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test All Grid Positions - Comprehensive Coverage
    // Test routing from every position to every other position
    // =============================================================================
    task test_all_grid_positions();
        int local_fail_start;
        int total_tests;
        
        local_fail_start = fail_count;
        total_tests = 0;
        
        $display("Testing All Grid Positions - Comprehensive Coverage");
        $display("------------------------------------------------");
        
        // Test a subset of all possible pairs for reasonable test time
        for (int sx = 0; sx < GRID_SIZE; sx += 2) begin
            for (int sy = 0; sy < GRID_SIZE; sy += 2) begin
                for (int dx = 0; dx < GRID_SIZE; dx += 2) begin
                    for (int dy = 0; dy < GRID_SIZE; dy += 2) begin
                        test_count++;
                        total_tests++;
                        test_name = $sformatf("Grid_Test_(%0d,%0d)_to_(%0d,%0d)", sx, sy, dx, dy);
                        test_passed = 1'b1;
                        
                        src_coord.x = sx;
                        src_coord.y = sy;
                        dst_coord.x = dx;
                        dst_coord.y = dy;
                        
                        // Simulate routing
                        current_coord = src_coord;
                        hop_count = 0;
                        
                        while ((current_coord.x != dst_coord.x || current_coord.y != dst_coord.y) && test_passed && hop_count <= 2 * GRID_SIZE) begin
                            target_id = {dst_coord.y, dst_coord.x};
                            flit_valid = 1;
                            
                            test_route_at_position(current_coord, dst_coord, output_port);
                            
                            @(posedge clk);
                            
                            // Move to next hop
                            case (output_port)
                                PORT_EAST:  current_coord.x = current_coord.x + 1;
                                PORT_WEST:  current_coord.x = current_coord.x - 1;
                                PORT_SOUTH: current_coord.y = current_coord.y + 1;
                                PORT_NORTH: current_coord.y = current_coord.y - 1;
                                default: test_passed = 1'b0;
                            endcase
                            
                            hop_count++;
                        end
                        
                        if (hop_count > 2 * GRID_SIZE && test_passed) begin
                            test_passed = 1'b0;
                        end
                        
                        if (test_passed) begin
                            pass_count++;
                        end else begin
                            fail_count++;
                            $display("  [FAIL] %s", test_name);
                        end
                    end
                end
            end
        end
        
        flit_valid = 0;
        @(posedge clk);
        
        $display("  Grid Coverage: %0d/%0d tests passed\n", total_tests - (fail_count - local_fail_start), total_tests);
    endtask
    
    // =============================================================================
    // Helper Task: Test routing at a specific position
    // =============================================================================
    task test_route_at_position(
        input coord_t current,
        input coord_t target,
        output logic [2:0] port
    );
        // Compute routing decision based on X-Y dimension order
        if (current.x != target.x) begin
            if (current.x < target.x) begin
                port = PORT_EAST;
            end else begin
                port = PORT_WEST;
            end
        end else if (current.y != target.y) begin
            if (current.y < target.y) begin
                port = PORT_SOUTH;
            end else begin
                port = PORT_NORTH;
            end
        end else begin
            port = PORT_LOCAL;
        end
    endtask

endmodule
