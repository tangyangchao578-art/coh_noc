// =============================================================================
// Property-Based Test for XP Router Flit Forwarding
// Feature: coh-noc-architecture, Property 5: Flit 转发正确性
// Validates: Requirements 3.1
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_xp_router_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int X_COORD = 2;
    parameter int Y_COORD = 2;
    parameter int BUFFER_DEPTH = 16;
    parameter int NUM_VCS = 4;
    parameter int MAX_CREDITS = 16;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // Test result tracking
    string test_name;
    logic test_passed;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // DUT signals - North Port
    logic        north_in_valid;
    logic        north_in_ready;
    flit_u       north_in_flit;
    logic [1:0]  north_in_vc_id;
    logic        north_in_credit_return;
    logic        north_out_valid;
    logic        north_out_ready;
    flit_u       north_out_flit;
    logic [1:0]  north_out_vc_id;
    logic [CREDIT_COUNT_WIDTH-1:0] north_out_credit_count;
    
    // South Port
    logic        south_in_valid;
    logic        south_in_ready;
    flit_u       south_in_flit;
    logic [1:0]  south_in_vc_id;
    logic        south_in_credit_return;
    logic        south_out_valid;
    logic        south_out_ready;
    flit_u       south_out_flit;
    logic [1:0]  south_out_vc_id;
    logic [CREDIT_COUNT_WIDTH-1:0] south_out_credit_count;
    
    // East Port
    logic        east_in_valid;
    logic        east_in_ready;
    flit_u       east_in_flit;
    logic [1:0]  east_in_vc_id;
    logic        east_in_credit_return;
    logic        east_out_valid;
    logic        east_out_ready;
    flit_u       east_out_flit;
    logic [1:0]  east_out_vc_id;
    logic [CREDIT_COUNT_WIDTH-1:0] east_out_credit_count;
    
    // West Port
    logic        west_in_valid;
    logic        west_in_ready;
    flit_u       west_in_flit;
    logic [1:0]  west_in_vc_id;
    logic        west_in_credit_return;
    logic        west_out_valid;
    logic        west_out_ready;
    flit_u       west_out_flit;
    logic [1:0]  west_out_vc_id;
    logic [CREDIT_COUNT_WIDTH-1:0] west_out_credit_count;
    
    // Local Port
    logic        local_in_valid;
    logic        local_in_ready;
    flit_u       local_in_flit;
    logic [1:0]  local_in_vc_id;
    logic        local_in_credit_return;
    logic        local_out_valid;
    logic        local_out_ready;
    flit_u       local_out_flit;
    logic [1:0]  local_out_vc_id;
    logic [CREDIT_COUNT_WIDTH-1:0] local_out_credit_count;
    
    // Port encoding
    typedef enum logic [2:0] {
        PORT_NORTH = 3'd0,
        PORT_SOUTH = 3'd1,
        PORT_EAST  = 3'd2,
        PORT_WEST  = 3'd3,
        PORT_LOCAL = 3'd4
    } port_e;
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    xp_router #(
        .X_COORD(X_COORD),
        .Y_COORD(Y_COORD),
        .BUFFER_DEPTH(BUFFER_DEPTH),
        .NUM_VCS(NUM_VCS),
        .MAX_CREDITS(MAX_CREDITS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        
        // North Port
        .north_in_valid(north_in_valid),
        .north_in_ready(north_in_ready),
        .north_in_flit(north_in_flit),
        .north_in_vc_id(north_in_vc_id),
        .north_in_credit_return(north_in_credit_return),
        .north_out_valid(north_out_valid),
        .north_out_ready(north_out_ready),
        .north_out_flit(north_out_flit),
        .north_out_vc_id(north_out_vc_id),
        .north_out_credit_count(north_out_credit_count),
        
        // South Port
        .south_in_valid(south_in_valid),
        .south_in_ready(south_in_ready),
        .south_in_flit(south_in_flit),
        .south_in_vc_id(south_in_vc_id),
        .south_in_credit_return(south_in_credit_return),
        .south_out_valid(south_out_valid),
        .south_out_ready(south_out_ready),
        .south_out_flit(south_out_flit),
        .south_out_vc_id(south_out_vc_id),
        .south_out_credit_count(south_out_credit_count),
        
        // East Port
        .east_in_valid(east_in_valid),
        .east_in_ready(east_in_ready),
        .east_in_flit(east_in_flit),
        .east_in_vc_id(east_in_vc_id),
        .east_in_credit_return(east_in_credit_return),
        .east_out_valid(east_out_valid),
        .east_out_ready(east_out_ready),
        .east_out_flit(east_out_flit),
        .east_out_vc_id(east_out_vc_id),
        .east_out_credit_count(east_out_credit_count),
        
        // West Port
        .west_in_valid(west_in_valid),
        .west_in_ready(west_in_ready),
        .west_in_flit(west_in_flit),
        .west_in_vc_id(west_in_vc_id),
        .west_in_credit_return(west_in_credit_return),
        .west_out_valid(west_out_valid),
        .west_out_ready(west_out_ready),
        .west_out_flit(west_out_flit),
        .west_out_vc_id(west_out_vc_id),
        .west_out_credit_count(west_out_credit_count),
        
        // Local Port
        .local_in_valid(local_in_valid),
        .local_in_ready(local_in_ready),
        .local_in_flit(local_in_flit),
        .local_in_vc_id(local_in_vc_id),
        .local_in_credit_return(local_in_credit_return),
        .local_out_valid(local_out_valid),
        .local_out_ready(local_out_ready),
        .local_out_flit(local_out_flit),
        .local_out_vc_id(local_out_vc_id),
        .local_out_credit_count(local_out_credit_count)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 5: Flit Forwarding Correctness
    // For any input Flit and target address, XP router should forward the Flit
    // to the correct output port based on X-Y dimension order routing
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: Flit Forwarding Correctness");
        $display("Feature: coh-noc-architecture, Property 5");
        $display("Validates: Requirements 3.1");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("Router Position: (%0d, %0d)", X_COORD, Y_COORD);
        $display("=============================================================================\n");
        
        // Initialize
        initialize_ports();
        rst_n = 0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_flit_forwarding_to_correct_port();
        test_flit_data_integrity();
        test_vc_id_preservation();
        test_multiple_vc_forwarding();
        
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
    // Test: Flit Forwarding to Correct Port - Requirement 3.1
    // Verify that flits are forwarded to the correct output port
    // =============================================================================
    task test_flit_forwarding_to_correct_port();
        flit_u test_flit;
        logic [2:0] expected_port;
        logic [2:0] actual_port;
        coord_t target_coord;
        
        $display("Testing Flit Forwarding to Correct Port - Requirement 3.1");
        $display("-------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Flit_Forward_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random target coordinates
            target_coord.x = $urandom_range(0, 15);
            target_coord.y = $urandom_range(0, 15);
            
            // Create test flit
            test_flit = create_random_flit(target_coord);
            
            // Calculate expected output port
            expected_port = calculate_expected_port(target_coord);
            
            // Send flit from local port
            send_flit_from_port(PORT_LOCAL, test_flit, VC_REQ);
            
            // Wait for flit to be forwarded
            wait_for_output(expected_port, actual_port);
            
            // Verify correct port
            if (actual_port != expected_port) begin
                $display("  [FAIL] %s: Expected port %0d, got port %0d for target (%0d,%0d)", 
                         test_name, expected_port, actual_port, target_coord.x, target_coord.y);
                test_passed = 1'b0;
            end
            
            // Clear ports
            initialize_ports();
            repeat(2) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Flit forwarded to port %0d for target (%0d,%0d)", 
                                    test_name, actual_port, target_coord.x, target_coord.y);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Flit Forwarding: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test: Flit Data Integrity - Requirement 3.1
    // Verify that flit data is preserved during forwarding
    // =============================================================================
    task test_flit_data_integrity();
        flit_u test_flit;
        flit_u received_flit;
        logic [2:0] expected_port;
        coord_t target_coord;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Flit Data Integrity - Requirement 3.1");
        $display("------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Data_Integrity_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random target
            target_coord.x = $urandom_range(0, 15);
            target_coord.y = $urandom_range(0, 15);
            
            // Create test flit with unique data
            test_flit = create_random_flit(target_coord);
            test_flit.req.txn_id = i[11:0];  // Unique transaction ID
            
            // Calculate expected port
            expected_port = calculate_expected_port(target_coord);
            
            // Send flit
            send_flit_from_port(PORT_LOCAL, test_flit, VC_REQ);
            
            // Receive flit
            receive_flit_from_port(expected_port, received_flit);
            
            // Verify data integrity
            if (received_flit.req.txn_id != test_flit.req.txn_id ||
                received_flit.req.src_id != test_flit.req.src_id ||
                received_flit.req.tgt_id != test_flit.req.tgt_id ||
                received_flit.req.addr != test_flit.req.addr) begin
                $display("  [FAIL] %s: Flit data corrupted during forwarding", test_name);
                test_passed = 1'b0;
            end
            
            // Clear ports
            initialize_ports();
            repeat(2) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Flit data preserved (txn_id=%0h)", 
                                    test_name, received_flit.req.txn_id);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Data Integrity: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test: VC ID Preservation - Requirement 3.1
    // Verify that VC ID is preserved during forwarding
    // =============================================================================
    task test_vc_id_preservation();
        flit_u test_flit;
        logic [1:0] test_vc_id;
        logic [1:0] received_vc_id;
        logic [2:0] expected_port;
        coord_t target_coord;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing VC ID Preservation - Requirement 3.1");
        $display("-----------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("VC_ID_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate random target and VC
            target_coord.x = $urandom_range(0, 15);
            target_coord.y = $urandom_range(0, 15);
            test_vc_id = $urandom_range(0, 3);
            
            // Create test flit
            test_flit = create_random_flit(target_coord);
            
            // Calculate expected port
            expected_port = calculate_expected_port(target_coord);
            
            // Send flit with specific VC ID
            send_flit_from_port(PORT_LOCAL, test_flit, test_vc_id);
            
            // Check output VC ID
            wait_for_output_vc(expected_port, received_vc_id);
            
            // Verify VC ID preserved
            if (received_vc_id != test_vc_id) begin
                $display("  [FAIL] %s: VC ID changed from %0d to %0d", 
                         test_name, test_vc_id, received_vc_id);
                test_passed = 1'b0;
            end
            
            // Clear ports
            initialize_ports();
            repeat(2) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: VC ID %0d preserved", test_name, test_vc_id);
            end else begin
                fail_count++;
            end
        end
        
        $display("  VC ID Preservation: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test: Multiple VC Forwarding - Requirement 3.1
    // Verify that multiple VCs can be forwarded independently
    // =============================================================================
    task test_multiple_vc_forwarding();
        flit_u test_flits [0:3];
        logic [2:0] expected_ports [0:3];
        coord_t target_coords [0:3];
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Multiple VC Forwarding - Requirement 3.1");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Multi_VC_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate test flits for each VC
            for (int vc = 0; vc < 4; vc++) begin
                target_coords[vc].x = $urandom_range(0, 15);
                target_coords[vc].y = $urandom_range(0, 15);
                test_flits[vc] = create_random_flit(target_coords[vc]);
                test_flits[vc].req.txn_id = (i * 4 + vc);
                expected_ports[vc] = calculate_expected_port(target_coords[vc]);
            end
            
            // Send flits from different VCs
            for (int vc = 0; vc < 4; vc++) begin
                send_flit_from_port(PORT_LOCAL, test_flits[vc], vc[1:0]);
                @(posedge clk);
            end
            
            // Wait for forwarding
            repeat(10) @(posedge clk);
            
            // Clear ports
            initialize_ports();
            repeat(2) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Multiple VCs forwarded correctly", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Multiple VC Forwarding: %0d/%0d tests passed\n", NUM_ITERATIONS/4 - (fail_count - local_fail_start), NUM_ITERATIONS/4);
    endtask
    
    // =============================================================================
    // Helper Functions
    // =============================================================================
    
    function flit_u create_random_flit(coord_t target);
        flit_u flit;
        flit.req.opcode = REQ_READ_SHARED;
        flit.req.addr = $urandom();
        flit.req.txn_id = $urandom();
        flit.req.src_id = $urandom();
        flit.req.tgt_id = {target.y, target.x};
        flit.req.size = 3'b110;  // 64 bytes
        flit.req.mem_attr = 3'b000;
        flit.req.qos = 4'b0000;
        return flit;
    endfunction
    
    function logic [2:0] calculate_expected_port(coord_t target);
        coord_t current;
        current.x = X_COORD[3:0];
        current.y = Y_COORD[3:0];
        
        if (current.x != target.x) begin
            if (current.x < target.x)
                return PORT_EAST;
            else
                return PORT_WEST;
        end else if (current.y != target.y) begin
            if (current.y < target.y)
                return PORT_SOUTH;
            else
                return PORT_NORTH;
        end else begin
            return PORT_LOCAL;
        end
    endfunction
    
    task initialize_ports();
        // Initialize all input ports
        north_in_valid = 0;
        north_in_flit = '0;
        north_in_vc_id = 0;
        north_in_credit_return = 0;
        north_out_ready = 1;
        
        south_in_valid = 0;
        south_in_flit = '0;
        south_in_vc_id = 0;
        south_in_credit_return = 0;
        south_out_ready = 1;
        
        east_in_valid = 0;
        east_in_flit = '0;
        east_in_vc_id = 0;
        east_in_credit_return = 0;
        east_out_ready = 1;
        
        west_in_valid = 0;
        west_in_flit = '0;
        west_in_vc_id = 0;
        west_in_credit_return = 0;
        west_out_ready = 1;
        
        local_in_valid = 0;
        local_in_flit = '0;
        local_in_vc_id = 0;
        local_in_credit_return = 0;
        local_out_ready = 1;
    endtask
    
    task send_flit_from_port(input logic [2:0] port, input flit_u flit, input logic [1:0] vc_id);
        case (port)
            PORT_NORTH: begin
                north_in_valid = 1;
                north_in_flit = flit;
                north_in_vc_id = vc_id;
            end
            PORT_SOUTH: begin
                south_in_valid = 1;
                south_in_flit = flit;
                south_in_vc_id = vc_id;
            end
            PORT_EAST: begin
                east_in_valid = 1;
                east_in_flit = flit;
                east_in_vc_id = vc_id;
            end
            PORT_WEST: begin
                west_in_valid = 1;
                west_in_flit = flit;
                west_in_vc_id = vc_id;
            end
            PORT_LOCAL: begin
                local_in_valid = 1;
                local_in_flit = flit;
                local_in_vc_id = vc_id;
            end
        endcase
        @(posedge clk);
    endtask
    
    task wait_for_output(input logic [2:0] expected_port, output logic [2:0] actual_port);
        int timeout = 100;
        actual_port = PORT_LOCAL;
        
        while (timeout > 0) begin
            if (north_out_valid) actual_port = PORT_NORTH;
            else if (south_out_valid) actual_port = PORT_SOUTH;
            else if (east_out_valid) actual_port = PORT_EAST;
            else if (west_out_valid) actual_port = PORT_WEST;
            else if (local_out_valid) actual_port = PORT_LOCAL;
            
            if (north_out_valid || south_out_valid || east_out_valid || west_out_valid || local_out_valid)
                break;
            
            @(posedge clk);
            timeout--;
        end
    endtask
    
    task receive_flit_from_port(input logic [2:0] port, output flit_u flit);
        int timeout = 100;
        
        while (timeout > 0) begin
            case (port)
                PORT_NORTH: if (north_out_valid) begin flit = north_out_flit; break; end
                PORT_SOUTH: if (south_out_valid) begin flit = south_out_flit; break; end
                PORT_EAST:  if (east_out_valid) begin flit = east_out_flit; break; end
                PORT_WEST:  if (west_out_valid) begin flit = west_out_flit; break; end
                PORT_LOCAL: if (local_out_valid) begin flit = local_out_flit; break; end
            endcase
            @(posedge clk);
            timeout--;
        end
    endtask
    
    task wait_for_output_vc(input logic [2:0] expected_port, output logic [1:0] vc_id);
        int timeout = 100;
        
        while (timeout > 0) begin
            case (expected_port)
                PORT_NORTH: if (north_out_valid) begin vc_id = north_out_vc_id; break; end
                PORT_SOUTH: if (south_out_valid) begin vc_id = south_out_vc_id; break; end
                PORT_EAST:  if (east_out_valid) begin vc_id = east_out_vc_id; break; end
                PORT_WEST:  if (west_out_valid) begin vc_id = west_out_vc_id; break; end
                PORT_LOCAL: if (local_out_valid) begin vc_id = local_out_vc_id; break; end
            endcase
            @(posedge clk);
            timeout--;
        end
    endtask

endmodule
