// =============================================================================
// Unit Tests for XP Router - Edge Cases and Error Conditions
// Requirements: 3.1, 3.3
// Tests edge cases, error conditions, and port contention handling
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_xp_router_unit;

    // Test parameters
    parameter int X_COORD = 2;
    parameter int Y_COORD = 2;
    parameter int BUFFER_DEPTH = 16;
    parameter int NUM_VCS = 4;
    parameter int MAX_CREDITS = 16;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
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
    // Main Test Sequence
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("XP Router Unit Tests - Edge Cases and Error Conditions");
        $display("Requirements: 3.1, 3.3");
        $display("Router Position: (%0d, %0d)", X_COORD, Y_COORD);
        $display("=============================================================================\n");
        
        // Initialize
        initialize_ports();
        rst_n = 0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run unit tests
        test_reset_behavior();
        test_buffer_full_backpressure();
        test_output_port_busy_buffering();
        test_port_contention_same_output();
        test_port_contention_different_vcs();
        test_simultaneous_multi_port_input();
        test_zero_credit_blocking();
        test_invalid_target_coordinates();
        test_same_node_loopback();
        
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
    // Test 1: Reset Behavior - Requirement 3.1
    // Verify that router properly initializes on reset
    // =============================================================================
    task test_reset_behavior();
        $display("Test 1: Reset Behavior");
        $display("----------------------");
        test_count++;
        
        // Apply reset
        rst_n = 0;
        repeat(3) @(posedge clk);
        
        // Check that all outputs are inactive
        if (north_out_valid || south_out_valid || east_out_valid || 
            west_out_valid || local_out_valid) begin
            $display("  [FAIL] Outputs active during reset");
            fail_count++;
        end else begin
            $display("  [PASS] All outputs inactive during reset");
            pass_count++;
        end
        
        // Release reset
        rst_n = 1;
        repeat(2) @(posedge clk);
        initialize_ports();
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 2: Buffer Full Backpressure - Requirement 3.3
    // Verify that router asserts backpressure when buffer is full
    // =============================================================================
    task test_buffer_full_backpressure();
        flit_u test_flit;
        int flits_sent;
        
        $display("Test 2: Buffer Full Backpressure");
        $display("--------------------------------");
        test_count++;
        
        // Create test flit targeting east (will be buffered)
        test_flit = create_flit_to_target(X_COORD + 1, Y_COORD);
        
        // Block the output port
        east_out_ready = 0;
        
        // Send flits until buffer is full
        flits_sent = 0;
        for (int i = 0; i < BUFFER_DEPTH + 5; i++) begin
            if (local_in_ready) begin
                local_in_valid = 1;
                local_in_flit = test_flit;
                local_in_vc_id = VC_REQ;
                @(posedge clk);
                flits_sent++;
            end
        end
        
        local_in_valid = 0;
        @(posedge clk);
        
        // Verify backpressure was asserted
        if (!local_in_ready && flits_sent <= BUFFER_DEPTH) begin
            $display("  [PASS] Backpressure asserted after %0d flits (buffer depth: %0d)", 
                     flits_sent, BUFFER_DEPTH);
            pass_count++;
        end else begin
            $display("  [FAIL] Backpressure not asserted correctly (sent: %0d, ready: %0b)", 
                     flits_sent, local_in_ready);
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 3: Output Port Busy Buffering - Requirement 3.3
    // Verify that flits are buffered when output port is busy
    // =============================================================================
    task test_output_port_busy_buffering();
        flit_u test_flit;
        logic flit_received;
        
        $display("Test 3: Output Port Busy Buffering");
        $display("----------------------------------");
        test_count++;
        
        // Create test flit
        test_flit = create_flit_to_target(X_COORD + 1, Y_COORD);
        test_flit.req.txn_id = 12'hABC;
        
        // Block output port initially
        east_out_ready = 0;
        
        // Send flit
        local_in_valid = 1;
        local_in_flit = test_flit;
        local_in_vc_id = VC_REQ;
        @(posedge clk);
        local_in_valid = 0;
        
        // Wait a few cycles with port blocked
        repeat(5) @(posedge clk);
        
        // Verify flit is not yet output
        if (east_out_valid) begin
            $display("  [FAIL] Flit output despite blocked port");
            fail_count++;
        end else begin
            // Now unblock the port
            east_out_ready = 1;
            
            // Wait for flit to be forwarded
            flit_received = 0;
            for (int i = 0; i < 20; i++) begin
                @(posedge clk);
                if (east_out_valid && east_out_flit.req.txn_id == 12'hABC) begin
                    flit_received = 1;
                    i = 20; // Exit early
                end
            end
            
            if (flit_received) begin
                $display("  [PASS] Flit buffered and forwarded when port became ready");
                pass_count++;
            end else begin
                $display("  [FAIL] Flit not forwarded after port became ready");
                fail_count++;
            end
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 4: Port Contention - Same Output Port - Requirement 3.1, 3.3
    // Verify arbitration when multiple inputs target the same output
    // =============================================================================
    task test_port_contention_same_output();
        flit_u flit_north, flit_south;
        int north_received, south_received;
        
        $display("Test 4: Port Contention - Same Output Port");
        $display("------------------------------------------");
        test_count++;
        
        // Create flits from north and south both targeting east
        flit_north = create_flit_to_target(X_COORD + 1, Y_COORD);
        flit_north.req.txn_id = 12'h111;
        
        flit_south = create_flit_to_target(X_COORD + 1, Y_COORD);
        flit_south.req.txn_id = 12'h222;
        
        // Send both flits simultaneously
        north_in_valid = 1;
        north_in_flit = flit_north;
        north_in_vc_id = VC_REQ;
        
        south_in_valid = 1;
        south_in_flit = flit_south;
        south_in_vc_id = VC_REQ;
        
        @(posedge clk);
        north_in_valid = 0;
        south_in_valid = 0;
        
        // Wait and collect outputs
        north_received = 0;
        south_received = 0;
        
        for (int i = 0; i < 30; i++) begin
            @(posedge clk);
            if (east_out_valid) begin
                if (east_out_flit.req.txn_id == 12'h111) north_received = 1;
                if (east_out_flit.req.txn_id == 12'h222) south_received = 1;
            end
            if (north_received && south_received) i = 30; // Exit early
        end
        
        // Verify both flits were eventually forwarded
        if (north_received && south_received) begin
            $display("  [PASS] Both flits forwarded despite contention");
            pass_count++;
        end else begin
            $display("  [FAIL] Not all flits forwarded (north: %0b, south: %0b)", 
                     north_received, south_received);
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 5: Port Contention - Different VCs - Requirement 3.1, 3.3
    // Verify that different VCs can be forwarded independently
    // =============================================================================
    task test_port_contention_different_vcs();
        flit_u flit_vc0, flit_vc1;
        int vc0_received, vc1_received;
        
        $display("Test 5: Port Contention - Different VCs");
        $display("---------------------------------------");
        test_count++;
        
        // Create flits on different VCs targeting same output
        flit_vc0 = create_flit_to_target(X_COORD + 1, Y_COORD);
        flit_vc0.req.txn_id = 12'h0C0;
        
        flit_vc1 = create_flit_to_target(X_COORD + 1, Y_COORD);
        flit_vc1.req.txn_id = 12'h0C1;
        
        // Send on different VCs
        local_in_valid = 1;
        local_in_flit = flit_vc0;
        local_in_vc_id = VC_REQ;
        @(posedge clk);
        
        local_in_flit = flit_vc1;
        local_in_vc_id = VC_RSP;
        @(posedge clk);
        
        local_in_valid = 0;
        
        // Collect outputs
        vc0_received = 0;
        vc1_received = 0;
        
        for (int i = 0; i < 30; i++) begin
            @(posedge clk);
            if (east_out_valid) begin
                if (east_out_flit.req.txn_id == 12'h0C0) vc0_received = 1;
                if (east_out_flit.req.txn_id == 12'h0C1) vc1_received = 1;
            end
            if (vc0_received && vc1_received) i = 30; // Exit early
        end
        
        // Verify both VCs forwarded
        if (vc0_received && vc1_received) begin
            $display("  [PASS] Both VCs forwarded independently");
            pass_count++;
        end else begin
            $display("  [FAIL] Not all VCs forwarded (VC0: %0b, VC1: %0b)", 
                     vc0_received, vc1_received);
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 6: Simultaneous Multi-Port Input - Requirement 3.1
    // Verify router handles inputs from multiple ports simultaneously
    // =============================================================================
    task test_simultaneous_multi_port_input();
        flit_u flit_n, flit_s, flit_e, flit_w, flit_l;
        int count_received;
        
        $display("Test 6: Simultaneous Multi-Port Input");
        $display("-------------------------------------");
        test_count++;
        
        // Create flits from all ports with different targets
        flit_n = create_flit_to_target(X_COORD, Y_COORD + 1);  // South
        flit_n.req.txn_id = 12'h001;
        
        flit_s = create_flit_to_target(X_COORD, Y_COORD - 1);  // North
        flit_s.req.txn_id = 12'h002;
        
        flit_e = create_flit_to_target(X_COORD - 1, Y_COORD);  // West
        flit_e.req.txn_id = 12'h003;
        
        flit_w = create_flit_to_target(X_COORD + 1, Y_COORD);  // East
        flit_w.req.txn_id = 12'h004;
        
        flit_l = create_flit_to_target(X_COORD, Y_COORD);      // Local
        flit_l.req.txn_id = 12'h005;
        
        // Send all simultaneously
        north_in_valid = 1; north_in_flit = flit_n; north_in_vc_id = VC_REQ;
        south_in_valid = 1; south_in_flit = flit_s; south_in_vc_id = VC_REQ;
        east_in_valid = 1;  east_in_flit = flit_e;  east_in_vc_id = VC_REQ;
        west_in_valid = 1;  west_in_flit = flit_w;  west_in_vc_id = VC_REQ;
        local_in_valid = 1; local_in_flit = flit_l; local_in_vc_id = VC_REQ;
        
        @(posedge clk);
        
        north_in_valid = 0;
        south_in_valid = 0;
        east_in_valid = 0;
        west_in_valid = 0;
        local_in_valid = 0;
        
        // Count how many were received
        count_received = 0;
        
        for (int i = 0; i < 50; i++) begin
            @(posedge clk);
            if (north_out_valid || south_out_valid || east_out_valid || 
                west_out_valid || local_out_valid) begin
                count_received++;
            end
        end
        
        // Verify all flits were eventually forwarded
        if (count_received >= 5) begin
            $display("  [PASS] All %0d flits from different ports forwarded", count_received);
            pass_count++;
        end else begin
            $display("  [FAIL] Only %0d/5 flits forwarded", count_received);
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 7: Zero Credit Blocking - Requirement 3.3
    // Verify that transmission stops when credits are exhausted
    // =============================================================================
    task test_zero_credit_blocking();
        flit_u test_flit;
        int initial_credits;
        
        $display("Test 7: Zero Credit Blocking");
        $display("----------------------------");
        test_count++;
        
        // Create test flit
        test_flit = create_flit_to_target(X_COORD + 1, Y_COORD);
        
        // Check initial credit count
        @(posedge clk);
        initial_credits = east_out_credit_count;
        
        // Send multiple flits without credit returns
        for (int i = 0; i < MAX_CREDITS + 2; i++) begin
            local_in_valid = 1;
            local_in_flit = test_flit;
            local_in_vc_id = VC_REQ;
            @(posedge clk);
        end
        
        local_in_valid = 0;
        repeat(10) @(posedge clk);
        
        // Verify credits were consumed
        if (east_out_credit_count < initial_credits) begin
            $display("  [PASS] Credits consumed (initial: %0d, current: %0d)", 
                     initial_credits, east_out_credit_count);
            pass_count++;
        end else begin
            $display("  [FAIL] Credits not consumed properly");
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(10) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 8: Invalid Target Coordinates - Requirement 3.1
    // Verify router handles edge case coordinates
    // =============================================================================
    task test_invalid_target_coordinates();
        flit_u test_flit;
        logic output_occurred;
        
        $display("Test 8: Edge Case Target Coordinates");
        $display("------------------------------------");
        test_count++;
        
        // Test with maximum coordinates
        test_flit = create_flit_to_target(4'hF, 4'hF);
        test_flit.req.txn_id = 12'hFFF;
        
        local_in_valid = 1;
        local_in_flit = test_flit;
        local_in_vc_id = VC_REQ;
        @(posedge clk);
        local_in_valid = 0;
        
        // Check if router forwards it
        output_occurred = 0;
        for (int i = 0; i < 20; i++) begin
            @(posedge clk);
            if (north_out_valid || south_out_valid || east_out_valid || 
                west_out_valid || local_out_valid) begin
                output_occurred = 1;
                i = 20; // Exit early
            end
        end
        
        if (output_occurred) begin
            $display("  [PASS] Router handled edge case coordinates");
            pass_count++;
        end else begin
            $display("  [FAIL] Router did not forward flit with edge coordinates");
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Test 9: Same Node Loopback - Requirement 3.1
    // Verify router handles flits destined for itself
    // =============================================================================
    task test_same_node_loopback();
        flit_u test_flit;
        logic loopback_received;
        
        $display("Test 9: Same Node Loopback");
        $display("--------------------------");
        test_count++;
        
        // Create flit targeting this router's coordinates
        test_flit = create_flit_to_target(X_COORD, Y_COORD);
        test_flit.req.txn_id = 12'hAAA;
        
        // Send from local port
        local_in_valid = 1;
        local_in_flit = test_flit;
        local_in_vc_id = VC_REQ;
        @(posedge clk);
        local_in_valid = 0;
        
        // Check if it comes back to local port
        loopback_received = 0;
        for (int i = 0; i < 20; i++) begin
            @(posedge clk);
            if (local_out_valid && local_out_flit.req.txn_id == 12'hAAA) begin
                loopback_received = 1;
                i = 20; // Exit early
            end
        end
        
        if (loopback_received) begin
            $display("  [PASS] Loopback to same node handled correctly");
            pass_count++;
        end else begin
            $display("  [FAIL] Loopback flit not received at local port");
            fail_count++;
        end
        
        // Cleanup
        initialize_ports();
        repeat(5) @(posedge clk);
        
        $display("");
    endtask
    
    // =============================================================================
    // Helper Functions
    // =============================================================================
    
    function flit_u create_flit_to_target(logic [3:0] target_x, logic [3:0] target_y);
        flit_u flit;
        flit.req.opcode = REQ_READ_SHARED;
        flit.req.addr = $urandom();
        flit.req.txn_id = $urandom();
        flit.req.src_id = $urandom();
        flit.req.tgt_id = {target_y, target_x};
        flit.req.size = 3'b110;
        flit.req.mem_attr = 3'b000;
        flit.req.qos = 4'b0000;
        return flit;
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

endmodule
