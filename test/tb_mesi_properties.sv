// =============================================================================
// Property-Based Test for MESI State Machine Correctness
// Feature: coh-noc-architecture, Property 12: MESI 状态机正确性
// Validates: Requirements 4.6
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_mesi_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int ADDR_WIDTH = 48;
    parameter int NODE_ID_WIDTH = 8;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // Test result tracking
    string test_name;
    logic test_passed;
    
    // DUT signals
    logic clk;
    logic rst_n;
    
    // State Machine Control Interface
    logic                    req_valid;
    logic                    req_ready;
    logic [ADDR_WIDTH-1:0]   req_addr;
    coherency_event_e        req_event;
    logic [NODE_ID_WIDTH-1:0] req_node_id;
    directory_entry_t        current_state;
    
    // State Machine Response Interface
    logic                    rsp_valid;
    logic                    rsp_ready;
    directory_entry_t        new_state;
    coherency_action_t       required_actions;
    logic                    state_changed;
    
    // Snoop Generation Interface
    logic                    snoop_valid;
    logic                    snoop_ready;
    logic [ADDR_WIDTH-1:0]   snoop_addr;
    snp_opcode_e             snoop_opcode;
    logic [15:0]             snoop_targets;
    
    // Error and Debug Interface
    logic                    protocol_error;
    logic [7:0]              error_code;
    
    // Test variables
    directory_entry_t test_states [$];
    coherency_event_e test_events [$];
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    mesi_state_machine #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .NODE_ID_WIDTH(NODE_ID_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .req_valid(req_valid),
        .req_ready(req_ready),
        .req_addr(req_addr),
        .req_event(req_event),
        .req_node_id(req_node_id),
        .current_state(current_state),
        .rsp_valid(rsp_valid),
        .rsp_ready(rsp_ready),
        .new_state(new_state),
        .required_actions(required_actions),
        .state_changed(state_changed),
        .snoop_valid(snoop_valid),
        .snoop_ready(snoop_ready),
        .snoop_addr(snoop_addr),
        .snoop_opcode(snoop_opcode),
        .snoop_targets(snoop_targets),
        .protocol_error(protocol_error),
        .error_code(error_code)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 12: MESI State Machine Correctness
    // For any cache coherency state transition, the system should follow
    // MESI protocol state transition rules correctly
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: MESI State Machine Correctness");
        $display("Feature: coh-noc-architecture, Property 12");
        $display("Validates: Requirements 4.6");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        req_valid = 0;
        req_addr = 0;
        req_event = EVENT_CPU_READ;
        req_node_id = 0;
        current_state = init_directory_entry();
        rsp_ready = 1;
        snoop_ready = 1;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_invalid_state_transitions();
        test_shared_state_transitions();
        test_exclusive_state_transitions();
        test_modified_state_transitions();
        test_protocol_error_detection();
        
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
    // Test Invalid State Transitions - Requirement 4.6
    // Verify transitions from Invalid state follow MESI protocol
    // =============================================================================
    task test_invalid_state_transitions();
        directory_entry_t init_state;
        logic [NODE_ID_WIDTH-1:0] test_node;
        
        $display("Testing Invalid State Transitions - Requirement 4.6");
        $display("------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Invalid_State_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize to Invalid state
            init_state = init_directory_entry();
            init_state.state = DIR_INVALID;
            test_node = $urandom_range(0, 15);
            
            // Test CPU Read from Invalid -> Should go to Exclusive or Shared
            perform_state_transition(init_state, EVENT_CPU_READ, test_node);
            
            if (protocol_error) begin
                $display("  [FAIL] %s: Protocol error on CPU read from Invalid (error=0x%02x)", 
                         test_name, error_code);
                test_passed = 1'b0;
            end else if (!state_changed) begin
                $display("  [FAIL] %s: State didn't change on CPU read from Invalid", test_name);
                test_passed = 1'b0;
            end else if (new_state.state != DIR_EXCLUSIVE && new_state.state != DIR_SHARED) begin
                $display("  [FAIL] %s: Invalid transition I->%s on CPU read", 
                         test_name, directory_state_to_string(new_state.state));
                test_passed = 1'b0;
            end else if (!is_sharer(new_state, test_node)) begin
                $display("  [FAIL] %s: Node %0d not added as sharer", test_name, test_node);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: I->%s on CPU read by node %0d", 
                                    test_name, directory_state_to_string(new_state.state), test_node);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Invalid State Transitions: %0d/%0d tests passed\n", 
                 (NUM_ITERATIONS/4) - (fail_count - (test_count - NUM_ITERATIONS/4)), (NUM_ITERATIONS/4));
    endtask
    
    // =============================================================================
    // Test Shared State Transitions - Requirement 4.6
    // Verify transitions from Shared state follow MESI protocol
    // =============================================================================
    task test_shared_state_transitions();
        directory_entry_t init_state;
        logic [NODE_ID_WIDTH-1:0] test_node, other_node;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Shared State Transitions - Requirement 4.6");
        $display("-----------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Shared_State_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize to Shared state with multiple sharers
            init_state = init_directory_entry();
            init_state.state = DIR_SHARED;
            test_node = $urandom_range(0, 7);
            other_node = $urandom_range(8, 15);
            
            // Add both nodes as sharers
            init_state = add_sharer(init_state, test_node);
            init_state = add_sharer(init_state, other_node);
            
            // Test CPU Write from Shared -> Should go to Modified and invalidate others
            perform_state_transition(init_state, EVENT_CPU_WRITE, test_node);
            
            if (protocol_error) begin
                $display("  [FAIL] %s: Protocol error on CPU write from Shared (error=0x%02x)", 
                         test_name, error_code);
                test_passed = 1'b0;
            end else if (!state_changed) begin
                $display("  [FAIL] %s: State didn't change on CPU write from Shared", test_name);
                test_passed = 1'b0;
            end else if (new_state.state != DIR_MODIFIED) begin
                $display("  [FAIL] %s: Invalid transition S->%s on CPU write", 
                         test_name, directory_state_to_string(new_state.state));
                test_passed = 1'b0;
            end else if (new_state.owner_id != test_node) begin
                $display("  [FAIL] %s: Wrong owner after S->M transition (expected %0d, got %0d)", 
                         test_name, test_node, new_state.owner_id);
                test_passed = 1'b0;
            end else if (!required_actions.send_snoop_invalidate) begin
                $display("  [FAIL] %s: No snoop invalidate action for S->M transition", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: S->M on CPU write by node %0d", test_name, test_node);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Shared State Transitions: %0d/%0d tests passed\n", 
                 (NUM_ITERATIONS/4) - (fail_count - local_fail_start), (NUM_ITERATIONS/4));
    endtask
    
    // =============================================================================
    // Test Exclusive State Transitions - Requirement 4.6
    // Verify transitions from Exclusive state follow MESI protocol
    // =============================================================================
    task test_exclusive_state_transitions();
        directory_entry_t init_state;
        logic [NODE_ID_WIDTH-1:0] owner_node, other_node;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Exclusive State Transitions - Requirement 4.6");
        $display("--------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Exclusive_State_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize to Exclusive state
            init_state = init_directory_entry();
            init_state.state = DIR_EXCLUSIVE;
            owner_node = $urandom_range(0, 7);
            other_node = $urandom_range(8, 15);
            init_state.owner_id = owner_node;
            init_state = add_sharer(init_state, owner_node);
            
            // Test CPU Write by owner from Exclusive -> Should go to Modified
            perform_state_transition(init_state, EVENT_CPU_WRITE, owner_node);
            
            if (protocol_error) begin
                $display("  [FAIL] %s: Protocol error on owner CPU write from Exclusive (error=0x%02x)", 
                         test_name, error_code);
                test_passed = 1'b0;
            end else if (!state_changed) begin
                $display("  [FAIL] %s: State didn't change on owner CPU write from Exclusive", test_name);
                test_passed = 1'b0;
            end else if (new_state.state != DIR_MODIFIED) begin
                $display("  [FAIL] %s: Invalid transition E->%s on owner CPU write", 
                         test_name, directory_state_to_string(new_state.state));
                test_passed = 1'b0;
            end else if (new_state.owner_id != owner_node) begin
                $display("  [FAIL] %s: Owner changed after E->M transition", test_name);
                test_passed = 1'b0;
            end else if (!new_state.dirty) begin
                $display("  [FAIL] %s: Dirty bit not set after E->M transition", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: E->M on owner CPU write by node %0d", test_name, owner_node);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Exclusive State Transitions: %0d/%0d tests passed\n", 
                 (NUM_ITERATIONS/4) - (fail_count - local_fail_start), (NUM_ITERATIONS/4));
    endtask
    
    // =============================================================================
    // Test Modified State Transitions - Requirement 4.6
    // Verify transitions from Modified state follow MESI protocol
    // =============================================================================
    task test_modified_state_transitions();
        directory_entry_t init_state;
        logic [NODE_ID_WIDTH-1:0] owner_node, other_node;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Modified State Transitions - Requirement 4.6");
        $display("------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Modified_State_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize to Modified state
            init_state = init_directory_entry();
            init_state.state = DIR_MODIFIED;
            owner_node = $urandom_range(0, 7);
            other_node = $urandom_range(8, 15);
            init_state.owner_id = owner_node;
            init_state.dirty = 1'b1;
            init_state = add_sharer(init_state, owner_node);
            
            // Test CPU Read by other node from Modified -> Should go to Shared with writeback
            perform_state_transition(init_state, EVENT_CPU_READ, other_node);
            
            if (protocol_error) begin
                $display("  [FAIL] %s: Protocol error on other CPU read from Modified (error=0x%02x)", 
                         test_name, error_code);
                test_passed = 1'b0;
            end else if (!state_changed) begin
                $display("  [FAIL] %s: State didn't change on other CPU read from Modified", test_name);
                test_passed = 1'b0;
            end else if (new_state.state != DIR_SHARED) begin
                $display("  [FAIL] %s: Invalid transition M->%s on other CPU read", 
                         test_name, directory_state_to_string(new_state.state));
                test_passed = 1'b0;
            end else if (!is_sharer(new_state, other_node)) begin
                $display("  [FAIL] %s: New reader not added as sharer", test_name);
                test_passed = 1'b0;
            end else if (!required_actions.send_mem_write) begin
                $display("  [FAIL] %s: No memory write action for M->S transition", test_name);
                test_passed = 1'b0;
            end else if (new_state.dirty) begin
                $display("  [FAIL] %s: Dirty bit still set after M->S transition", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: M->S on other CPU read by node %0d", test_name, other_node);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Modified State Transitions: %0d/%0d tests passed\n", 
                 (NUM_ITERATIONS/4) - (fail_count - local_fail_start), (NUM_ITERATIONS/4));
    endtask
    
    // =============================================================================
    // Test Protocol Error Detection - Requirement 4.6
    // Verify that invalid operations are detected and reported
    // =============================================================================
    task test_protocol_error_detection();
        directory_entry_t init_state;
        logic [NODE_ID_WIDTH-1:0] wrong_node;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Protocol Error Detection - Requirement 4.6");
        $display("-----------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Protocol_Error_Test_%0d", i);
            test_passed = 1'b1;
            
            // Test invalid operation: non-owner trying to evict from Exclusive
            init_state = init_directory_entry();
            init_state.state = DIR_EXCLUSIVE;
            init_state.owner_id = 5;
            init_state = add_sharer(init_state, 5);
            wrong_node = 10;  // Different from owner
            
            perform_state_transition(init_state, EVENT_CPU_EVICT, wrong_node);
            
            if (!protocol_error) begin
                $display("  [FAIL] %s: No protocol error for non-owner evict from Exclusive", test_name);
                test_passed = 1'b0;
            end else if (error_code == 8'h00) begin
                $display("  [FAIL] %s: Protocol error without error code", test_name);
                test_passed = 1'b0;
            end else if (state_changed) begin
                $display("  [FAIL] %s: State changed despite protocol error", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: Protocol error detected for invalid operation (code=0x%02x)", 
                                    test_name, error_code);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Protocol Error Detection: %0d/%0d tests passed\n", 
                 (NUM_ITERATIONS/4) - (fail_count - local_fail_start), (NUM_ITERATIONS/4));
    endtask
    
    // =============================================================================
    // Helper Tasks and Functions
    // =============================================================================
    
    task perform_state_transition(
        input directory_entry_t init_state,
        input coherency_event_e event,
        input logic [NODE_ID_WIDTH-1:0] node_id
    );
        req_addr = generate_random_address();
        req_event = event;
        req_node_id = node_id;
        current_state = init_state;
        req_valid = 1'b1;
        
        // Wait for request to be accepted
        while (!req_ready) @(posedge clk);
        @(posedge clk);
        req_valid = 1'b0;
        
        // Wait for response
        while (!rsp_valid) @(posedge clk);
        @(posedge clk);
        
        // Response is automatically ready
    endtask
    
    function automatic logic [ADDR_WIDTH-1:0] generate_random_address();
        logic [ADDR_WIDTH-1:0] addr;
        addr = {$urandom(), $urandom()};
        // Align to cache line boundary
        addr[5:0] = 6'b000000;
        return addr;
    endfunction

endmodule