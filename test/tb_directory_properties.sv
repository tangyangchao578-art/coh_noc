// =============================================================================
// Property-Based Test for Directory State Management
// Feature: coh-noc-architecture, Property 10: Directory 状态一致性
// Validates: Requirements 4.4, 7.1, 7.2, 7.3
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_directory_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // Test result tracking
    string test_name;
    logic test_passed;
    
    // Random variables
    logic [7:0] rand_node_id;
    directory_entry_t rand_entry;
    
    // =============================================================================
    // Property 10: Directory State Consistency
    // For any cache line operation, the Directory should accurately track
    // the cache line replica state across RN-F nodes
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: Directory State Consistency");
        $display("Feature: coh-noc-architecture, Property 10");
        $display("Validates: Requirements 4.4, 7.1, 7.2, 7.3");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("=============================================================================\n");
        
        // Run property tests
        test_directory_initialization();
        test_add_sharer_consistency();
        test_remove_sharer_consistency();
        test_write_transition_consistency();
        test_read_transition_consistency();
        test_invalidate_consistency();
        test_sharer_tracking();
        
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
    // Test Directory Initialization - Requirement 7.1
    // =============================================================================
    task test_directory_initialization();
        directory_entry_t entry;
        
        $display("Testing Directory Initialization - Requirement 7.1");
        $display("------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Dir_Init_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize directory entry
            entry = init_directory_entry();
            
            // Verify initial state
            if (entry.state !== DIR_INVALID) begin
                $display("  [FAIL] %s: Expected DIR_INVALID, got %s", test_name, entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            if (entry.sharer_mask !== 16'h0000) begin
                $display("  [FAIL] %s: Expected empty sharer_mask, got 0x%04h", test_name, entry.sharer_mask);
                test_passed = 1'b0;
            end
            
            if (entry.owner_id !== 8'h00) begin
                $display("  [FAIL] %s: Expected owner_id=0, got 0x%02h", test_name, entry.owner_id);
                test_passed = 1'b0;
            end
            
            if (entry.dirty !== 1'b0) begin
                $display("  [FAIL] %s: Expected dirty=0, got %b", test_name, entry.dirty);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Directory Init: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Add Sharer Consistency - Requirement 7.1, 7.2
    // =============================================================================
    task test_add_sharer_consistency();
        directory_entry_t entry, new_entry;
        int local_fail_start;
        logic [7:0] second_node;
        
        local_fail_start = fail_count;
        
        $display("Testing Add Sharer Consistency - Requirements 7.1, 7.2");
        $display("----------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Add_Sharer_Test_%0d", i);
            test_passed = 1'b1;
            
            // Start with invalid entry
            entry = init_directory_entry();
            
            // Add first sharer
            rand_node_id = $urandom_range(0, 15);
            new_entry = add_sharer(entry, rand_node_id);
            
            // Verify first sharer transitions to EXCLUSIVE
            if (new_entry.state !== DIR_EXCLUSIVE) begin
                $display("  [FAIL] %s: Expected DIR_EXCLUSIVE after first sharer, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            if (!((new_entry.sharer_mask >> rand_node_id) & 1'b1)) begin
                $display("  [FAIL] %s: Sharer bit not set for node %0d", test_name, rand_node_id);
                test_passed = 1'b0;
            end
            
            if (new_entry.owner_id !== rand_node_id) begin
                $display("  [FAIL] %s: Expected owner_id=%0d, got %0d", 
                         test_name, rand_node_id, new_entry.owner_id);
                test_passed = 1'b0;
            end
            
            // Add second sharer
            second_node = (rand_node_id + 1) % 16;
            entry = new_entry;
            new_entry = add_sharer(entry, second_node);
            
            // Verify transition to SHARED
            if (new_entry.state !== DIR_SHARED) begin
                $display("  [FAIL] %s: Expected DIR_SHARED after second sharer, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            if (!((new_entry.sharer_mask >> second_node) & 1'b1)) begin
                $display("  [FAIL] %s: Second sharer bit not set for node %0d", test_name, second_node);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Add Sharer: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Remove Sharer Consistency - Requirement 7.1, 7.2
    // =============================================================================
    task test_remove_sharer_consistency();
        directory_entry_t entry, new_entry;
        logic [7:0] node1, node2;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Remove Sharer Consistency - Requirements 7.1, 7.2");
        $display("-------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Remove_Sharer_Test_%0d", i);
            test_passed = 1'b1;
            
            // Create entry with two sharers
            entry = init_directory_entry();
            node1 = $urandom_range(0, 14);
            node2 = node1 + 1;
            
            entry = add_sharer(entry, node1);
            entry = add_sharer(entry, node2);
            
            // Should be in SHARED state
            if (entry.state !== DIR_SHARED) begin
                $display("  [FAIL] %s: Setup failed - expected DIR_SHARED", test_name);
                test_passed = 1'b0;
                fail_count++;
            end else begin
                // Remove one sharer
                new_entry = remove_sharer(entry, node2);
            
                // Should transition to EXCLUSIVE
                if (new_entry.state !== DIR_EXCLUSIVE) begin
                    $display("  [FAIL] %s: Expected DIR_EXCLUSIVE after removing one sharer, got %s", 
                             test_name, new_entry, directory_state_to_string(entry.state));
                    test_passed = 1'b0;
                end
                
                if ((new_entry.sharer_mask >> node2) & 1'b1) begin
                    $display("  [FAIL] %s: Removed sharer bit still set for node %0d", test_name, node2);
                    test_passed = 1'b0;
                end
                
                if (!((new_entry.sharer_mask >> node1) & 1'b1)) begin
                    $display("  [FAIL] %s: Remaining sharer bit cleared for node %0d", test_name, node1);
                    test_passed = 1'b0;
                end
                
                // Remove last sharer
                entry = new_entry;
                new_entry = remove_sharer(entry, node1);
                
                // Should transition to INVALID
                if (new_entry.state !== DIR_INVALID) begin
                    $display("  [FAIL] %s: Expected DIR_INVALID after removing last sharer, got %s", 
                             test_name, new_entry, directory_state_to_string(entry.state));
                    test_passed = 1'b0;
                end
                
                if (new_entry.sharer_mask !== 16'h0000) begin
                    $display("  [FAIL] %s: Expected empty sharer_mask, got 0x%04h", 
                             test_name, new_entry.sharer_mask);
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
        
        $display("  Remove Sharer: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Write Transition Consistency - Requirement 7.2, 7.3
    // =============================================================================
    task test_write_transition_consistency();
        directory_entry_t entry, new_entry;
        logic [7:0] writer_id;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Write Transition Consistency - Requirements 7.2, 7.3");
        $display("---------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Write_Transition_Test_%0d", i);
            test_passed = 1'b1;
            
            // Create entry with multiple sharers
            entry = init_directory_entry();
            for (int j = 0; j < 3; j++) begin
                entry = add_sharer(entry, j);
            end
            
            // Perform write transition
            writer_id = $urandom_range(0, 15);
            new_entry = directory_write_transition(entry, writer_id);
            
            // Verify transition to MODIFIED
            if (new_entry.state !== DIR_MODIFIED) begin
                $display("  [FAIL] %s: Expected DIR_MODIFIED, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            // Verify dirty bit is set
            if (!new_entry.dirty) begin
                $display("  [FAIL] %s: Expected dirty bit to be set", test_name);
                test_passed = 1'b0;
            end
            
            // Verify only writer is in sharer mask
            if (writer_id < 16) begin
                if (!((new_entry.sharer_mask >> writer_id) & 1'b1)) begin
                    $display("  [FAIL] %s: Writer not in sharer mask", test_name);
                    test_passed = 1'b0;
                end
                
                // Check no other sharers
                for (int j = 0; j < 16; j++) begin
                    if (j != writer_id && ((new_entry.sharer_mask >> j) & 1'b1)) begin
                        $display("  [FAIL] %s: Other sharers still present after write", test_name);
                        test_passed = 1'b0;
                        j = 16; // Exit loop
                    end
                end
            end
            
            // Verify owner is writer
            if (new_entry.owner_id !== writer_id) begin
                $display("  [FAIL] %s: Expected owner_id=%0d, got %0d", 
                         test_name, writer_id, new_entry.owner_id);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Write Transition: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Read Transition Consistency - Requirement 7.2
    // =============================================================================
    task test_read_transition_consistency();
        directory_entry_t entry, new_entry;
        logic [7:0] reader_id;
        logic [7:0] second_reader;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Read Transition Consistency - Requirement 7.2");
        $display("--------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Read_Transition_Test_%0d", i);
            test_passed = 1'b1;
            
            // Test read from INVALID state
            entry = init_directory_entry();
            reader_id = $urandom_range(0, 15);
            new_entry = directory_read_transition(entry, reader_id);
            
            if (new_entry.state !== DIR_EXCLUSIVE) begin
                $display("  [FAIL] %s: Expected DIR_EXCLUSIVE from INVALID, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            // Test read from EXCLUSIVE state
            entry = new_entry;
            second_reader = (reader_id + 1) % 16;
            new_entry = directory_read_transition(entry, second_reader);
            
            if (new_entry.state !== DIR_SHARED) begin
                $display("  [FAIL] %s: Expected DIR_SHARED from EXCLUSIVE, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            // Verify both readers are in sharer mask
            if (!((new_entry.sharer_mask >> reader_id) & 1'b1) || !((new_entry.sharer_mask >> second_reader) & 1'b1)) begin
                $display("  [FAIL] %s: Not all readers in sharer mask", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Read Transition: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Invalidate Consistency - Requirement 7.3
    // =============================================================================
    task test_invalidate_consistency();
        directory_entry_t entry, new_entry;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Invalidate Consistency - Requirement 7.3");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Invalidate_Test_%0d", i);
            test_passed = 1'b1;
            
            // Create entry with random state
            entry = init_directory_entry();
            for (int j = 0; j < $urandom_range(1, 5); j++) begin
                entry = add_sharer(entry, j);
            end
            
            // Invalidate all sharers
            new_entry = invalidate_all_sharers(entry);
            
            // Verify state is INVALID
            if (new_entry.state !== DIR_INVALID) begin
                $display("  [FAIL] %s: Expected DIR_INVALID, got %s", 
                         test_name, new_entry, directory_state_to_string(entry.state));
                test_passed = 1'b0;
            end
            
            // Verify sharer mask is clear
            if (new_entry.sharer_mask !== 16'h0000) begin
                $display("  [FAIL] %s: Expected empty sharer_mask, got 0x%04h", 
                         test_name, new_entry.sharer_mask);
                test_passed = 1'b0;
            end
            
            // Verify dirty bit is clear
            if (new_entry.dirty) begin
                $display("  [FAIL] %s: Expected dirty bit to be clear", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Invalidate: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Sharer Tracking - Requirement 7.1
    // =============================================================================
    task test_sharer_tracking();
        directory_entry_t entry;
        int expected_count;
        int actual_count;
        int local_fail_start;
        
        local_fail_start = fail_count;
        
        $display("Testing Sharer Tracking - Requirement 7.1");
        $display("---------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Sharer_Tracking_Test_%0d", i);
            test_passed = 1'b1;
            
            // Create entry with random number of sharers
            entry = init_directory_entry();
            expected_count = $urandom_range(0, 10);
            
            for (int j = 0; j < expected_count; j++) begin
                entry = add_sharer(entry, j);
            end
            
            // Verify sharer count
            actual_count = get_sharer_count(entry);
            if (actual_count !== expected_count) begin
                $display("  [FAIL] %s: Expected %0d sharers, got %0d", 
                         test_name, expected_count, actual_count);
                test_passed = 1'b0;
            end
            
            // Verify is_sharer function
            for (int j = 0; j < expected_count; j++) begin
                if (!is_sharer(entry, j)) begin
                    $display("  [FAIL] %s: Node %0d should be a sharer", test_name, j);
                    test_passed = 1'b0;
                end
            end
            
            // Verify non-sharers
            for (int j = expected_count; j < 16; j++) begin
                if (is_sharer(entry, j)) begin
                    $display("  [FAIL] %s: Node %0d should not be a sharer", test_name, j);
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
        
        $display("  Sharer Tracking: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask

endmodule
