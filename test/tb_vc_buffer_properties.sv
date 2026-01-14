// =============================================================================
// Property-Based Test for Virtual Channel Buffer Isolation
// Feature: coh-noc-architecture, Property 7: 虚拟通道隔离性
// Validates: Requirements 3.5, 8.3
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_vc_buffer_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int BUFFER_DEPTH = 16;
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
    
    // Write interface
    logic        wr_en;
    logic [1:0]  wr_vc_id;
    flit_u       wr_data;
    logic [3:0]  vc_full;
    logic [3:0]  vc_almost_full;
    
    // Read interface
    logic        rd_en;
    logic [1:0]  rd_vc_id;
    flit_u       rd_data;
    logic [3:0]  vc_empty;
    logic [3:0]  vc_almost_empty;
    
    // Status signals
    logic [7:0]  vc_count [0:NUM_VCS-1];
    logic [7:0]  vc_free_slots [0:NUM_VCS-1];
    
    // Test variables
    logic [11:0] test_txn_ids [0:NUM_VCS-1][0:BUFFER_DEPTH-1];  // Store txn_ids for verification
    int vc_write_count [0:NUM_VCS-1];
    int vc_read_count [0:NUM_VCS-1];
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    vc_buffer_manager #(
        .BUFFER_DEPTH(BUFFER_DEPTH),
        .NUM_VCS(NUM_VCS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_vc_id(wr_vc_id),
        .wr_data(wr_data),
        .vc_full(vc_full),
        .vc_almost_full(vc_almost_full),
        .rd_en(rd_en),
        .rd_vc_id(rd_vc_id),
        .rd_data(rd_data),
        .vc_empty(vc_empty),
        .vc_almost_empty(vc_almost_empty),
        .vc_count(vc_count),
        .vc_free_slots(vc_free_slots)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 7: Virtual Channel Isolation
    // For any combination of virtual channels, data in different VCs should be
    // processed in independent buffers and not interfere with each other
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: Virtual Channel Isolation");
        $display("Feature: coh-noc-architecture, Property 7");
        $display("Validates: Requirements 3.5, 8.3");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("Buffer Depth: %0d", BUFFER_DEPTH);
        $display("Number of VCs: %0d", NUM_VCS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        wr_en = 0;
        rd_en = 0;
        wr_vc_id = 0;
        rd_vc_id = 0;
        wr_data = '0;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_vc_independence();
        test_vc_fifo_order();
        test_vc_concurrent_access();
        test_vc_buffer_full_isolation();
        
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
    // Test VC Independence - Requirement 3.5
    // Verify that writing to one VC doesn't affect other VCs
    // =============================================================================
    task test_vc_independence();
        logic [7:0] initial_counts [0:NUM_VCS-1];
        int target_vc;
        
        $display("Testing VC Independence - Requirement 3.5");
        $display("---------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("VC_Independence_Test_%0d", i);
            test_passed = 1'b1;
            
            // Record initial counts
            for (int v = 0; v < NUM_VCS; v++) begin
                initial_counts[v] = vc_count[v];
            end
            
            // Write to a random VC
            target_vc = $urandom_range(0, NUM_VCS-1);
            wr_vc_id = target_vc;
            wr_data = generate_random_flit(target_vc);
            wr_en = 1;
            
            @(posedge clk);
            wr_en = 0;
            @(posedge clk);
            
            // Verify only target VC count increased
            for (int v = 0; v < NUM_VCS; v++) begin
                if (v == target_vc) begin
                    if (vc_count[v] != initial_counts[v] + 1 && !vc_full[v]) begin
                        $display("  [FAIL] %s: VC%0d count didn't increase (expected %0d, got %0d)", 
                                 test_name, v, initial_counts[v] + 1, vc_count[v]);
                        test_passed = 1'b0;
                    end
                end else begin
                    if (vc_count[v] != initial_counts[v]) begin
                        $display("  [FAIL] %s: VC%0d count changed (expected %0d, got %0d)", 
                                 test_name, v, initial_counts[v], vc_count[v]);
                        test_passed = 1'b0;
                    end
                end
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Write to VC%0d isolated", test_name, target_vc);
            end else begin
                fail_count++;
            end
        end
        
        // Clear all buffers
        clear_all_buffers();
        
        $display("  VC Independence: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test VC FIFO Order - Requirement 3.5
    // Verify that each VC maintains FIFO order independently
    // =============================================================================
    task test_vc_fifo_order();
        int local_fail_start;
        int num_writes;
        logic [11:0] expected_txn_id;
        int write_idx [0:NUM_VCS-1];
        int read_idx [0:NUM_VCS-1];
        
        local_fail_start = fail_count;
        
        $display("Testing VC FIFO Order - Requirement 3.5");
        $display("-------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("VC_FIFO_Order_Test_%0d", i);
            test_passed = 1'b1;
            
            // Initialize indices
            for (int v = 0; v < NUM_VCS; v++) begin
                write_idx[v] = 0;
                read_idx[v] = 0;
            end
            
            // Write random number of flits to each VC
            for (int v = 0; v < NUM_VCS; v++) begin
                num_writes = $urandom_range(1, 8);
                
                for (int w = 0; w < num_writes; w++) begin
                    wr_vc_id = v;
                    wr_data = generate_random_flit(v);
                    test_txn_ids[v][write_idx[v]] = wr_data.req.txn_id;
                    write_idx[v]++;
                    wr_en = 1;
                    
                    @(posedge clk);
                    wr_en = 0;
                end
            end
            
            @(posedge clk);
            
            // Read back and verify FIFO order for each VC
            for (int v = 0; v < NUM_VCS; v++) begin
                while (read_idx[v] < write_idx[v]) begin
                    expected_txn_id = test_txn_ids[v][read_idx[v]];
                    read_idx[v]++;
                    
                    rd_vc_id = v;
                    rd_en = 1;
                    
                    @(posedge clk);
                    rd_en = 0;
                    
                    // Compare read data with expected
                    if (rd_data.req.txn_id != expected_txn_id) begin
                        $display("  [FAIL] %s: VC%0d FIFO order violated (expected txn_id=0x%03x, got 0x%03x)", 
                                 test_name, v, expected_txn_id, rd_data.req.txn_id);
                        test_passed = 1'b0;
                    end
                end
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: All VCs maintain FIFO order", test_name);
            end else begin
                fail_count++;
            end
        end
        
        // Clear all buffers
        clear_all_buffers();
        
        $display("  VC FIFO Order: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test VC Concurrent Access - Requirement 8.3
    // Verify that different VCs can be accessed concurrently
    // =============================================================================
    task test_vc_concurrent_access();
        int local_fail_start;
        int wr_vc, rd_vc;
        logic [7:0] wr_count_before, rd_count_before;
        
        local_fail_start = fail_count;
        
        $display("Testing VC Concurrent Access - Requirement 8.3");
        $display("--------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("VC_Concurrent_Test_%0d", i);
            test_passed = 1'b1;
            
            // Select different VCs for write and read
            wr_vc = $urandom_range(0, NUM_VCS-1);
            rd_vc = (wr_vc + 1) % NUM_VCS;
            
            // Ensure read VC has data
            if (vc_empty[rd_vc]) begin
                wr_vc_id = rd_vc;
                wr_data = generate_random_flit(rd_vc);
                wr_en = 1;
                @(posedge clk);
                wr_en = 0;
                @(posedge clk);
            end
            
            // Record counts before concurrent access
            wr_count_before = vc_count[wr_vc];
            rd_count_before = vc_count[rd_vc];
            
            // Perform concurrent write and read to different VCs
            wr_vc_id = wr_vc;
            rd_vc_id = rd_vc;
            wr_data = generate_random_flit(wr_vc);
            wr_en = 1;
            rd_en = 1;
            
            @(posedge clk);
            wr_en = 0;
            rd_en = 0;
            @(posedge clk);
            
            // Verify both operations completed
            if (!vc_full[wr_vc] && vc_count[wr_vc] != wr_count_before + 1) begin
                $display("  [FAIL] %s: VC%0d write failed during concurrent access", test_name, wr_vc);
                test_passed = 1'b0;
            end
            
            if (vc_count[rd_vc] != rd_count_before - 1) begin
                $display("  [FAIL] %s: VC%0d read failed during concurrent access", test_name, rd_vc);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Concurrent access to VC%0d (write) and VC%0d (read)", 
                                    test_name, wr_vc, rd_vc);
            end else begin
                fail_count++;
            end
        end
        
        // Clear all buffers
        clear_all_buffers();
        
        $display("  VC Concurrent Access: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test VC Buffer Full Isolation - Requirement 3.5, 8.3
    // Verify that a full VC doesn't block other VCs
    // =============================================================================
    task test_vc_buffer_full_isolation();
        int local_fail_start;
        int full_vc, other_vc;
        
        local_fail_start = fail_count;
        
        $display("Testing VC Buffer Full Isolation - Requirements 3.5, 8.3");
        $display("------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("VC_Full_Isolation_Test_%0d", i);
            test_passed = 1'b1;
            
            // Select a VC to fill
            full_vc = $urandom_range(0, NUM_VCS-1);
            other_vc = (full_vc + 1) % NUM_VCS;
            
            // Fill the selected VC
            wr_vc_id = full_vc;
            for (int w = 0; w < BUFFER_DEPTH; w++) begin
                wr_data = generate_random_flit(full_vc);
                wr_en = 1;
                @(posedge clk);
            end
            wr_en = 0;
            @(posedge clk);
            
            // Verify VC is full
            if (!vc_full[full_vc]) begin
                $display("  [FAIL] %s: VC%0d not full after %0d writes", test_name, full_vc, BUFFER_DEPTH);
                test_passed = 1'b0;
            end
            
            // Try to write to other VC
            wr_vc_id = other_vc;
            wr_data = generate_random_flit(other_vc);
            wr_en = 1;
            @(posedge clk);
            wr_en = 0;
            @(posedge clk);
            
            // Verify other VC accepted the write
            if (vc_count[other_vc] == 0) begin
                $display("  [FAIL] %s: VC%0d blocked by full VC%0d", test_name, other_vc, full_vc);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Full VC%0d doesn't block VC%0d", test_name, full_vc, other_vc);
            end else begin
                fail_count++;
            end
            
            // Clear buffers for next iteration
            clear_all_buffers();
        end
        
        $display("  VC Full Isolation: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Helper Tasks
    // =============================================================================
    
    function automatic flit_u generate_random_flit(input int vc_id);
        flit_u flit;
        logic [11:0] rand_txn_id;
        
        // Initialize all bits to zero
        flit = '0;
        
        // Generate random transaction ID
        rand_txn_id = $urandom_range(0, 4095);
        
        // Set transaction ID in the appropriate field based on VC type
        // All channel types have txn_id at the same bit position
        flit.req.txn_id = rand_txn_id;
        flit.req.src_id = $urandom_range(0, 255);
        flit.req.tgt_id = $urandom_range(0, 255);
        flit.req.addr = {$urandom(), $urandom_range(0, 65535)};
        
        return flit;
    endfunction
    
    task clear_all_buffers();
        // Read out all data from all VCs
        for (int v = 0; v < NUM_VCS; v++) begin
            rd_vc_id = v;
            while (!vc_empty[v]) begin
                rd_en = 1;
                @(posedge clk);
                rd_en = 0;
            end
        end
        @(posedge clk);
    endtask

endmodule
