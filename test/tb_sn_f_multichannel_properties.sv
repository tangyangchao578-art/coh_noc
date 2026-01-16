// =============================================================================
// Property-Based Test for SN-F Multi-Channel Parallel Access
// Feature: coh-noc-architecture, Property 16: 多通道并行访问
// Validates: Requirements 6.4
// =============================================================================
// This test validates that for any concurrent memory access requests, the SN-F
// correctly handles multiple memory channels with parallel access, load balancing,
// and proper scheduling.
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_sn_f_multichannel_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int NUM_CHANNELS = 4;
    parameter int NODE_ID = 8'h10;
    parameter int ADDR_WIDTH = 48;
    parameter int DATA_WIDTH = 512;
    
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
    
    // Network interfaces
    xp_port_if req_in();
    xp_port_if rsp_out();
    xp_port_if dat_out();
    
    // DDR interfaces
    ddr_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) ddr_ctrl[NUM_CHANNELS-1:0]();
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    sn_f #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .NODE_ID(NODE_ID),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .req_in(req_in.slave),
        .rsp_out(rsp_out.master),
        .dat_out(dat_out.master),
        .ddr_ctrl(ddr_ctrl)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // DDR Controller Mock Behavior with Realistic Delays
    // =============================================================================
    
    genvar ch;
    generate
        for (ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_ddr_mock
            initial begin
                ddr_ctrl[ch].cmd_ready = 1'b1;
                ddr_ctrl[ch].wr_ready = 1'b1;
                ddr_ctrl[ch].rd_valid = 1'b0;
                ddr_ctrl[ch].rd_data = '0;
                ddr_ctrl[ch].rd_last = 1'b0;
                ddr_ctrl[ch].rd_resp = 2'b00;
                ddr_ctrl[ch].init_done = 1'b1;
                ddr_ctrl[ch].cal_done = 1'b1;
                ddr_ctrl[ch].error = 1'b0;
            end
            
            // Respond to read commands with variable delay
            always @(posedge clk) begin
                if (rst_n && ddr_ctrl[ch].cmd_valid && ddr_ctrl[ch].cmd_ready && ddr_ctrl[ch].cmd_read) begin
                    // Variable delay: 2-5 cycles
                    repeat($urandom_range(2, 5)) @(posedge clk);
                    ddr_ctrl[ch].rd_valid <= 1'b1;
                    ddr_ctrl[ch].rd_data <= {$urandom(), $urandom(), $urandom(), $urandom(), 
                                             $urandom(), $urandom(), $urandom(), $urandom(),
                                             $urandom(), $urandom(), $urandom(), $urandom(),
                                             $urandom(), $urandom(), $urandom(), $urandom()};
                    ddr_ctrl[ch].rd_last <= 1'b1;
                    ddr_ctrl[ch].rd_resp <= 2'b00;
                    @(posedge clk);
                    if (ddr_ctrl[ch].rd_ready) begin
                        ddr_ctrl[ch].rd_valid <= 1'b0;
                        ddr_ctrl[ch].rd_last <= 1'b0;
                    end
                end
            end
        end
    endgenerate
    
    // =============================================================================
    // Property 16: Multi-Channel Parallel Access
    // For any concurrent memory access requests, SN-F should correctly handle
    // multiple memory channels with parallel access
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: SN-F Multi-Channel Parallel Access");
        $display("Feature: coh-noc-architecture, Property 16");
        $display("Validates: Requirements 6.4");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("Number of Channels: %0d", NUM_CHANNELS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        req_in.valid = 0;
        req_in.flit = '0;
        req_in.vc_id = VC_REQ;
        req_in.channel_type = 2'b00;
        rsp_out.ready = 1;
        dat_out.ready = 1;
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_parallel_channel_usage();
        test_load_balancing();
        test_channel_independence();
        test_concurrent_throughput();
        
        // Print summary
        $display("\n=============================================================================");
        $display("Test Summary - Property 16");
        $display("=============================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("=============================================================================\n");
        
        if (fail_count == 0) begin
            $display("*** PROPERTY 16 TESTS PASSED ***\n");
        end else begin
            $display("*** PROPERTY 16 TESTS FAILED ***\n");
        end
        
        $finish(0);
    end

    // =============================================================================
    // Test 1: Parallel Channel Usage - Requirement 6.4
    // Verify that multiple channels can be used simultaneously
    // =============================================================================
    task test_parallel_channel_usage();
        int local_fail_start;
        logic [47:0] test_addrs[NUM_CHANNELS];
        logic [11:0] test_txn_ids[NUM_CHANNELS];
        logic [NUM_CHANNELS-1:0] channels_used;
        int active_channels;
        int max_concurrent;
        
        local_fail_start = fail_count;
        
        $display("Testing Parallel Channel Usage - Requirement 6.4");
        $display("----------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Parallel_Channel_Test_%0d", i);
            test_passed = 1'b1;
            channels_used = '0;
            max_concurrent = 0;
            
            // Generate multiple requests targeting different channels
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                // Use address bits to target specific channel
                test_addrs[ch] = ({$urandom(), $urandom()} & 48'hFFFFFFFFFF) | (ch << 6);
                test_txn_ids[ch] = ($urandom() & 12'hFFF) | (ch << 8);
            end
            
            // Send requests rapidly to fill multiple channels
            for (int req = 0; req < NUM_CHANNELS; req++) begin
                req_in.valid = 1'b1;
                req_in.flit.req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(test_addrs[req]),
                    .txn_id(test_txn_ids[req]),
                    .src_id(8'h01),
                    .tgt_id(NODE_ID),
                    .size(3'b110),
                    .mem_attr(3'b000),
                    .qos(4'h0),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
                req_in.vc_id = VC_REQ;
                req_in.channel_type = 2'b00;
                
                @(posedge clk);
                if (req_in.ready) begin
                    // Track which channel accepted this request
                    for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                        if (dut.txn_buffer[dut.free_txn_idx].channel_id == ch) begin
                            channels_used[ch] = 1'b1;
                        end
                    end
                end
            end
            req_in.valid = 1'b0;
            
            // Check how many channels are actively processing
            repeat(3) @(posedge clk);
            active_channels = 0;
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                if (ddr_ctrl[ch].cmd_valid || dut.channel_busy[ch]) begin
                    active_channels++;
                end
            end
            
            if (active_channels > max_concurrent) begin
                max_concurrent = active_channels;
            end
            
            // Verify multiple channels were used
            if ($countones(channels_used) < 2) begin
                $display("  [FAIL] %s: Only %0d channels used (expected >= 2)", 
                         test_name, $countones(channels_used));
                test_passed = 1'b0;
            end
            
            // Verify concurrent processing occurred
            if (max_concurrent < 2) begin
                $display("  [FAIL] %s: Max concurrent channels = %0d (expected >= 2)", 
                         test_name, max_concurrent);
                test_passed = 1'b0;
            end
            
            // Wait for all transactions to complete
            repeat(30) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: %0d channels used, %0d concurrent", 
                                   test_name, $countones(channels_used), max_concurrent);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Parallel Channel Usage: %0d/%0d tests passed\n", 
                 NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test 2: Load Balancing - Requirement 6.4
    // Verify that requests are distributed across channels
    // =============================================================================
    task test_load_balancing();
        int local_fail_start;
        int channel_usage[NUM_CHANNELS];
        logic [47:0] test_addr;
        logic [11:0] test_txn_id;
        int min_usage, max_usage;
        real balance_ratio;
        
        local_fail_start = fail_count;
        
        $display("Testing Load Balancing - Requirement 6.4");
        $display("--------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Load_Balance_Test_%0d", i);
            test_passed = 1'b1;
            
            // Reset channel usage counters
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                channel_usage[ch] = 0;
            end
            
            // Send multiple requests and track channel allocation
            for (int req = 0; req < NUM_CHANNELS * 4; req++) begin
                test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
                test_txn_id = $urandom() & 12'hFFF;
                
                req_in.valid = 1'b1;
                req_in.flit.req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(test_addr),
                    .txn_id(test_txn_id),
                    .src_id(8'h01),
                    .tgt_id(NODE_ID),
                    .size(3'b110),
                    .mem_attr(3'b000),
                    .qos(4'h0),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
                req_in.vc_id = VC_REQ;
                req_in.channel_type = 2'b00;
                
                @(posedge clk);
                while (!req_in.ready) @(posedge clk);
                
                // Track which channel was selected
                channel_usage[dut.selected_channel]++;
                
                req_in.valid = 1'b0;
                repeat(2) @(posedge clk);
            end
            
            // Calculate load balance metrics
            min_usage = channel_usage[0];
            max_usage = channel_usage[0];
            for (int ch = 1; ch < NUM_CHANNELS; ch++) begin
                if (channel_usage[ch] < min_usage) min_usage = channel_usage[ch];
                if (channel_usage[ch] > max_usage) max_usage = channel_usage[ch];
            end
            
            // Check balance ratio (max should not be more than 2x min)
            if (min_usage > 0) begin
                balance_ratio = real'(max_usage) / real'(min_usage);
                if (balance_ratio > 2.5) begin
                    $display("  [FAIL] %s: Poor load balance (ratio=%.2f)", test_name, balance_ratio);
                    test_passed = 1'b0;
                end
            end
            
            // Verify all channels were used
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                if (channel_usage[ch] == 0) begin
                    $display("  [FAIL] %s: Channel %0d never used", test_name, ch);
                    test_passed = 1'b0;
                end
            end
            
            // Wait for completion
            repeat(50) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Balance ratio=%.2f", test_name, balance_ratio);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Load Balancing: %0d/%0d tests passed\n", 
                 NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask

    // =============================================================================
    // Test 3: Channel Independence - Requirement 6.4
    // Verify that operations on different channels don't interfere
    // =============================================================================
    task test_channel_independence();
        int local_fail_start;
        logic [47:0] test_addrs[NUM_CHANNELS];
        logic [11:0] test_txn_ids[NUM_CHANNELS];
        logic [NUM_CHANNELS-1:0] responses_received;
        int response_count;
        
        local_fail_start = fail_count;
        
        $display("Testing Channel Independence - Requirement 6.4");
        $display("--------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Channel_Independence_Test_%0d", i);
            test_passed = 1'b1;
            responses_received = '0;
            response_count = 0;
            
            // Generate requests for each channel
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                // Target specific channel using address interleaving
                test_addrs[ch] = ({$urandom(), $urandom()} & 48'hFFFFFFFF00) | (ch << 6);
                test_txn_ids[ch] = (ch << 8) | i;
            end
            
            // Send all requests
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                req_in.valid = 1'b1;
                req_in.flit.req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(test_addrs[ch]),
                    .txn_id(test_txn_ids[ch]),
                    .src_id(8'h01 + ch),
                    .tgt_id(NODE_ID),
                    .size(3'b110),
                    .mem_attr(3'b000),
                    .qos(4'h0),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
                req_in.vc_id = VC_REQ;
                req_in.channel_type = 2'b00;
                
                @(posedge clk);
                while (!req_in.ready) @(posedge clk);
                req_in.valid = 1'b0;
                @(posedge clk);
            end
            
            // Monitor for responses from all channels
            fork
                begin
                    for (int cycle = 0; cycle < 100; cycle++) begin
                        @(posedge clk);
                        if (dat_out.valid) begin
                            // Check which transaction this response is for
                            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                                if (dat_out.flit.dat.txn_id == test_txn_ids[ch]) begin
                                    responses_received[ch] = 1'b1;
                                    response_count++;
                                end
                            end
                        end
                        
                        // Exit early if all responses received
                        if (response_count >= NUM_CHANNELS) begin
                            cycle = 100;
                        end
                    end
                end
            join
            
            // Verify all channels responded independently
            if (response_count != NUM_CHANNELS) begin
                $display("  [FAIL] %s: Only %0d/%0d responses received", 
                         test_name, response_count, NUM_CHANNELS);
                test_passed = 1'b0;
            end
            
            // Verify no responses were lost or duplicated
            for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                if (!responses_received[ch]) begin
                    $display("  [FAIL] %s: Channel %0d response missing", test_name, ch);
                    test_passed = 1'b0;
                end
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: All %0d channels responded independently", 
                                   test_name, NUM_CHANNELS);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Channel Independence: %0d/%0d tests passed\n", 
                 NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test 4: Concurrent Throughput - Requirement 6.4
    // Verify that multiple channels increase overall throughput
    // =============================================================================
    task test_concurrent_throughput();
        int local_fail_start;
        int single_channel_time;
        int multi_channel_time;
        real speedup;
        logic [47:0] test_addr;
        logic [11:0] test_txn_id;
        int start_time, end_time;
        int responses_received;
        
        local_fail_start = fail_count;
        
        $display("Testing Concurrent Throughput - Requirement 6.4");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Throughput_Test_%0d", i);
            test_passed = 1'b1;
            
            // Measure time for sequential requests (simulating single channel)
            start_time = $time;
            for (int req = 0; req < 4; req++) begin
                test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
                test_txn_id = ($urandom() & 12'hFFF) | (req << 8);
                
                req_in.valid = 1'b1;
                req_in.flit.req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(test_addr),
                    .txn_id(test_txn_id),
                    .src_id(8'h01),
                    .tgt_id(NODE_ID),
                    .size(3'b110),
                    .mem_attr(3'b000),
                    .qos(4'h0),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
                req_in.vc_id = VC_REQ;
                req_in.channel_type = 2'b00;
                
                @(posedge clk);
                while (!req_in.ready) @(posedge clk);
                req_in.valid = 1'b0;
                
                // Wait for response before sending next
                responses_received = 0;
                fork
                    begin
                        for (int cycle = 0; cycle < 50; cycle++) begin
                            @(posedge clk);
                            if (dat_out.valid && dat_out.flit.dat.txn_id == test_txn_id) begin
                                responses_received = 1;
                                cycle = 50;
                            end
                        end
                    end
                join
            end
            single_channel_time = $time - start_time;
            
            // Small delay between tests
            repeat(10) @(posedge clk);
            
            // Measure time for parallel requests (using multiple channels)
            start_time = $time;
            responses_received = 0;
            
            // Send all requests rapidly
            for (int req = 0; req < 4; req++) begin
                test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
                test_txn_id = ($urandom() & 12'hFFF) | ((req + 16) << 8);
                
                req_in.valid = 1'b1;
                req_in.flit.req = pack_req_flit(
                    .opcode(REQ_READ_SHARED),
                    .addr(test_addr),
                    .txn_id(test_txn_id),
                    .src_id(8'h01),
                    .tgt_id(NODE_ID),
                    .size(3'b110),
                    .mem_attr(3'b000),
                    .qos(4'h0),
                    .ns(1'b0),
                    .likely_shared(1'b0),
                    .allow_retry(1'b0),
                    .order(1'b0)
                );
                req_in.vc_id = VC_REQ;
                req_in.channel_type = 2'b00;
                
                @(posedge clk);
                while (!req_in.ready) @(posedge clk);
                req_in.valid = 1'b0;
                @(posedge clk);
            end
            
            // Wait for all responses
            fork
                begin
                    for (int cycle = 0; cycle < 100; cycle++) begin
                        @(posedge clk);
                        if (dat_out.valid) begin
                            responses_received++;
                        end
                        if (responses_received >= 4) begin
                            cycle = 100;
                        end
                    end
                end
            join
            multi_channel_time = $time - start_time;
            
            // Calculate speedup
            if (multi_channel_time > 0) begin
                speedup = real'(single_channel_time) / real'(multi_channel_time);
                
                // Multi-channel should be faster (speedup > 1.0)
                if (speedup < 1.0) begin
                    $display("  [FAIL] %s: No speedup (%.2fx)", test_name, speedup);
                    test_passed = 1'b0;
                end
            end else begin
                $display("  [FAIL] %s: Invalid timing measurement", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s: Speedup=%.2fx", test_name, speedup);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Concurrent Throughput: %0d/%0d tests passed\n", 
                 NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask

endmodule
