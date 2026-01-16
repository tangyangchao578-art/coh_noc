// =============================================================================
// Property-Based Test for SN-F Memory Interface Protocol Conversion
// Feature: coh-noc-architecture, Property 15: 内存接口协议转换
// Validates: Requirements 6.1, 6.2
// =============================================================================
// This test validates that for any network memory access request, the SN-F
// correctly converts it to memory controller protocol format.
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_sn_f_properties;

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
    // DDR Controller Mock Behavior
    // =============================================================================
    
    // Simple mock that responds to commands
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
            
            // Respond to read commands after delay
            always @(posedge clk) begin
                if (rst_n && ddr_ctrl[ch].cmd_valid && ddr_ctrl[ch].cmd_ready && ddr_ctrl[ch].cmd_read) begin
                    repeat(2) @(posedge clk);
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
    // Property 15: Memory Interface Protocol Conversion
    // For any network memory access request, SN-F should correctly convert
    // to memory controller protocol format
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: SN-F Memory Interface Protocol Conversion");
        $display("Feature: coh-noc-architecture, Property 15");
        $display("Validates: Requirements 6.1, 6.2");
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
        test_read_conversion();
        test_write_conversion();
        test_protocol_fields();
        
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
    // Test Read Request Conversion - Requirement 6.1, 6.2
    // =============================================================================
    task test_read_conversion();
        int local_fail_start;
        logic [47:0] test_addr;
        logic [11:0] test_txn_id;
        logic cmd_found;
        int ch;
        
        local_fail_start = fail_count;
        
        $display("Testing Read Request Conversion - Requirements 6.1, 6.2");
        $display("-----------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Read_Conversion_Test_%0d", i);
            test_passed = 1'b1;
            cmd_found = 1'b0;
            
            // Generate random read request
            test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
            test_txn_id = $urandom() & 12'hFFF;
            
            // Send read request
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
            
            // Wait for acceptance
            @(posedge clk);
            while (!req_in.ready) @(posedge clk);
            req_in.valid = 1'b0;
            
            // Check that DDR command was issued
            @(posedge clk);
            for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1) begin
                if (ddr_ctrl[ch].cmd_valid) begin
                    cmd_found = 1'b1;
                    
                    // Verify command is read
                    if (!ddr_ctrl[ch].cmd_read) begin
                        $display("  [FAIL] %s: Channel %0d cmd_read should be 1", test_name, ch);
                        test_passed = 1'b0;
                    end
                    
                    // Verify address matches
                    if (ddr_ctrl[ch].cmd_addr != test_addr[ADDR_WIDTH-1:0]) begin
                        $display("  [FAIL] %s: Address mismatch", test_name);
                        test_passed = 1'b0;
                    end
                end
            end
            
            if (!cmd_found) begin
                $display("  [FAIL] %s: No DDR command issued", test_name);
                test_passed = 1'b0;
            end
            
            // Wait for completion
            repeat(10) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Read Conversion: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Write Request Conversion - Requirement 6.1, 6.2
    // =============================================================================
    task test_write_conversion();
        int local_fail_start;
        logic [47:0] test_addr;
        logic [11:0] test_txn_id;
        logic cmd_found;
        int ch;
        
        local_fail_start = fail_count;
        
        $display("Testing Write Request Conversion - Requirements 6.1, 6.2");
        $display("------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Write_Conversion_Test_%0d", i);
            test_passed = 1'b1;
            cmd_found = 1'b0;
            
            // Generate random write request
            test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
            test_txn_id = $urandom() & 12'hFFF;
            
            // Send write request
            req_in.valid = 1'b1;
            req_in.flit.req = pack_req_flit(
                .opcode(REQ_WRITE_BACK_FULL),
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
            
            // Wait for acceptance
            @(posedge clk);
            while (!req_in.ready) @(posedge clk);
            req_in.valid = 1'b0;
            
            // Check that DDR command was issued
            @(posedge clk);
            for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1) begin
                if (ddr_ctrl[ch].cmd_valid) begin
                    cmd_found = 1'b1;
                    
                    // Verify command is write
                    if (ddr_ctrl[ch].cmd_read) begin
                        $display("  [FAIL] %s: Channel %0d cmd_read should be 0", test_name, ch);
                        test_passed = 1'b0;
                    end
                    
                    // Verify write data is valid
                    if (!ddr_ctrl[ch].wr_valid) begin
                        $display("  [FAIL] %s: wr_valid should be 1", test_name);
                        test_passed = 1'b0;
                    end
                end
            end
            
            if (!cmd_found) begin
                $display("  [FAIL] %s: No DDR command issued", test_name);
                test_passed = 1'b0;
            end
            
            // Wait for completion
            repeat(10) @(posedge clk);
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Write Conversion: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test Protocol Field Preservation - Requirement 6.2
    // =============================================================================
    task test_protocol_fields();
        int local_fail_start;
        logic [47:0] test_addr;
        logic [11:0] test_txn_id;
        logic [7:0] test_src_id;
        logic response_found;
        int ch;
        int cycle;
        
        local_fail_start = fail_count;
        
        $display("Testing Protocol Field Preservation - Requirement 6.2");
        $display("--------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("Protocol_Fields_Test_%0d", i);
            test_passed = 1'b1;
            response_found = 1'b0;
            
            // Generate random request
            test_addr = {$urandom(), $urandom()} & 48'hFFFFFFFFFFFF;
            test_txn_id = $urandom() & 12'hFFF;
            test_src_id = $urandom() & 8'hFF;
            
            // Send read request
            req_in.valid = 1'b1;
            req_in.flit.req = pack_req_flit(
                .opcode(REQ_READ_SHARED),
                .addr(test_addr),
                .txn_id(test_txn_id),
                .src_id(test_src_id),
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
            
            // Wait for acceptance
            @(posedge clk);
            while (!req_in.ready) @(posedge clk);
            req_in.valid = 1'b0;
            
            // Wait for DAT response
            for (cycle = 0; cycle < 20; cycle = cycle + 1) begin
                @(posedge clk);
                if (dat_out.valid) begin
                    response_found = 1'b1;
                    
                    // Verify transaction ID matches
                    if (dat_out.flit.dat.txn_id != test_txn_id) begin
                        $display("  [FAIL] %s: TXN_ID mismatch", test_name);
                        test_passed = 1'b0;
                    end
                    
                    // Verify source ID is NODE_ID
                    if (dat_out.flit.dat.src_id != NODE_ID) begin
                        $display("  [FAIL] %s: SRC_ID mismatch", test_name);
                        test_passed = 1'b0;
                    end
                    
                    // Verify target ID is original source
                    if (dat_out.flit.dat.tgt_id != test_src_id) begin
                        $display("  [FAIL] %s: TGT_ID mismatch", test_name);
                        test_passed = 1'b0;
                    end
                    
                    cycle = 20; // Exit loop
                end
            end
            
            if (!response_found) begin
                $display("  [FAIL] %s: No response received", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  Protocol Fields: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask

endmodule
