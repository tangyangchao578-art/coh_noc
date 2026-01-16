// =============================================================================
// Property-Based Test for RN-F Proxy Functionality
// Feature: coh-noc-architecture, Property 13: RN-F 代理功能
// Validates: Requirements 5.1, 5.4
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_rn_f_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int NODE_ID = 8'h05;
    
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
    
    // CPU Interface signals
    logic        cpu_req_valid;
    logic        cpu_req_ready;
    logic        cpu_req_read;
    logic [47:0] cpu_req_addr;
    logic [3:0]  cpu_req_size;
    logic [511:0] cpu_req_data;
    logic [7:0]  cpu_req_qos;
    logic        cpu_rsp_valid;
    logic        cpu_rsp_ready;
    logic [511:0] cpu_rsp_data;
    logic        cpu_rsp_error;
    logic [11:0] cpu_rsp_txn_id;
    
    // Network Interface signals
    logic        req_out_valid;
    logic        req_out_ready;
    flit_u       req_out_flit;
    logic [1:0]  req_out_vc_id;
    logic [1:0]  req_out_channel_type;
    logic        req_out_credit_return;
    
    logic        rsp_in_valid;
    logic        rsp_in_ready;
    flit_u       rsp_in_flit;
    
    logic        dat_in_valid;
    logic        dat_in_ready;
    flit_u       dat_in_flit;
    
    logic        snp_in_valid;
    logic        snp_in_ready;
    flit_u       snp_in_flit;
    
    logic        snp_rsp_out_valid;
    logic        snp_rsp_out_ready;
    flit_u       snp_rsp_out_flit;
    logic [1:0]  snp_rsp_out_vc_id;
    logic [1:0]  snp_rsp_out_channel_type;
    logic        snp_rsp_out_credit_return;
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    rn_f #(
        .CACHE_SIZE(64*1024),
        .NUM_WAYS(4),
        .NODE_ID(NODE_ID)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .cpu_req_valid(cpu_req_valid),
        .cpu_req_ready(cpu_req_ready),
        .cpu_req_read(cpu_req_read),
        .cpu_req_addr(cpu_req_addr),
        .cpu_req_size(cpu_req_size),
        .cpu_req_data(cpu_req_data),
        .cpu_req_qos(cpu_req_qos),
        .cpu_rsp_valid(cpu_rsp_valid),
        .cpu_rsp_ready(cpu_rsp_ready),
        .cpu_rsp_data(cpu_rsp_data),
        .cpu_rsp_error(cpu_rsp_error),
        .cpu_rsp_txn_id(cpu_rsp_txn_id),
        .req_out_valid(req_out_valid),
        .req_out_ready(req_out_ready),
        .req_out_flit(req_out_flit),
        .req_out_vc_id(req_out_vc_id),
        .req_out_channel_type(req_out_channel_type),
        .req_out_credit_return(req_out_credit_return),
        .rsp_in_valid(rsp_in_valid),
        .rsp_in_ready(rsp_in_ready),
        .rsp_in_flit(rsp_in_flit),
        .dat_in_valid(dat_in_valid),
        .dat_in_ready(dat_in_ready),
        .dat_in_flit(dat_in_flit),
        .snp_in_valid(snp_in_valid),
        .snp_in_ready(snp_in_ready),
        .snp_in_flit(snp_in_flit),
        .snp_rsp_out_valid(snp_rsp_out_valid),
        .snp_rsp_out_ready(snp_rsp_out_ready),
        .snp_rsp_out_flit(snp_rsp_out_flit),
        .snp_rsp_out_vc_id(snp_rsp_out_vc_id),
        .snp_rsp_out_channel_type(snp_rsp_out_channel_type),
        .snp_rsp_out_credit_return(snp_rsp_out_credit_return)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 13: RN-F Proxy Functionality
    // For any CPU memory access request, RN-F should correctly convert it to
    // the appropriate network message and handle the response
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: RN-F Proxy Functionality");
        $display("Feature: coh-noc-architecture, Property 13");
        $display("Validates: Requirements 5.1, 5.4");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        init_cpu_interface();
        init_network_interfaces();
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_cpu_read_request_conversion();
        test_cpu_write_request_conversion();
        
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
    // Test CPU Read Request Conversion - Requirements 5.1, 5.4
    // Verify that CPU read requests are correctly converted to network REQ messages
    // =============================================================================
    task test_cpu_read_request_conversion();
        logic [47:0] test_addr;
        logic [3:0] test_size;
        logic [7:0] test_qos;
        req_flit_t captured_req;
        
        $display("Testing CPU Read Request Conversion - Requirements 5.1, 5.4");
        $display("--------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/2; i++) begin
            test_count++;
            test_name = $sformatf("CPU_Read_Conversion_%0d", i);
            test_passed = 1'b1;
            
            // Generate random read request
            test_addr = generate_random_address();
            test_size = $urandom_range(0, 6);  // 2^size bytes
            test_qos = $urandom_range(0, 15);
            
            // Send CPU read request and capture network request
            fork
                begin
                    send_cpu_read_request(test_addr, test_size, test_qos);
                end
                begin
                    capture_network_request(captured_req);
                end
            join
            
            // Verify conversion
            if (captured_req.opcode != REQ_READ_SHARED) begin
                $display("  [FAIL] %s: Wrong opcode (expected READ_SHARED, got 0x%02x)", 
                         test_name, captured_req.opcode);
                test_passed = 1'b0;
            end
            
            if (captured_req.addr != test_addr) begin
                $display("  [FAIL] %s: Address mismatch (expected 0x%012x, got 0x%012x)", 
                         test_name, test_addr, captured_req.addr);
                test_passed = 1'b0;
            end
            
            if (captured_req.src_id != NODE_ID) begin
                $display("  [FAIL] %s: Wrong source ID (expected 0x%02x, got 0x%02x)", 
                         test_name, NODE_ID, captured_req.src_id);
                test_passed = 1'b0;
            end
            
            if (captured_req.size != test_size) begin
                $display("  [FAIL] %s: Size mismatch (expected %0d, got %0d)", 
                         test_name, test_size, captured_req.size);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: CPU read correctly converted to REQ_READ_SHARED", test_name);
            end else begin
                fail_count++;
            end
            
            // Wait before next test
            repeat(5) @(posedge clk);
        end
        
        $display("  CPU Read Request Conversion: %0d/%0d tests passed\n", 
                 pass_count, NUM_ITERATIONS/2);
    endtask
    
    // =============================================================================
    // Test CPU Write Request Conversion - Requirements 5.1, 5.4
    // Verify that CPU write requests are correctly converted to network REQ messages
    // =============================================================================
    task test_cpu_write_request_conversion();
        logic [47:0] test_addr;
        logic [511:0] test_data;
        logic [3:0] test_size;
        req_flit_t captured_req;
        int local_pass_start;
        
        local_pass_start = pass_count;
        
        $display("Testing CPU Write Request Conversion - Requirements 5.1, 5.4");
        $display("---------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/2; i++) begin
            test_count++;
            test_name = $sformatf("CPU_Write_Conversion_%0d", i);
            test_passed = 1'b1;
            
            // Generate random write request
            test_addr = generate_random_address();
            test_data = {$urandom(), $urandom(), $urandom(), $urandom(), 
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom()};
            test_size = $urandom_range(0, 6);
            
            // Send CPU write request and capture network request
            fork
                begin
                    send_cpu_write_request(test_addr, test_data, test_size);
                end
                begin
                    capture_network_request(captured_req);
                end
            join
            
            // Verify conversion
            if (captured_req.opcode != REQ_WRITE_UNIQUE_FULL) begin
                $display("  [FAIL] %s: Wrong opcode (expected WRITE_UNIQUE_FULL, got 0x%02x)", 
                         test_name, captured_req.opcode);
                test_passed = 1'b0;
            end
            
            if (captured_req.addr != test_addr) begin
                $display("  [FAIL] %s: Address mismatch", test_name);
                test_passed = 1'b0;
            end
            
            if (captured_req.src_id != NODE_ID) begin
                $display("  [FAIL] %s: Wrong source ID", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: CPU write correctly converted to REQ_WRITE_UNIQUE_FULL", test_name);
            end else begin
                fail_count++;
            end
            
            repeat(5) @(posedge clk);
        end
        
        $display("  CPU Write Request Conversion: %0d/%0d tests passed\n", 
                 pass_count - local_pass_start, NUM_ITERATIONS/2);
    endtask
    
    // =============================================================================
    // Helper Tasks and Functions
    // =============================================================================
    
    task init_cpu_interface();
        cpu_req_valid = 0;
        cpu_req_read = 0;
        cpu_req_addr = 0;
        cpu_req_size = 0;
        cpu_req_data = 0;
        cpu_req_qos = 0;
        cpu_rsp_ready = 1;
    endtask
    
    task init_network_interfaces();
        req_out_ready = 1;
        rsp_in_valid = 0;
        rsp_in_flit = '0;
        dat_in_valid = 0;
        dat_in_flit = '0;
        snp_in_valid = 0;
        snp_in_flit = '0;
        snp_rsp_out_ready = 1;
    endtask
    
    task send_cpu_read_request(
        input logic [47:0] addr,
        input logic [3:0] size,
        input logic [7:0] qos
    );
        @(posedge clk);
        cpu_req_valid = 1;
        cpu_req_read = 1;
        cpu_req_addr = addr;
        cpu_req_size = size;
        cpu_req_qos = qos;
        
        wait(cpu_req_ready);
        @(posedge clk);
        cpu_req_valid = 0;
    endtask
    
    task send_cpu_write_request(
        input logic [47:0] addr,
        input logic [511:0] data,
        input logic [3:0] size
    );
        @(posedge clk);
        cpu_req_valid = 1;
        cpu_req_read = 0;
        cpu_req_addr = addr;
        cpu_req_data = data;
        cpu_req_size = size;
        cpu_req_qos = 0;
        
        wait(cpu_req_ready);
        @(posedge clk);
        cpu_req_valid = 0;
    endtask
    
    task capture_network_request(output req_flit_t captured);
        wait(req_out_valid && req_out_ready);
        captured = req_out_flit.req;
        @(posedge clk);
    endtask
    
    function logic [47:0] generate_random_address();
        logic [47:0] addr;
        addr = {$urandom(), $urandom()};
        addr[5:0] = 6'b000000;  // Align to 64-byte boundary
        return addr;
    endfunction

endmodule

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    parameter int NODE_ID = 8'h05;
    
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
    
    // CPU Interface
    cpu_if cpu_req();
    
    // Network Interfaces
    xp_port_if #(.CHANNEL_TYPE("REQ")) req_out();
    xp_port_if #(.CHANNEL_TYPE("RSP")) rsp_in();
    xp_port_if #(.CHANNEL_TYPE("DAT")) dat_in();
    xp_port_if #(.CHANNEL_TYPE("SNP")) snp_in();
    xp_port_if #(.CHANNEL_TYPE("DAT")) snp_rsp_out();
    
    // =============================================================================
    // DUT Instantiation
    // =============================================================================
    
    rn_f #(
        .CACHE_SIZE(64*1024),
        .NUM_WAYS(4),
        .NODE_ID(NODE_ID)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .cpu_req(cpu_req.slave),
        .req_out(req_out.master),
        .rsp_in(rsp_in.slave),
        .dat_in(dat_in.slave),
        .snp_in(snp_in.slave),
        .snp_rsp_out(snp_rsp_out.master)
    );
    
    // =============================================================================
    // Clock Generation
    // =============================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // =============================================================================
    // Property 13: RN-F Proxy Functionality
    // For any CPU memory access request, RN-F should correctly convert it to
    // the appropriate network message and handle the response
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: RN-F Proxy Functionality");
        $display("Feature: coh-noc-architecture, Property 13");
        $display("Validates: Requirements 5.1, 5.4");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("=============================================================================\n");
        
        // Initialize
        rst_n = 0;
        init_cpu_interface();
        init_network_interfaces();
        
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run property tests
        test_cpu_read_request_conversion();
        test_cpu_write_request_conversion();
        test_cache_hit_response();
        test_cache_miss_flow();
        
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
    // Test CPU Read Request Conversion - Requirements 5.1, 5.4
    // Verify that CPU read requests are correctly converted to network REQ messages
    // =============================================================================
    task test_cpu_read_request_conversion();
        logic [47:0] test_addr;
        logic [3:0] test_size;
        logic [7:0] test_qos;
        req_flit_t captured_req;
        
        $display("Testing CPU Read Request Conversion - Requirements 5.1, 5.4");
        $display("--------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("CPU_Read_Conversion_%0d", i);
            test_passed = 1'b1;
            
            // Generate random read request
            test_addr = generate_random_address();
            test_size = $urandom_range(0, 6);  // 2^size bytes
            test_qos = $urandom_range(0, 15);
            
            // Send CPU read request
            fork
                begin
                    send_cpu_read_request(test_addr, test_size, test_qos);
                end
                begin
                    capture_network_request(captured_req);
                end
            join
            
            // Verify conversion
            if (captured_req.opcode != REQ_READ_SHARED) begin
                $display("  [FAIL] %s: Wrong opcode (expected READ_SHARED, got 0x%02x)", 
                         test_name, captured_req.opcode);
                test_passed = 1'b0;
            end
            
            if (captured_req.addr != test_addr) begin
                $display("  [FAIL] %s: Address mismatch (expected 0x%012x, got 0x%012x)", 
                         test_name, test_addr, captured_req.addr);
                test_passed = 1'b0;
            end
            
            if (captured_req.src_id != NODE_ID) begin
                $display("  [FAIL] %s: Wrong source ID (expected 0x%02x, got 0x%02x)", 
                         test_name, NODE_ID, captured_req.src_id);
                test_passed = 1'b0;
            end
            
            if (captured_req.size != test_size) begin
                $display("  [FAIL] %s: Size mismatch (expected %0d, got %0d)", 
                         test_name, test_size, captured_req.size);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: CPU read correctly converted to REQ_READ_SHARED", test_name);
            end else begin
                fail_count++;
            end
            
            // Wait before next test
            repeat(5) @(posedge clk);
        end
        
        $display("  CPU Read Request Conversion: %0d/%0d tests passed\n", 
                 pass_count - (test_count - NUM_ITERATIONS/4), NUM_ITERATIONS/4);
    endtask
    
    // =============================================================================
    // Test CPU Write Request Conversion - Requirements 5.1, 5.4
    // Verify that CPU write requests are correctly converted to network REQ messages
    // =============================================================================
    task test_cpu_write_request_conversion();
        logic [47:0] test_addr;
        logic [511:0] test_data;
        logic [3:0] test_size;
        req_flit_t captured_req;
        int local_pass_start;
        
        local_pass_start = pass_count;
        
        $display("Testing CPU Write Request Conversion - Requirements 5.1, 5.4");
        $display("---------------------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("CPU_Write_Conversion_%0d", i);
            test_passed = 1'b1;
            
            // Generate random write request
            test_addr = generate_random_address();
            test_data = {$urandom(), $urandom(), $urandom(), $urandom(), 
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom()};
            test_size = $urandom_range(0, 6);
            
            // Send CPU write request
            fork
                begin
                    send_cpu_write_request(test_addr, test_data, test_size);
                end
                begin
                    capture_network_request(captured_req);
                end
            join
            
            // Verify conversion
            if (captured_req.opcode != REQ_WRITE_UNIQUE_FULL) begin
                $display("  [FAIL] %s: Wrong opcode (expected WRITE_UNIQUE_FULL, got 0x%02x)", 
                         test_name, captured_req.opcode);
                test_passed = 1'b0;
            end
            
            if (captured_req.addr != test_addr) begin
                $display("  [FAIL] %s: Address mismatch", test_name);
                test_passed = 1'b0;
            end
            
            if (captured_req.src_id != NODE_ID) begin
                $display("  [FAIL] %s: Wrong source ID", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: CPU write correctly converted to REQ_WRITE_UNIQUE_FULL", test_name);
            end else begin
                fail_count++;
            end
            
            repeat(5) @(posedge clk);
        end
        
        $display("  CPU Write Request Conversion: %0d/%0d tests passed\n", 
                 pass_count - local_pass_start, NUM_ITERATIONS/4);
    endtask
    
    // =============================================================================
    // Test Cache Hit Response - Requirements 5.1, 5.4
    // Verify that cache hits are handled correctly without network traffic
    // =============================================================================
    task test_cache_hit_response();
        logic [47:0] test_addr;
        logic [511:0] test_data;
        logic [511:0] read_data;
        int local_pass_start;
        
        local_pass_start = pass_count;
        
        $display("Testing Cache Hit Response - Requirements 5.1, 5.4");
        $display("-----------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Cache_Hit_Test_%0d", i);
            test_passed = 1'b1;
            
            // Generate test data
            test_addr = generate_random_address();
            test_data = {$urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom()};
            
            // First write to populate cache
            send_cpu_write_request_simple(test_addr, test_data);
            wait_for_cpu_response();
            repeat(10) @(posedge clk);
            
            // Now read from same address (should hit cache)
            fork
                begin
                    send_cpu_read_request_simple(test_addr);
                    wait_for_cpu_response();
                    read_data = cpu_req.rsp_data;
                end
                begin
                    // Monitor network - should see no new requests for cache hit
                    automatic int timeout = 100;
                    automatic logic saw_request = 1'b0;
                    for (int j = 0; j < timeout; j++) begin
                        @(posedge clk);
                        if (req_out.valid && req_out.ready) begin
                            saw_request = 1'b1;
                            break;
                        end
                    end
                    if (saw_request) begin
                        $display("  [FAIL] %s: Network request sent on cache hit", test_name);
                        test_passed = 1'b0;
                    end
                end
            join
            
            // Verify data matches
            if (read_data != test_data) begin
                $display("  [FAIL] %s: Data mismatch on cache hit", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: Cache hit handled correctly without network traffic", test_name);
            end else begin
                fail_count++;
            end
            
            repeat(5) @(posedge clk);
        end
        
        $display("  Cache Hit Response: %0d/%0d tests passed\n", 
                 pass_count - local_pass_start, NUM_ITERATIONS/4);
    endtask
    
    // =============================================================================
    // Test Cache Miss Flow - Requirements 5.1, 5.4
    // Verify complete cache miss handling with network request/response
    // =============================================================================
    task test_cache_miss_flow();
        logic [47:0] test_addr;
        logic [511:0] test_data;
        logic [511:0] read_data;
        req_flit_t captured_req;
        int local_pass_start;
        
        local_pass_start = pass_count;
        
        $display("Testing Cache Miss Flow - Requirements 5.1, 5.4");
        $display("--------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS/4; i++) begin
            test_count++;
            test_name = $sformatf("Cache_Miss_Flow_%0d", i);
            test_passed = 1'b1;
            
            // Generate unique address for cache miss
            test_addr = generate_random_address() | (i << 12);  // Ensure unique
            test_data = {$urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom()};
            
            // Send read request (will miss cache)
            fork
                begin
                    send_cpu_read_request_simple(test_addr);
                end
                begin
                    // Capture network request
                    capture_network_request(captured_req);
                    
                    // Send network response
                    send_network_response(captured_req.txn_id, test_data);
                end
            join
            
            // Wait for CPU response
            wait_for_cpu_response();
            read_data = cpu_req.rsp_data;
            
            // Verify data
            if (read_data != test_data) begin
                $display("  [FAIL] %s: Data mismatch after cache miss", test_name);
                test_passed = 1'b0;
            end
            
            if (captured_req.opcode != REQ_READ_SHARED) begin
                $display("  [FAIL] %s: Wrong request opcode on cache miss", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 3) $display("  [PASS] %s: Cache miss flow completed correctly", test_name);
            end else begin
                fail_count++;
            end
            
            repeat(5) @(posedge clk);
        end
        
        $display("  Cache Miss Flow: %0d/%0d tests passed\n", 
                 pass_count - local_pass_start, NUM_ITERATIONS/4);
    endtask
    
    // =============================================================================
    // Helper Tasks and Functions
    // =============================================================================
    
    task init_cpu_interface();
        cpu_req.req_valid = 0;
        cpu_req.req_read = 0;
        cpu_req.req_addr = 0;
        cpu_req.req_size = 0;
        cpu_req.req_data = 0;
        cpu_req.req_qos = 0;
        cpu_req.rsp_ready = 1;
    endtask
    
    task init_network_interfaces();
        req_out.ready = 1;
        rsp_in.valid = 0;
        rsp_in.flit = '0;
        dat_in.valid = 0;
        dat_in.flit = '0;
        snp_in.valid = 0;
        snp_in.flit = '0;
        snp_rsp_out.ready = 1;
    endtask
    
    task send_cpu_read_request(
        input logic [47:0] addr,
        input logic [3:0] size,
        input logic [7:0] qos
    );
        @(posedge clk);
        cpu_req.req_valid = 1;
        cpu_req.req_read = 1;
        cpu_req.req_addr = addr;
        cpu_req.req_size = size;
        cpu_req.req_qos = qos;
        
        wait(cpu_req.req_ready);
        @(posedge clk);
        cpu_req.req_valid = 0;
    endtask
    
    task send_cpu_read_request_simple(input logic [47:0] addr);
        @(posedge clk);
        cpu_req.req_valid = 1;
        cpu_req.req_read = 1;
        cpu_req.req_addr = addr;
        cpu_req.req_size = 6;  // 64 bytes
        cpu_req.req_qos = 0;
        
        wait(cpu_req.req_ready);
        @(posedge clk);
        cpu_req.req_valid = 0;
    endtask
    
    task send_cpu_write_request(
        input logic [47:0] addr,
        input logic [511:0] data,
        input logic [3:0] size
    );
        @(posedge clk);
        cpu_req.req_valid = 1;
        cpu_req.req_read = 0;
        cpu_req.req_addr = addr;
        cpu_req.req_data = data;
        cpu_req.req_size = size;
        cpu_req.req_qos = 0;
        
        wait(cpu_req.req_ready);
        @(posedge clk);
        cpu_req.req_valid = 0;
    endtask
    
    task send_cpu_write_request_simple(
        input logic [47:0] addr,
        input logic [511:0] data
    );
        @(posedge clk);
        cpu_req.req_valid = 1;
        cpu_req.req_read = 0;
        cpu_req.req_addr = addr;
        cpu_req.req_data = data;
        cpu_req.req_size = 6;  // 64 bytes
        cpu_req.req_qos = 0;
        
        wait(cpu_req.req_ready);
        @(posedge clk);
        cpu_req.req_valid = 0;
    endtask
    
    task capture_network_request(output req_flit_t captured);
        wait(req_out.valid && req_out.ready);
        captured = req_out.flit.req;
        @(posedge clk);
    endtask
    
    task send_network_response(
        input logic [11:0] txn_id,
        input logic [511:0] data
    );
        // Send RSP
        @(posedge clk);
        rsp_in.valid = 1;
        rsp_in.flit.rsp = pack_rsp_flit(
            .opcode(RSP_COMP_DATA),
            .txn_id(txn_id),
            .src_id(8'h00),
            .tgt_id(NODE_ID),
            .dbid(8'h00),
            .resp(2'b00),
            .fwd_state(2'b00)
        );
        @(posedge clk);
        rsp_in.valid = 0;
        
        // Send DAT
        repeat(2) @(posedge clk);
        dat_in.valid = 1;
        dat_in.flit.dat = pack_dat_flit(
            .opcode(DAT_COMP_DATA),
            .txn_id(txn_id),
            .src_id(8'h00),
            .tgt_id(NODE_ID),
            .home_node_id(8'h00),
            .dbid(8'h00),
            .data(data),
            .be(64'hFFFFFFFFFFFFFFFF),
            .data_id(3'b000),
            .resp(2'b00)
        );
        @(posedge clk);
        dat_in.valid = 0;
    endtask
    
    task wait_for_cpu_response();
        wait(cpu_req.rsp_valid);
        @(posedge clk);
    endtask
    
    function automatic logic [47:0] generate_random_address();
        logic [47:0] addr;
        addr = {$urandom(), $urandom()};
        addr[5:0] = 6'b000000;  // Align to 64-byte boundary
        return addr;
    endfunction

endmodule
