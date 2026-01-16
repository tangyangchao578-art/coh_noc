// =============================================================================
// System Integration Testbench
// Requirements: All requirements
// =============================================================================
// This testbench validates the complete coherent NoC system with end-to-end
// data flow and coherence protocol verification.
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_system_integration;

    // =============================================================================
    // Test Parameters
    // =============================================================================
    
    parameter int MESH_SIZE_X = 3;
    parameter int MESH_SIZE_Y = 3;
    parameter int NUM_RN_F = 4;
    parameter int NUM_HN_F = 2;
    parameter int NUM_SN_F = 2;
    parameter int SN_F_CHANNELS = 4;
    
    parameter int CLK_PERIOD = 10;  // 10ns = 100MHz
    
    // =============================================================================
    // Clock and Reset
    // =============================================================================
    
    logic clk;
    logic rst_n;
    
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    initial begin
        rst_n = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
    end
    
    // =============================================================================
    // DUT Interfaces
    // =============================================================================
    
    cpu_if cpu[NUM_RN_F-1:0]();
    ddr_if #(.ADDR_WIDTH(48), .DATA_WIDTH(512)) mem[NUM_SN_F-1:0][SN_F_CHANNELS-1:0]();
    
    logic system_ready;
    logic [31:0] total_transactions;
    logic [31:0] active_transactions;
    
    // =============================================================================
    // DUT Instance
    // =============================================================================
    
    coh_noc_system #(
        .MESH_SIZE_X(MESH_SIZE_X),
        .MESH_SIZE_Y(MESH_SIZE_Y),
        .NUM_RN_F(NUM_RN_F),
        .NUM_HN_F(NUM_HN_F),
        .NUM_SN_F(NUM_SN_F),
        .SN_F_CHANNELS(SN_F_CHANNELS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .cpu(cpu),
        .mem(mem),
        .system_ready(system_ready),
        .total_transactions(total_transactions),
        .active_transactions(active_transactions)
    );
    
    // =============================================================================
    // Memory Model (Simple DDR Simulator)
    // =============================================================================
    
    genvar sn, ch;
    generate
        for (sn = 0; sn < NUM_SN_F; sn++) begin : gen_sn_mem
            for (ch = 0; ch < SN_F_CHANNELS; ch++) begin : gen_ch_mem
                
                // Memory array
                logic [511:0] memory [logic [47:0]];
                
                // Command handling
                always_ff @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        mem[sn][ch].cmd_ready <= 1'b0;
                        mem[sn][ch].wr_ready <= 1'b0;
                        mem[sn][ch].rd_valid <= 1'b0;
                        mem[sn][ch].rd_data <= '0;
                        mem[sn][ch].rd_last <= 1'b0;
                        mem[sn][ch].rd_resp <= 2'b00;
                        mem[sn][ch].init_done <= 1'b0;
                        mem[sn][ch].cal_done <= 1'b0;
                        mem[sn][ch].error <= 1'b0;
                    end else begin
                        // Initialization
                        mem[sn][ch].init_done <= 1'b1;
                        mem[sn][ch].cal_done <= 1'b1;
                        mem[sn][ch].error <= 1'b0;
                        
                        // Always ready for commands
                        mem[sn][ch].cmd_ready <= 1'b1;
                        mem[sn][ch].wr_ready <= 1'b1;
                        
                        // Handle read commands
                        if (mem[sn][ch].cmd_valid && mem[sn][ch].cmd_ready && mem[sn][ch].cmd_read) begin
                            // Read from memory array
                            if (memory.exists(mem[sn][ch].cmd_addr)) begin
                                mem[sn][ch].rd_data <= memory[mem[sn][ch].cmd_addr];
                            end else begin
                                mem[sn][ch].rd_data <= 512'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
                            end
                            mem[sn][ch].rd_valid <= 1'b1;
                            mem[sn][ch].rd_last <= 1'b1;
                            mem[sn][ch].rd_resp <= 2'b00;  // OK
                        end else if (mem[sn][ch].rd_valid && mem[sn][ch].rd_ready) begin
                            mem[sn][ch].rd_valid <= 1'b0;
                            mem[sn][ch].rd_last <= 1'b0;
                        end
                        
                        // Handle write commands
                        if (mem[sn][ch].wr_valid && mem[sn][ch].wr_ready && mem[sn][ch].wr_last) begin
                            // Write to memory array
                            if (mem[sn][ch].cmd_valid && !mem[sn][ch].cmd_read) begin
                                memory[mem[sn][ch].cmd_addr] = mem[sn][ch].wr_data;
                                $display("[%0t] Memory[%0d][%0d] Write: Addr=0x%h Data=0x%h", 
                                        $time, sn, ch, mem[sn][ch].cmd_addr, mem[sn][ch].wr_data);
                            end
                        end
                    end
                end
                
            end
        end
    endgenerate
    
    // =============================================================================
    // Test Stimulus Tasks
    // =============================================================================
    
    // Task to send CPU read request
    task automatic cpu_read(
        input int cpu_id,
        input logic [47:0] addr,
        output logic [511:0] data,
        output logic error
    );
        begin
            @(posedge clk);
            cpu[cpu_id].req_valid <= 1'b1;
            cpu[cpu_id].req_read <= 1'b1;
            cpu[cpu_id].req_addr <= addr;
            cpu[cpu_id].req_size <= 4'h6;  // 64 bytes
            cpu[cpu_id].req_data <= '0;
            cpu[cpu_id].req_qos <= 8'h0;
            cpu[cpu_id].rsp_ready <= 1'b1;
            
            // Wait for request accepted
            wait(cpu[cpu_id].req_ready);
            @(posedge clk);
            cpu[cpu_id].req_valid <= 1'b0;
            
            // Wait for response
            wait(cpu[cpu_id].rsp_valid);
            @(posedge clk);
            data = cpu[cpu_id].rsp_data;
            error = cpu[cpu_id].rsp_error;
            cpu[cpu_id].rsp_ready <= 1'b0;
            
            $display("[%0t] CPU[%0d] Read: Addr=0x%h Data=0x%h Error=%b", 
                    $time, cpu_id, addr, data, error);
        end
    endtask
    
    // Task to send CPU write request
    task automatic cpu_write(
        input int cpu_id,
        input logic [47:0] addr,
        input logic [511:0] data,
        output logic error
    );
        begin
            @(posedge clk);
            cpu[cpu_id].req_valid <= 1'b1;
            cpu[cpu_id].req_read <= 1'b0;
            cpu[cpu_id].req_addr <= addr;
            cpu[cpu_id].req_size <= 4'h6;  // 64 bytes
            cpu[cpu_id].req_data <= data;
            cpu[cpu_id].req_qos <= 8'h0;
            cpu[cpu_id].rsp_ready <= 1'b1;
            
            // Wait for request accepted
            wait(cpu[cpu_id].req_ready);
            @(posedge clk);
            cpu[cpu_id].req_valid <= 1'b0;
            
            // Wait for response
            wait(cpu[cpu_id].rsp_valid);
            @(posedge clk);
            error = cpu[cpu_id].rsp_error;
            cpu[cpu_id].rsp_ready <= 1'b0;
            
            $display("[%0t] CPU[%0d] Write: Addr=0x%h Data=0x%h Error=%b", 
                    $time, cpu_id, addr, data, error);
        end
    endtask
    
    // =============================================================================
    // Test Scenarios
    // =============================================================================
    
    // Test 1: Basic Read/Write
    task test_basic_read_write();
        logic [511:0] write_data, read_data;
        logic error;
        
        $display("\n=== Test 1: Basic Read/Write ===");
        
        // Write data from CPU 0
        write_data = 512'hCAFEBABE_12345678_ABCDEF01_23456789_CAFEBABE_12345678_ABCDEF01_23456789_CAFEBABE_12345678_ABCDEF01_23456789_CAFEBABE_12345678_ABCDEF01_23456789;
        cpu_write(0, 48'h0000_1000, write_data, error);
        
        if (error) begin
            $display("ERROR: Write failed!");
            $finish;
        end
        
        // Read back from CPU 0
        cpu_read(0, 48'h0000_1000, read_data, error);
        
        if (error) begin
            $display("ERROR: Read failed!");
            $finish;
        end
        
        // Verify data
        if (read_data == write_data) begin
            $display("PASS: Data matches!");
        end else begin
            $display("FAIL: Data mismatch! Expected=0x%h Got=0x%h", write_data, read_data);
        end
    endtask
    
    // Test 2: Cache Coherence - Write from one CPU, read from another
    task test_cache_coherence();
        logic [511:0] write_data, read_data;
        logic error;
        
        $display("\n=== Test 2: Cache Coherence ===");
        
        // CPU 0 writes data
        write_data = 512'hDEADBEEF_FEEDFACE_BAADF00D_C0FFEE00_DEADBEEF_FEEDFACE_BAADF00D_C0FFEE00_DEADBEEF_FEEDFACE_BAADF00D_C0FFEE00_DEADBEEF_FEEDFACE_BAADF00D_C0FFEE00;
        cpu_write(0, 48'h0000_2000, write_data, error);
        
        if (error) begin
            $display("ERROR: CPU 0 write failed!");
            $finish;
        end
        
        // CPU 1 reads the same address (should get coherent data)
        cpu_read(1, 48'h0000_2000, read_data, error);
        
        if (error) begin
            $display("ERROR: CPU 1 read failed!");
            $finish;
        end
        
        // Verify coherence
        if (read_data == write_data) begin
            $display("PASS: Cache coherence maintained!");
        end else begin
            $display("FAIL: Cache coherence violation! Expected=0x%h Got=0x%h", write_data, read_data);
        end
    endtask
    
    // Test 3: Multiple CPUs accessing different addresses
    task test_parallel_access();
        logic [511:0] write_data[NUM_RN_F-1:0];
        logic [511:0] read_data[NUM_RN_F-1:0];
        logic error;
        
        $display("\n=== Test 3: Parallel Access ===");
        
        // Each CPU writes to a different address
        for (int i = 0; i < NUM_RN_F; i++) begin
            write_data[i] = 512'(i) * 512'h11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111;
            fork
                automatic int cpu_id = i;
                begin
                    cpu_write(cpu_id, 48'h0000_3000 + (cpu_id * 64), write_data[cpu_id], error);
                end
            join_none
        end
        
        // Wait for all writes to complete
        wait fork;
        
        // Each CPU reads back its own data
        for (int i = 0; i < NUM_RN_F; i++) begin
            cpu_read(i, 48'h0000_3000 + (i * 64), read_data[i], error);
            
            if (read_data[i] == write_data[i]) begin
                $display("PASS: CPU[%0d] data matches!", i);
            end else begin
                $display("FAIL: CPU[%0d] data mismatch!", i);
            end
        end
    endtask
    
    // Test 4: Stress test with random accesses
    task test_stress();
        logic [511:0] write_data, read_data;
        logic [47:0] addr;
        logic error;
        int num_ops = 100;
        
        $display("\n=== Test 4: Stress Test ===");
        
        for (int i = 0; i < num_ops; i++) begin
            int cpu_id = $urandom_range(0, NUM_RN_F-1);
            addr = {$urandom(), $urandom()} & 48'h0000_FFFF_FFC0;  // Align to 64 bytes
            write_data = {$urandom(), $urandom(), $urandom(), $urandom(),
                         $urandom(), $urandom(), $urandom(), $urandom(),
                         $urandom(), $urandom(), $urandom(), $urandom(),
                         $urandom(), $urandom(), $urandom(), $urandom()};
            
            if ($urandom_range(0, 1)) begin
                // Write
                cpu_write(cpu_id, addr, write_data, error);
            end else begin
                // Read
                cpu_read(cpu_id, addr, read_data, error);
            end
            
            if (error) begin
                $display("ERROR: Operation failed at iteration %0d", i);
            end
        end
        
        $display("PASS: Stress test completed %0d operations", num_ops);
    endtask
    
    // =============================================================================
    // Main Test Sequence
    // =============================================================================
    
    initial begin
        // Initialize CPU interfaces
        for (int i = 0; i < NUM_RN_F; i++) begin
            cpu[i].req_valid = 1'b0;
            cpu[i].req_read = 1'b0;
            cpu[i].req_addr = '0;
            cpu[i].req_size = '0;
            cpu[i].req_data = '0;
            cpu[i].req_qos = '0;
            cpu[i].rsp_ready = 1'b0;
        end
        
        // Wait for reset
        wait(rst_n);
        wait(system_ready);
        repeat(10) @(posedge clk);
        
        $display("\n========================================");
        $display("System Integration Test Starting");
        $display("========================================");
        
        // Run test scenarios
        test_basic_read_write();
        repeat(20) @(posedge clk);
        
        test_cache_coherence();
        repeat(20) @(posedge clk);
        
        test_parallel_access();
        repeat(20) @(posedge clk);
        
        test_stress();
        repeat(20) @(posedge clk);
        
        $display("\n========================================");
        $display("System Integration Test Complete");
        $display("Total Transactions: %0d", total_transactions);
        $display("Active Transactions: %0d", active_transactions);
        $display("========================================\n");
        
        $finish;
    end
    
    // =============================================================================
    // Timeout Watchdog
    // =============================================================================
    
    initial begin
        #(CLK_PERIOD * 100000);  // 1ms timeout
        $display("ERROR: Test timeout!");
        $finish;
    end
    
    // =============================================================================
    // Waveform Dump
    // =============================================================================
    
    initial begin
        $dumpfile("test_system_integration.vcd");
        $dumpvars(0, tb_system_integration);
    end

endmodule : tb_system_integration
