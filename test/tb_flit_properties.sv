// =============================================================================
// Property-Based Test for Flit Structures
// Feature: coh-noc-architecture, Property 4: 虚拟通道功能完整性
// Validates: Requirements 2.3, 2.4, 2.5, 2.6
// =============================================================================

`timescale 1ns/1ps

import coh_noc_pkg::*;

module tb_flit_properties;

    // Test parameters
    parameter int NUM_ITERATIONS = 100;
    
    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;
    
    // Random variables for test generation
    req_opcode_e rand_req_opcode;
    rsp_opcode_e rand_rsp_opcode;
    dat_opcode_e rand_dat_opcode;
    snp_opcode_e rand_snp_opcode;
    
    logic [47:0] rand_addr;
    logic [11:0] rand_txn_id;
    logic [7:0]  rand_src_id;
    logic [7:0]  rand_tgt_id;
    logic [2:0]  rand_size;
    logic [511:0] rand_data;
    logic [63:0] rand_be;
    
    // Test result tracking
    string test_name;
    logic test_passed;
    
    // =============================================================================
    // Property 4: Virtual Channel Functional Integrity
    // For any CHI message type, the system should correctly support transmission
    // of REQ, RSP, DAT, SNP four virtual channels
    // =============================================================================
    
    initial begin
        $display("=============================================================================");
        $display("Property-Based Test: Flit Virtual Channel Functional Integrity");
        $display("Feature: coh-noc-architecture, Property 4");
        $display("Validates: Requirements 2.3, 2.4, 2.5, 2.6");
        $display("Iterations: %0d", NUM_ITERATIONS);
        $display("=============================================================================\n");
        
        // Run property tests
        test_req_channel_integrity();
        test_rsp_channel_integrity();
        test_dat_channel_integrity();
        test_snp_channel_integrity();
        
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
    // Test REQ Channel (VC_REQ) - Requirement 2.3
    // =============================================================================
    task test_req_channel_integrity();
        req_flit_t req_flit;
        virtual_channel_e vc;
        
        $display("Testing REQ Channel (VC_REQ) - Requirement 2.3");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("REQ_Channel_Test_%0d", i);
            test_passed = 1'b1;
            
            // Randomize REQ flit parameters
            randomize_req_params();
            
            // Pack REQ flit
            req_flit = pack_req_flit(
                rand_req_opcode,
                rand_addr,
                rand_txn_id,
                rand_src_id,
                rand_tgt_id,
                rand_size,
                3'b000,  // mem_attr
                4'h0,    // qos
                1'b0,    // ns
                1'b0,    // likely_shared
                1'b0,    // allow_retry
                1'b0     // order
            );
            
            // Verify virtual channel assignment
            vc = get_virtual_channel_from_req(rand_req_opcode);
            
            if (vc !== VC_REQ) begin
                $display("  [FAIL] %s: Expected VC_REQ, got %s", test_name, vc.name());
                test_passed = 1'b0;
            end
            
            // Verify flit fields are correctly packed
            if (req_flit.opcode !== rand_req_opcode ||
                req_flit.addr !== rand_addr ||
                req_flit.txn_id !== rand_txn_id ||
                req_flit.src_id !== rand_src_id ||
                req_flit.tgt_id !== rand_tgt_id ||
                req_flit.size !== rand_size) begin
                $display("  [FAIL] %s: Flit packing error", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  REQ Channel: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - (test_count - NUM_ITERATIONS)), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test RSP Channel (VC_RSP) - Requirement 2.4
    // =============================================================================
    task test_rsp_channel_integrity();
        rsp_flit_t rsp_flit;
        virtual_channel_e vc;
        int local_fail_start = fail_count;
        
        $display("Testing RSP Channel (VC_RSP) - Requirement 2.4");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("RSP_Channel_Test_%0d", i);
            test_passed = 1'b1;
            
            // Randomize RSP flit parameters
            randomize_rsp_params();
            
            // Pack RSP flit
            rsp_flit = pack_rsp_flit(
                rand_rsp_opcode,
                rand_txn_id,
                rand_src_id,
                rand_tgt_id,
                8'h00,   // dbid
                2'b00,   // resp
                2'b00    // fwd_state
            );
            
            // Verify virtual channel assignment
            vc = get_virtual_channel_from_rsp(rand_rsp_opcode);
            
            if (vc !== VC_RSP) begin
                $display("  [FAIL] %s: Expected VC_RSP, got %s", test_name, vc.name());
                test_passed = 1'b0;
            end
            
            // Verify flit fields are correctly packed
            if (rsp_flit.opcode !== rand_rsp_opcode ||
                rsp_flit.txn_id !== rand_txn_id ||
                rsp_flit.src_id !== rand_src_id ||
                rsp_flit.tgt_id !== rand_tgt_id) begin
                $display("  [FAIL] %s: Flit packing error", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  RSP Channel: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test DAT Channel (VC_DAT) - Requirement 2.5
    // =============================================================================
    task test_dat_channel_integrity();
        dat_flit_t dat_flit;
        virtual_channel_e vc;
        int local_fail_start = fail_count;
        
        $display("Testing DAT Channel (VC_DAT) - Requirement 2.5");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("DAT_Channel_Test_%0d", i);
            test_passed = 1'b1;
            
            // Randomize DAT flit parameters
            randomize_dat_params();
            
            // Pack DAT flit
            dat_flit = pack_dat_flit(
                rand_dat_opcode,
                rand_txn_id,
                rand_src_id,
                rand_tgt_id,
                8'h00,   // home_node_id
                8'h00,   // dbid
                rand_data,
                rand_be,
                3'b000,  // data_id
                2'b00    // resp
            );
            
            // Verify virtual channel assignment
            vc = get_virtual_channel_from_dat(rand_dat_opcode);
            
            if (vc !== VC_DAT) begin
                $display("  [FAIL] %s: Expected VC_DAT, got %s", test_name, vc.name());
                test_passed = 1'b0;
            end
            
            // Verify flit fields are correctly packed
            if (dat_flit.opcode !== rand_dat_opcode ||
                dat_flit.txn_id !== rand_txn_id ||
                dat_flit.src_id !== rand_src_id ||
                dat_flit.tgt_id !== rand_tgt_id ||
                dat_flit.data !== rand_data ||
                dat_flit.be !== rand_be) begin
                $display("  [FAIL] %s: Flit packing error", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  DAT Channel: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Test SNP Channel (VC_SNP) - Requirement 2.6
    // =============================================================================
    task test_snp_channel_integrity();
        snp_flit_t snp_flit;
        virtual_channel_e vc;
        int local_fail_start = fail_count;
        
        $display("Testing SNP Channel (VC_SNP) - Requirement 2.6");
        $display("---------------------------------------------");
        
        for (int i = 0; i < NUM_ITERATIONS; i++) begin
            test_count++;
            test_name = $sformatf("SNP_Channel_Test_%0d", i);
            test_passed = 1'b1;
            
            // Randomize SNP flit parameters
            randomize_snp_params();
            
            // Pack SNP flit
            snp_flit = pack_snp_flit(
                rand_snp_opcode,
                rand_addr[47:3],
                rand_txn_id,
                rand_src_id,
                8'h00,   // fwd_txn_id
                8'h00    // fwd_node_id
            );
            
            // Verify virtual channel assignment
            vc = get_virtual_channel_from_snp(rand_snp_opcode);
            
            if (vc !== VC_SNP) begin
                $display("  [FAIL] %s: Expected VC_SNP, got %s", test_name, vc.name());
                test_passed = 1'b0;
            end
            
            // Verify flit fields are correctly packed
            if (snp_flit.opcode !== rand_snp_opcode ||
                snp_flit.addr !== rand_addr[47:3] ||
                snp_flit.txn_id !== rand_txn_id ||
                snp_flit.src_id !== rand_src_id) begin
                $display("  [FAIL] %s: Flit packing error", test_name);
                test_passed = 1'b0;
            end
            
            if (test_passed) begin
                pass_count++;
                if (i < 5) $display("  [PASS] %s", test_name);
            end else begin
                fail_count++;
            end
        end
        
        $display("  SNP Channel: %0d/%0d tests passed\n", NUM_ITERATIONS - (fail_count - local_fail_start), NUM_ITERATIONS);
    endtask
    
    // =============================================================================
    // Randomization Helper Tasks
    // =============================================================================
    
    task randomize_req_params();
        int opcode_sel;
        opcode_sel = $urandom_range(0, 18);
        case (opcode_sel)
            0:  rand_req_opcode = REQ_READ_SHARED;
            1:  rand_req_opcode = REQ_READ_CLEAN;
            2:  rand_req_opcode = REQ_READ_ONCE;
            3:  rand_req_opcode = REQ_READ_NO_SNOOP;
            4:  rand_req_opcode = REQ_READ_UNIQUE;
            5:  rand_req_opcode = REQ_CLEAN_SHARED;
            6:  rand_req_opcode = REQ_CLEAN_INVALID;
            7:  rand_req_opcode = REQ_MAKE_INVALID;
            8:  rand_req_opcode = REQ_WRITE_BACK_FULL;
            9:  rand_req_opcode = REQ_WRITE_CLEAN_FULL;
            10: rand_req_opcode = REQ_WRITE_UNIQUE_FULL;
            11: rand_req_opcode = REQ_WRITE_UNIQUE_PTL;
            12: rand_req_opcode = REQ_WRITE_NO_SNOOP_FULL;
            13: rand_req_opcode = REQ_WRITE_NO_SNOOP_PTL;
            14: rand_req_opcode = REQ_ATOMIC_STORE;
            15: rand_req_opcode = REQ_ATOMIC_LOAD;
            16: rand_req_opcode = REQ_ATOMIC_SWAP;
            17: rand_req_opcode = REQ_ATOMIC_COMPARE;
            18: rand_req_opcode = REQ_DVM_OP;
        endcase
        
        rand_addr = $urandom();
        rand_addr[47:32] = $urandom_range(0, 65535);
        rand_txn_id = $urandom_range(0, 4095);
        rand_src_id = $urandom_range(0, 255);
        rand_tgt_id = $urandom_range(0, 255);
        rand_size = $urandom_range(0, 7);
    endtask
    
    task randomize_rsp_params();
        int opcode_sel;
        opcode_sel = $urandom_range(0, 6);
        case (opcode_sel)
            0: rand_rsp_opcode = RSP_COMP_ACK;
            1: rand_rsp_opcode = RSP_READ_RECEIPT;
            2: rand_rsp_opcode = RSP_COMP;
            3: rand_rsp_opcode = RSP_COMP_DATA;
            4: rand_rsp_opcode = RSP_DATA_SEPDATA;
            5: rand_rsp_opcode = RSP_RETRY_ACK;
            6: rand_rsp_opcode = RSP_PCR_GRANT_ACK;
        endcase
        
        rand_txn_id = $urandom_range(0, 4095);
        rand_src_id = $urandom_range(0, 255);
        rand_tgt_id = $urandom_range(0, 255);
    endtask
    
    task randomize_dat_params();
        int opcode_sel;
        opcode_sel = $urandom_range(0, 4);
        case (opcode_sel)
            0: rand_dat_opcode = DAT_DATA_FLIT;
            1: rand_dat_opcode = DAT_COMP_DATA;
            2: rand_dat_opcode = DAT_NON_COPY_BACK_WR_DATA;
            3: rand_dat_opcode = DAT_COPY_BACK_WR_DATA;
            4: rand_dat_opcode = DAT_DATA_SEP_DATA;
        endcase
        
        rand_txn_id = $urandom_range(0, 4095);
        rand_src_id = $urandom_range(0, 255);
        rand_tgt_id = $urandom_range(0, 255);
        
        // Randomize 512-bit data
        for (int i = 0; i < 16; i++) begin
            rand_data[i*32 +: 32] = $urandom();
        end
        
        // Randomize 64-bit byte enable
        rand_be[31:0] = $urandom();
        rand_be[63:32] = $urandom();
    endtask
    
    task randomize_snp_params();
        int opcode_sel;
        opcode_sel = $urandom_range(0, 15);
        case (opcode_sel)
            0:  rand_snp_opcode = SNP_SHARED;
            1:  rand_snp_opcode = SNP_CLEAN;
            2:  rand_snp_opcode = SNP_ONCE;
            3:  rand_snp_opcode = SNP_NOT_SHARED_DIRTY;
            4:  rand_snp_opcode = SNP_UNIQUE;
            5:  rand_snp_opcode = SNP_CLEAN_SHARED;
            6:  rand_snp_opcode = SNP_CLEAN_INVALID;
            7:  rand_snp_opcode = SNP_MAKE_INVALID;
            8:  rand_snp_opcode = SNP_DVM_OP;
            9:  rand_snp_opcode = SNP_FWD_SHARED;
            10: rand_snp_opcode = SNP_FWD_CLEAN;
            11: rand_snp_opcode = SNP_FWD_ONCE;
            12: rand_snp_opcode = SNP_FWD_NOT_SHARED_DIRTY;
            13: rand_snp_opcode = SNP_FWD_UNIQUE;
            14: rand_snp_opcode = SNP_FWD_CLEAN_SHARED;
            15: rand_snp_opcode = SNP_FWD_CLEAN_INVALID;
        endcase
        
        rand_addr = $urandom();
        rand_addr[47:32] = $urandom_range(0, 65535);
        rand_txn_id = $urandom_range(0, 4095);
        rand_src_id = $urandom_range(0, 255);
    endtask

endmodule
