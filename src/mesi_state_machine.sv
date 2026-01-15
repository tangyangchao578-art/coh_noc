// =============================================================================
// MESI Protocol State Machine - Cache Coherency State Transitions
// Requirements: 4.6
// =============================================================================

import coh_noc_pkg::*;

module mesi_state_machine #(
    parameter int ADDR_WIDTH = 48,
    parameter int NODE_ID_WIDTH = 8
)(
    input  logic clk,
    input  logic rst_n,
    
    // State Machine Control Interface
    input  logic                    req_valid,
    output logic                    req_ready,
    input  logic [ADDR_WIDTH-1:0]   req_addr,
    input  coherency_event_e        req_event,
    input  logic [NODE_ID_WIDTH-1:0] req_node_id,
    input  directory_entry_t        current_state,
    
    // State Machine Response Interface
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output directory_entry_t        new_state,
    output coherency_action_t       required_actions,
    output logic                    state_changed,
    
    // Snoop Generation Interface
    output logic                    snoop_valid,
    input  logic                    snoop_ready,
    output logic [ADDR_WIDTH-1:0]   snoop_addr,
    output snp_opcode_e             snoop_opcode,
    output logic [15:0]             snoop_targets,  // Bitmask of target nodes
    
    // Error and Debug Interface
    output logic                    protocol_error,
    output logic [7:0]              error_code
);

    // =============================================================================
    // Coherency Event Types
    // =============================================================================
    
    typedef enum logic [3:0] {
        // CPU-initiated events
        EVENT_CPU_READ      = 4'h0,
        EVENT_CPU_WRITE     = 4'h1,
        EVENT_CPU_EVICT     = 4'h2,
        
        // Network-initiated events
        EVENT_READ_REQ      = 4'h3,
        EVENT_WRITE_REQ     = 4'h4,
        EVENT_UPGRADE_REQ   = 4'h5,
        
        // Snoop responses
        EVENT_SNOOP_HIT_M   = 4'h6,
        EVENT_SNOOP_HIT_E   = 4'h7,
        EVENT_SNOOP_HIT_S   = 4'h8,
        EVENT_SNOOP_MISS    = 4'h9,
        
        // Memory responses
        EVENT_MEM_DATA      = 4'hA,
        EVENT_MEM_ACK       = 4'hB,
        
        // Invalidation events
        EVENT_INVALIDATE    = 4'hC,
        EVENT_WRITEBACK     = 4'hD
    } coherency_event_e;
    
    // =============================================================================
    // Coherency Action Types
    // =============================================================================
    
    typedef struct packed {
        logic send_snoop_shared;     // Send snoop to get shared copy
        logic send_snoop_exclusive;  // Send snoop to get exclusive copy
        logic send_snoop_invalidate; // Send snoop to invalidate copies
        logic send_mem_read;         // Send memory read request
        logic send_mem_write;        // Send memory write request
        logic send_cpu_data;         // Send data to CPU
        logic send_cpu_ack;          // Send acknowledgment to CPU
        logic send_net_data;         // Send data over network
        logic send_net_ack;          // Send network acknowledgment
        logic update_directory;      // Update directory state
        logic [7:0] reserved;        // Reserved for future use
    } coherency_action_t;
    
    // =============================================================================
    // State Machine Registers
    // =============================================================================
    
    typedef enum logic [2:0] {
        SM_IDLE,
        SM_PROCESS,
        SM_SNOOP_WAIT,
        SM_MEM_WAIT,
        SM_RESPOND
    } sm_state_e;
    
    sm_state_e state, next_state;
    
    // Registered inputs and outputs
    logic [ADDR_WIDTH-1:0]   req_addr_r;
    coherency_event_e        req_event_r;
    logic [NODE_ID_WIDTH-1:0] req_node_id_r;
    directory_entry_t        current_state_r;
    
    directory_entry_t        new_state_r;
    coherency_action_t       required_actions_r;
    logic                    state_changed_r;
    
    logic                    snoop_valid_r;
    logic [ADDR_WIDTH-1:0]   snoop_addr_r;
    snp_opcode_e             snoop_opcode_r;
    logic [15:0]             snoop_targets_r;
    
    logic                    protocol_error_r;
    logic [7:0]              error_code_r;
    
    // =============================================================================
    // State Machine Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= SM_IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            SM_IDLE: begin
                if (req_valid) begin
                    next_state = SM_PROCESS;
                end
            end
            
            SM_PROCESS: begin
                // Determine if we need to wait for snoops or memory
                if (required_actions_r.send_snoop_shared || 
                    required_actions_r.send_snoop_exclusive || 
                    required_actions_r.send_snoop_invalidate) begin
                    if (snoop_ready) begin
                        next_state = SM_SNOOP_WAIT;
                    end
                end else if (required_actions_r.send_mem_read || 
                            required_actions_r.send_mem_write) begin
                    next_state = SM_MEM_WAIT;
                end else begin
                    next_state = SM_RESPOND;
                end
            end
            
            SM_SNOOP_WAIT: begin
                // In real implementation, would wait for snoop responses
                // For now, proceed to response
                next_state = SM_RESPOND;
            end
            
            SM_MEM_WAIT: begin
                // In real implementation, would wait for memory responses
                // For now, proceed to response
                next_state = SM_RESPOND;
            end
            
            SM_RESPOND: begin
                if (rsp_ready) begin
                    next_state = SM_IDLE;
                end
            end
        endcase
    end
    
    // =============================================================================
    // Interface Assignments
    // =============================================================================
    
    assign req_ready = (state == SM_IDLE);
    assign rsp_valid = (state == SM_RESPOND);
    assign new_state = new_state_r;
    assign required_actions = required_actions_r;
    assign state_changed = state_changed_r;
    
    assign snoop_valid = snoop_valid_r;
    assign snoop_addr = snoop_addr_r;
    assign snoop_opcode = snoop_opcode_r;
    assign snoop_targets = snoop_targets_r;
    
    assign protocol_error = protocol_error_r;
    assign error_code = error_code_r;
    
    // =============================================================================
    // MESI State Transition Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_addr_r <= '0;
            req_event_r <= EVENT_CPU_READ;
            req_node_id_r <= '0;
            current_state_r <= init_directory_entry();
            
            new_state_r <= init_directory_entry();
            required_actions_r <= '0;
            state_changed_r <= 1'b0;
            
            snoop_valid_r <= 1'b0;
            snoop_addr_r <= '0;
            snoop_opcode_r <= SNP_SHARED;
            snoop_targets_r <= '0;
            
            protocol_error_r <= 1'b0;
            error_code_r <= '0;
            
        end else begin
            case (state)
                SM_IDLE: begin
                    if (req_valid) begin
                        // Capture request
                        req_addr_r <= req_addr;
                        req_event_r <= req_event;
                        req_node_id_r <= req_node_id;
                        current_state_r <= current_state;
                        
                        // Clear previous outputs
                        snoop_valid_r <= 1'b0;
                        protocol_error_r <= 1'b0;
                    end
                end
                
                SM_PROCESS: begin
                    // Process MESI state transition
                    directory_entry_t next_dir_state;
                    coherency_action_t actions;
                    logic error;
                    logic [7:0] err_code;
                    
                    // Initialize
                    next_dir_state = current_state_r;
                    actions = '0;
                    error = 1'b0;
                    err_code = 8'h00;
                    
                    // MESI state transition logic
                    case (current_state_r.state)
                        DIR_INVALID: begin
                            case (req_event_r)
                                EVENT_CPU_READ, EVENT_READ_REQ: begin
                                    // I -> S or I -> E (depending on other sharers)
                                    next_dir_state = directory_read_transition(current_state_r, req_node_id_r);
                                    actions.send_mem_read = 1'b1;
                                    actions.send_cpu_data = 1'b1;
                                    actions.update_directory = 1'b1;
                                end
                                
                                EVENT_CPU_WRITE, EVENT_WRITE_REQ: begin
                                    // I -> M
                                    next_dir_state = directory_write_transition(current_state_r, req_node_id_r);
                                    actions.send_mem_read = 1'b1;
                                    actions.send_cpu_data = 1'b1;
                                    actions.update_directory = 1'b1;
                                end
                                
                                default: begin
                                    error = 1'b1;
                                    err_code = 8'h01;  // Invalid transition from I
                                end
                            endcase
                        end
                        
                        DIR_SHARED: begin
                            case (req_event_r)
                                EVENT_CPU_READ, EVENT_READ_REQ: begin
                                    // S -> S (add new sharer)
                                    next_dir_state = add_sharer(current_state_r, req_node_id_r);
                                    actions.send_cpu_data = 1'b1;
                                    actions.update_directory = 1'b1;
                                end
                                
                                EVENT_CPU_WRITE, EVENT_WRITE_REQ, EVENT_UPGRADE_REQ: begin
                                    // S -> M (invalidate other sharers)
                                    next_dir_state = directory_write_transition(current_state_r, req_node_id_r);
                                    actions.send_snoop_invalidate = 1'b1;
                                    actions.send_cpu_ack = 1'b1;
                                    actions.update_directory = 1'b1;
                                    
                                    // Set snoop targets (all sharers except requester)
                                    snoop_addr_r <= req_addr_r;
                                    snoop_opcode_r <= SNP_MAKE_INVALID;
                                    snoop_targets_r <= current_state_r.sharer_mask & ~(16'h0001 << req_node_id_r);
                                    snoop_valid_r <= 1'b1;
                                end
                                
                                EVENT_CPU_EVICT: begin
                                    // S -> S or S -> I (remove sharer)
                                    next_dir_state = remove_sharer(current_state_r, req_node_id_r);
                                    actions.send_cpu_ack = 1'b1;
                                    actions.update_directory = 1'b1;
                                end
                                
                                default: begin
                                    error = 1'b1;
                                    err_code = 8'h02;  // Invalid transition from S
                                end
                            endcase
                        end
                        
                        DIR_EXCLUSIVE: begin
                            case (req_event_r)
                                EVENT_CPU_READ, EVENT_READ_REQ: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // E -> E (same owner)
                                        actions.send_cpu_data = 1'b1;
                                    end else begin
                                        // E -> S (add new sharer, demote owner)
                                        next_dir_state = add_sharer(current_state_r, req_node_id_r);
                                        actions.send_snoop_shared = 1'b1;
                                        actions.send_cpu_data = 1'b1;
                                        actions.update_directory = 1'b1;
                                        
                                        snoop_addr_r <= req_addr_r;
                                        snoop_opcode_r <= SNP_SHARED;
                                        snoop_targets_r <= (16'h0001 << current_state_r.owner_id);
                                        snoop_valid_r <= 1'b1;
                                    end
                                end
                                
                                EVENT_CPU_WRITE, EVENT_WRITE_REQ: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // E -> M (same owner)
                                        next_dir_state.state = DIR_MODIFIED;
                                        next_dir_state.dirty = 1'b1;
                                        actions.send_cpu_ack = 1'b1;
                                        actions.update_directory = 1'b1;
                                    end else begin
                                        // E -> M (new owner, invalidate old)
                                        next_dir_state = directory_write_transition(current_state_r, req_node_id_r);
                                        actions.send_snoop_invalidate = 1'b1;
                                        actions.send_cpu_data = 1'b1;
                                        actions.update_directory = 1'b1;
                                        
                                        snoop_addr_r <= req_addr_r;
                                        snoop_opcode_r <= SNP_MAKE_INVALID;
                                        snoop_targets_r <= (16'h0001 << current_state_r.owner_id);
                                        snoop_valid_r <= 1'b1;
                                    end
                                end
                                
                                EVENT_CPU_EVICT: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // E -> I
                                        next_dir_state = invalidate_all_sharers(current_state_r);
                                        actions.send_cpu_ack = 1'b1;
                                        actions.update_directory = 1'b1;
                                    end else begin
                                        error = 1'b1;
                                        err_code = 8'h03;  // Non-owner trying to evict
                                    end
                                end
                                
                                default: begin
                                    error = 1'b1;
                                    err_code = 8'h04;  // Invalid transition from E
                                end
                            endcase
                        end
                        
                        DIR_MODIFIED: begin
                            case (req_event_r)
                                EVENT_CPU_READ, EVENT_READ_REQ: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // M -> M (same owner)
                                        actions.send_cpu_data = 1'b1;
                                    end else begin
                                        // M -> S (writeback and share)
                                        next_dir_state = add_sharer(current_state_r, req_node_id_r);
                                        next_dir_state.state = DIR_SHARED;
                                        next_dir_state.dirty = 1'b0;
                                        actions.send_snoop_shared = 1'b1;
                                        actions.send_mem_write = 1'b1;  // Writeback
                                        actions.send_cpu_data = 1'b1;
                                        actions.update_directory = 1'b1;
                                        
                                        snoop_addr_r <= req_addr_r;
                                        snoop_opcode_r <= SNP_SHARED;
                                        snoop_targets_r <= (16'h0001 << current_state_r.owner_id);
                                        snoop_valid_r <= 1'b1;
                                    end
                                end
                                
                                EVENT_CPU_WRITE, EVENT_WRITE_REQ: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // M -> M (same owner)
                                        actions.send_cpu_ack = 1'b1;
                                    end else begin
                                        // M -> M (new owner, invalidate old)
                                        next_dir_state = directory_write_transition(current_state_r, req_node_id_r);
                                        actions.send_snoop_invalidate = 1'b1;
                                        actions.send_cpu_data = 1'b1;
                                        actions.update_directory = 1'b1;
                                        
                                        snoop_addr_r <= req_addr_r;
                                        snoop_opcode_r <= SNP_MAKE_INVALID;
                                        snoop_targets_r <= (16'h0001 << current_state_r.owner_id);
                                        snoop_valid_r <= 1'b1;
                                    end
                                end
                                
                                EVENT_WRITEBACK: begin
                                    if (req_node_id_r == current_state_r.owner_id) begin
                                        // M -> I (writeback)
                                        next_dir_state = invalidate_all_sharers(current_state_r);
                                        actions.send_mem_write = 1'b1;
                                        actions.send_cpu_ack = 1'b1;
                                        actions.update_directory = 1'b1;
                                    end else begin
                                        error = 1'b1;
                                        err_code = 8'h05;  // Non-owner trying to writeback
                                    end
                                end
                                
                                default: begin
                                    error = 1'b1;
                                    err_code = 8'h06;  // Invalid transition from M
                                end
                            endcase
                        end
                        
                        default: begin
                            error = 1'b1;
                            err_code = 8'h07;  // Unknown state
                        end
                    endcase
                    
                    // Update outputs
                    new_state_r <= next_dir_state;
                    required_actions_r <= actions;
                    state_changed_r <= (next_dir_state != current_state_r);
                    protocol_error_r <= error;
                    error_code_r <= err_code;
                end
                
                SM_SNOOP_WAIT: begin
                    // Wait for snoop completion
                    // In real implementation, would handle snoop responses
                end
                
                SM_MEM_WAIT: begin
                    // Wait for memory completion
                    // In real implementation, would handle memory responses
                end
                
                SM_RESPOND: begin
                    if (rsp_ready) begin
                        // Clear snoop valid when response is accepted
                        snoop_valid_r <= 1'b0;
                    end
                end
            endcase
        end
    end
    
    // =============================================================================
    // Assertions for Verification
    // =============================================================================
    
    `ifdef FORMAL
        // State machine should not have invalid states
        assert property (@(posedge clk) disable iff (!rst_n)
            state inside {SM_IDLE, SM_PROCESS, SM_SNOOP_WAIT, SM_MEM_WAIT, SM_RESPOND});
        
        // Protocol error should be accompanied by error code
        assert property (@(posedge clk) disable iff (!rst_n)
            protocol_error_r |-> (error_code_r != 8'h00));
        
        // Snoop valid should only be set with valid targets
        assert property (@(posedge clk) disable iff (!rst_n)
            snoop_valid_r |-> (snoop_targets_r != 16'h0000));
        
        // State changes should be accompanied by directory updates
        assert property (@(posedge clk) disable iff (!rst_n)
            state_changed_r |-> required_actions_r.update_directory);
    `endif

endmodule : mesi_state_machine