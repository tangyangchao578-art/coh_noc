// =============================================================================
// Retransmit Controller - Flit Retransmission and Recovery Mechanism
// Task 13.2: Implement retransmission and recovery mechanisms
// =============================================================================

import coh_noc_pkg::*;

module retransmit_controller #(
    parameter int BUFFER_DEPTH = 32,
    parameter int MAX_RETRIES = 3,
    parameter int RETRY_TIMEOUT = 100
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Original flit transmission interface
    input  logic        tx_valid,
    input  flit_u       tx_flit,
    input  logic [1:0]  tx_vc_id,
    output logic        tx_ready,
    
    // Actual network transmission interface
    output logic        net_tx_valid,
    output flit_u       net_tx_flit,
    output logic [1:0]  net_tx_vc_id,
    input  logic        net_tx_ready,
    
    // Error indication from error detection
    input  logic        error_detected,
    input  logic [11:0] error_txn_id,
    input  logic [7:0]  error_code,
    
    // Acknowledgment interface
    input  logic        ack_valid,
    input  logic [11:0] ack_txn_id,
    
    // Status outputs
    output logic        retransmit_active,
    output logic [7:0]  pending_count,
    output logic [7:0]  retry_count
);

    // =============================================================================
    // Retransmit Buffer Entry Structure
    // =============================================================================
    
    typedef struct packed {
        logic        valid;
        flit_u       flit;
        logic [1:0]  vc_id;
        logic [11:0] txn_id;
        logic [7:0]  retry_attempts;
        logic [15:0] timer;
        logic        acked;
    } retx_entry_t;
    
    // Retransmit buffer
    retx_entry_t retx_buffer [BUFFER_DEPTH-1:0];
    
    // Buffer management
    logic [5:0] write_ptr;
    logic [5:0] read_ptr;
    logic [7:0] buffer_count;
    logic       buffer_full;
    logic       buffer_empty;
    
    assign buffer_full = (buffer_count >= BUFFER_DEPTH);
    assign buffer_empty = (buffer_count == 0);
    assign pending_count = buffer_count;
    
    // =============================================================================
    // State Machine for Retransmission Control
    // =============================================================================
    
    typedef enum logic [2:0] {
        IDLE,
        TRANSMIT,
        WAIT_ACK,
        RETRANSMIT,
        ERROR_RECOVERY
    } state_t;
    
    state_t state, next_state;
    
    // Current transmission tracking
    logic [5:0] current_entry;
    logic [7:0] total_retries;
    
    assign retry_count = total_retries;
    assign retransmit_active = (state == RETRANSMIT || state == ERROR_RECOVERY);
    
    // =============================================================================
    // Buffer Write Logic - Store Outgoing Flits
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            write_ptr <= 6'h0;
            
            for (int i = 0; i < BUFFER_DEPTH; i++) begin
                retx_buffer[i].valid <= 1'b0;
                retx_buffer[i].flit <= '0;
                retx_buffer[i].vc_id <= 2'b00;
                retx_buffer[i].txn_id <= 12'h0;
                retx_buffer[i].retry_attempts <= 8'h0;
                retx_buffer[i].timer <= 16'h0;
                retx_buffer[i].acked <= 1'b0;
            end
        end else begin
            // Store new flit for potential retransmission
            if (tx_valid && tx_ready && !buffer_full) begin
                retx_buffer[write_ptr].valid <= 1'b1;
                retx_buffer[write_ptr].flit <= tx_flit;
                retx_buffer[write_ptr].vc_id <= tx_vc_id;
                retx_buffer[write_ptr].txn_id <= tx_flit.req.txn_id;
                retx_buffer[write_ptr].retry_attempts <= 8'h0;
                retx_buffer[write_ptr].timer <= 16'h0;
                retx_buffer[write_ptr].acked <= 1'b0;
                
                write_ptr <= write_ptr + 1;
            end
            
            // Update timers for all pending entries
            for (int i = 0; i < BUFFER_DEPTH; i++) begin
                if (retx_buffer[i].valid && !retx_buffer[i].acked) begin
                    retx_buffer[i].timer <= retx_buffer[i].timer + 1;
                end
            end
        end
    end
    
    // =============================================================================
    // Acknowledgment Processing
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset handled in buffer write logic
        end else begin
            // Mark entry as acknowledged
            if (ack_valid) begin
                for (int i = 0; i < BUFFER_DEPTH; i++) begin
                    if (retx_buffer[i].valid && 
                        retx_buffer[i].txn_id == ack_txn_id) begin
                        retx_buffer[i].acked <= 1'b1;
                    end
                end
            end
        end
    end
    
    // =============================================================================
    // Error Detection and Retry Logic
    // =============================================================================
    
    logic retry_needed;
    logic [5:0] retry_entry_idx;
    
    always_comb begin
        retry_needed = 1'b0;
        retry_entry_idx = 6'h0;
        
        // Check for errors or timeouts requiring retry
        if (error_detected) begin
            // Find entry matching error transaction ID
            for (int i = 0; i < BUFFER_DEPTH; i++) begin
                if (retx_buffer[i].valid && 
                    !retx_buffer[i].acked &&
                    retx_buffer[i].txn_id == error_txn_id &&
                    retx_buffer[i].retry_attempts < MAX_RETRIES) begin
                    retry_needed = 1'b1;
                    retry_entry_idx = i;
                end
            end
        end else begin
            // Check for timeout-based retries
            for (int i = 0; i < BUFFER_DEPTH; i++) begin
                if (retx_buffer[i].valid && 
                    !retx_buffer[i].acked &&
                    retx_buffer[i].timer >= RETRY_TIMEOUT &&
                    retx_buffer[i].retry_attempts < MAX_RETRIES) begin
                    retry_needed = 1'b1;
                    retry_entry_idx = i;
                end
            end
        end
    end
    
    // =============================================================================
    // State Machine Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            current_entry <= 6'h0;
            total_retries <= 8'h0;
        end else begin
            state <= next_state;
            
            // Track retransmission attempts
            if (state == RETRANSMIT && net_tx_ready) begin
                total_retries <= total_retries + 1;
                retx_buffer[current_entry].retry_attempts <= 
                    retx_buffer[current_entry].retry_attempts + 1;
                retx_buffer[current_entry].timer <= 16'h0;  // Reset timer
            end
            
            // Update current entry for retransmission
            if (retry_needed) begin
                current_entry <= retry_entry_idx;
            end
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (retry_needed) begin
                    next_state = RETRANSMIT;
                end else if (tx_valid && !buffer_full) begin
                    next_state = TRANSMIT;
                end
            end
            
            TRANSMIT: begin
                if (net_tx_ready) begin
                    next_state = WAIT_ACK;
                end
            end
            
            WAIT_ACK: begin
                if (retry_needed) begin
                    next_state = RETRANSMIT;
                end else if (tx_valid && !buffer_full) begin
                    next_state = TRANSMIT;
                end else begin
                    next_state = IDLE;
                end
            end
            
            RETRANSMIT: begin
                if (net_tx_ready) begin
                    if (retx_buffer[current_entry].retry_attempts >= MAX_RETRIES-1) begin
                        next_state = ERROR_RECOVERY;
                    end else begin
                        next_state = WAIT_ACK;
                    end
                end
            end
            
            ERROR_RECOVERY: begin
                // Mark failed entry as invalid and move on
                next_state = IDLE;
            end
            
            default: next_state = IDLE;
        endcase
    end
    
    // =============================================================================
    // Output Logic
    // =============================================================================
    
    always_comb begin
        // Default values
        net_tx_valid = 1'b0;
        net_tx_flit = '0;
        net_tx_vc_id = 2'b00;
        tx_ready = 1'b0;
        
        case (state)
            IDLE: begin
                tx_ready = !buffer_full;
            end
            
            TRANSMIT: begin
                net_tx_valid = tx_valid;
                net_tx_flit = tx_flit;
                net_tx_vc_id = tx_vc_id;
                tx_ready = net_tx_ready && !buffer_full;
            end
            
            WAIT_ACK: begin
                tx_ready = !buffer_full;
            end
            
            RETRANSMIT: begin
                net_tx_valid = 1'b1;
                net_tx_flit = retx_buffer[current_entry].flit;
                net_tx_vc_id = retx_buffer[current_entry].vc_id;
                tx_ready = 1'b0;  // Block new transmissions during retry
            end
            
            ERROR_RECOVERY: begin
                tx_ready = 1'b0;
            end
            
            default: begin
                tx_ready = 1'b0;
            end
        endcase
    end
    
    // =============================================================================
    // Buffer Cleanup - Remove Acknowledged Entries
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            read_ptr <= 6'h0;
            buffer_count <= 8'h0;
        end else begin
            // Remove acknowledged entries from buffer
            if (retx_buffer[read_ptr].valid && retx_buffer[read_ptr].acked) begin
                retx_buffer[read_ptr].valid <= 1'b0;
                read_ptr <= read_ptr + 1;
                if (buffer_count > 0) begin
                    buffer_count <= buffer_count - 1;
                end
            end
            
            // Add new entries to count
            if (tx_valid && tx_ready && !buffer_full) begin
                buffer_count <= buffer_count + 1;
            end
            
            // Handle error recovery - remove failed entries
            if (state == ERROR_RECOVERY) begin
                retx_buffer[current_entry].valid <= 1'b0;
                if (buffer_count > 0) begin
                    buffer_count <= buffer_count - 1;
                end
            end
        end
    end

endmodule : retransmit_controller
