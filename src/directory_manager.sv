// =============================================================================
// Directory Manager - Cache Coherency Directory State Management
// Requirements: 4.4, 7.1, 7.2
// =============================================================================

import coh_noc_pkg::*;

module directory_manager #(
    parameter int DIRECTORY_ENTRIES = 4096,
    parameter int ADDR_WIDTH = 48,
    parameter int NODE_ID_WIDTH = 8
)(
    input  logic clk,
    input  logic rst_n,
    
    // Directory Query Interface
    input  logic                    query_valid,
    output logic                    query_ready,
    input  logic [ADDR_WIDTH-1:0]   query_addr,
    output logic                    query_rsp_valid,
    input  logic                    query_rsp_ready,
    output directory_entry_t        query_rsp_entry,
    output logic                    query_hit,
    
    // Directory Update Interface
    input  logic                    update_valid,
    output logic                    update_ready,
    input  logic [ADDR_WIDTH-1:0]   update_addr,
    input  directory_entry_t        update_entry,
    input  logic                    update_allocate,  // Allocate new entry if miss
    
    // Directory Operation Interface
    input  logic                    op_valid,
    output logic                    op_ready,
    input  logic [ADDR_WIDTH-1:0]   op_addr,
    input  logic [NODE_ID_WIDTH-1:0] op_node_id,
    input  directory_op_e           op_type,
    output logic                    op_rsp_valid,
    input  logic                    op_rsp_ready,
    output directory_entry_t        op_rsp_entry,
    output logic                    op_success,
    
    // Eviction Interface (for directory replacement)
    output logic                    evict_valid,
    input  logic                    evict_ready,
    output logic [ADDR_WIDTH-1:0]   evict_addr,
    output directory_entry_t        evict_entry
);

    // =============================================================================
    // Directory Operation Types
    // =============================================================================
    
    typedef enum logic [2:0] {
        DIR_OP_ADD_SHARER    = 3'b000,
        DIR_OP_REMOVE_SHARER = 3'b001,
        DIR_OP_SET_EXCLUSIVE = 3'b010,
        DIR_OP_SET_MODIFIED  = 3'b011,
        DIR_OP_INVALIDATE    = 3'b100,
        DIR_OP_READ_TRANS    = 3'b101,
        DIR_OP_WRITE_TRANS   = 3'b110
    } directory_op_e;
    
    // =============================================================================
    // Directory Storage Parameters
    // =============================================================================
    
    localparam int SETS = DIRECTORY_ENTRIES / 4;  // 4-way set associative
    localparam int WAYS = 4;
    localparam int SET_BITS = $clog2(SETS);
    localparam int TAG_BITS = ADDR_WIDTH - SET_BITS - 6;  // 6 bits for 64-byte alignment
    
    // =============================================================================
    // Directory Entry Structure with Metadata
    // =============================================================================
    
    typedef struct packed {
        logic                   valid;
        logic [TAG_BITS-1:0]    tag;
        directory_entry_t       dir_entry;
        logic [1:0]             lru_counter;
    } dir_storage_entry_t;
    
    // =============================================================================
    // Directory Storage Array
    // =============================================================================
    
    dir_storage_entry_t dir_array [SETS-1:0][WAYS-1:0];
    
    // =============================================================================
    // Address Decomposition
    // =============================================================================
    
    function automatic logic [TAG_BITS-1:0] get_tag(logic [ADDR_WIDTH-1:0] addr);
        return addr[ADDR_WIDTH-1:SET_BITS+6];
    endfunction
    
    function automatic logic [SET_BITS-1:0] get_set(logic [ADDR_WIDTH-1:0] addr);
        return addr[SET_BITS+6-1:6];
    endfunction
    
    // =============================================================================
    // Directory Lookup Logic
    // =============================================================================
    
    logic [WAYS-1:0] way_hit;
    logic [WAYS-1:0] way_valid;
    logic [$clog2(WAYS)-1:0] hit_way;
    logic [$clog2(WAYS)-1:0] victim_way;
    logic dir_hit;
    
    logic [TAG_BITS-1:0] lookup_tag;
    logic [SET_BITS-1:0] lookup_set;
    
    // Current lookup address (from query, update, or operation)
    logic [ADDR_WIDTH-1:0] current_addr;
    
    always_comb begin
        // Priority: operation > update > query
        if (op_valid) begin
            current_addr = op_addr;
        end else if (update_valid) begin
            current_addr = update_addr;
        end else begin
            current_addr = query_addr;
        end
        
        lookup_tag = get_tag(current_addr);
        lookup_set = get_set(current_addr);
    end
    
    // Hit detection for each way
    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            way_hit[i] = dir_array[lookup_set][i].valid && 
                        (dir_array[lookup_set][i].tag == lookup_tag);
            way_valid[i] = dir_array[lookup_set][i].valid;
        end
    end
    
    assign dir_hit = |way_hit;
    
    // Priority encoder for hit way
    always_comb begin
        hit_way = 0;
        for (int i = 0; i < WAYS; i++) begin
            if (way_hit[i]) begin
                hit_way = i;
                break;
            end
        end
    end
    
    // =============================================================================
    // LRU Replacement Logic
    // =============================================================================
    
    always_comb begin
        victim_way = 0;
        logic [1:0] max_lru = 0;
        
        // Find invalid way first
        for (int i = 0; i < WAYS; i++) begin
            if (!dir_array[lookup_set][i].valid) begin
                victim_way = i;
                break;
            end
        end
        
        // If all ways valid, find LRU way
        if (&way_valid) begin
            for (int i = 0; i < WAYS; i++) begin
                if (dir_array[lookup_set][i].lru_counter >= max_lru) begin
                    max_lru = dir_array[lookup_set][i].lru_counter;
                    victim_way = i;
                end
            end
        end
    end
    
    // =============================================================================
    // State Machine for Directory Operations
    // =============================================================================
    
    typedef enum logic [2:0] {
        IDLE,
        QUERY_LOOKUP,
        UPDATE_WRITE,
        OP_EXECUTE,
        EVICT_PREPARE
    } dir_state_e;
    
    dir_state_e state, next_state;
    
    // Registered outputs
    logic                    query_rsp_valid_r;
    directory_entry_t        query_rsp_entry_r;
    logic                    query_hit_r;
    
    logic                    op_rsp_valid_r;
    directory_entry_t        op_rsp_entry_r;
    logic                    op_success_r;
    
    logic                    evict_valid_r;
    logic [ADDR_WIDTH-1:0]   evict_addr_r;
    directory_entry_t        evict_entry_r;
    
    // =============================================================================
    // State Machine Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (op_valid) begin
                    next_state = OP_EXECUTE;
                end else if (update_valid) begin
                    next_state = UPDATE_WRITE;
                end else if (query_valid) begin
                    next_state = QUERY_LOOKUP;
                end
            end
            
            QUERY_LOOKUP: begin
                if (query_rsp_ready) begin
                    next_state = IDLE;
                end
            end
            
            UPDATE_WRITE: begin
                // Check if we need to evict
                if (!dir_hit && update_allocate && (&way_valid) && 
                    dir_array[lookup_set][victim_way].dir_entry.state != DIR_INVALID) begin
                    next_state = EVICT_PREPARE;
                end else begin
                    next_state = IDLE;
                end
            end
            
            OP_EXECUTE: begin
                if (op_rsp_ready) begin
                    next_state = IDLE;
                end
            end
            
            EVICT_PREPARE: begin
                if (evict_ready) begin
                    next_state = IDLE;
                end
            end
        endcase
    end
    
    // =============================================================================
    // Interface Assignments
    // =============================================================================
    
    assign query_ready = (state == IDLE) && !op_valid && !update_valid;
    assign update_ready = (state == IDLE) && !op_valid;
    assign op_ready = (state == IDLE);
    
    assign query_rsp_valid = query_rsp_valid_r;
    assign query_rsp_entry = query_rsp_entry_r;
    assign query_hit = query_hit_r;
    
    assign op_rsp_valid = op_rsp_valid_r;
    assign op_rsp_entry = op_rsp_entry_r;
    assign op_success = op_success_r;
    
    assign evict_valid = evict_valid_r;
    assign evict_addr = evict_addr_r;
    assign evict_entry = evict_entry_r;
    
    // =============================================================================
    // Directory Array Updates and Operations
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize directory array
            for (int i = 0; i < SETS; i++) begin
                for (int j = 0; j < WAYS; j++) begin
                    dir_array[i][j].valid <= 1'b0;
                    dir_array[i][j].tag <= '0;
                    dir_array[i][j].dir_entry <= init_directory_entry();
                    dir_array[i][j].lru_counter <= '0;
                end
            end
            
            // Initialize registered outputs
            query_rsp_valid_r <= 1'b0;
            query_rsp_entry_r <= init_directory_entry();
            query_hit_r <= 1'b0;
            
            op_rsp_valid_r <= 1'b0;
            op_rsp_entry_r <= init_directory_entry();
            op_success_r <= 1'b0;
            
            evict_valid_r <= 1'b0;
            evict_addr_r <= '0;
            evict_entry_r <= init_directory_entry();
            
        end else begin
            case (state)
                QUERY_LOOKUP: begin
                    query_rsp_valid_r <= 1'b1;
                    query_hit_r <= dir_hit;
                    
                    if (dir_hit) begin
                        query_rsp_entry_r <= dir_array[lookup_set][hit_way].dir_entry;
                        
                        // Update LRU on hit
                        for (int i = 0; i < WAYS; i++) begin
                            if (i == hit_way) begin
                                dir_array[lookup_set][i].lru_counter <= 2'b00;
                            end else if (dir_array[lookup_set][i].lru_counter < dir_array[lookup_set][hit_way].lru_counter) begin
                                dir_array[lookup_set][i].lru_counter <= dir_array[lookup_set][i].lru_counter + 1;
                            end
                        end
                    end else begin
                        query_rsp_entry_r <= init_directory_entry();
                    end
                    
                    if (query_rsp_ready) begin
                        query_rsp_valid_r <= 1'b0;
                    end
                end
                
                UPDATE_WRITE: begin
                    if (dir_hit || update_allocate) begin
                        logic [$clog2(WAYS)-1:0] target_way;
                        target_way = dir_hit ? hit_way : victim_way;
                        
                        // Update directory entry
                        dir_array[lookup_set][target_way].valid <= 1'b1;
                        dir_array[lookup_set][target_way].tag <= lookup_tag;
                        dir_array[lookup_set][target_way].dir_entry <= update_entry;
                        dir_array[lookup_set][target_way].lru_counter <= 2'b00;
                        
                        // Update LRU counters
                        for (int i = 0; i < WAYS; i++) begin
                            if (i != target_way) begin
                                dir_array[lookup_set][i].lru_counter <= dir_array[lookup_set][i].lru_counter + 1;
                            end
                        end
                    end
                end
                
                OP_EXECUTE: begin
                    op_rsp_valid_r <= 1'b1;
                    op_success_r <= 1'b0;
                    
                    if (dir_hit) begin
                        directory_entry_t new_entry;
                        new_entry = dir_array[lookup_set][hit_way].dir_entry;
                        
                        // Perform directory operation
                        case (op_type)
                            DIR_OP_ADD_SHARER: begin
                                new_entry = add_sharer(new_entry, op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_REMOVE_SHARER: begin
                                new_entry = remove_sharer(new_entry, op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_SET_EXCLUSIVE: begin
                                new_entry.state = DIR_EXCLUSIVE;
                                new_entry.owner_id = op_node_id;
                                new_entry.sharer_mask = (16'h0001 << op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_SET_MODIFIED: begin
                                new_entry = directory_write_transition(new_entry, op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_INVALIDATE: begin
                                new_entry = invalidate_all_sharers(new_entry);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_READ_TRANS: begin
                                new_entry = directory_read_transition(new_entry, op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            DIR_OP_WRITE_TRANS: begin
                                new_entry = directory_write_transition(new_entry, op_node_id);
                                op_success_r <= 1'b1;
                            end
                            
                            default: begin
                                op_success_r <= 1'b0;
                            end
                        endcase
                        
                        // Update the entry
                        dir_array[lookup_set][hit_way].dir_entry <= new_entry;
                        op_rsp_entry_r <= new_entry;
                        
                        // Update LRU
                        for (int i = 0; i < WAYS; i++) begin
                            if (i == hit_way) begin
                                dir_array[lookup_set][i].lru_counter <= 2'b00;
                            end else if (dir_array[lookup_set][i].lru_counter < dir_array[lookup_set][hit_way].lru_counter) begin
                                dir_array[lookup_set][i].lru_counter <= dir_array[lookup_set][i].lru_counter + 1;
                            end
                        end
                        
                    end else begin
                        op_rsp_entry_r <= init_directory_entry();
                        op_success_r <= 1'b0;
                    end
                    
                    if (op_rsp_ready) begin
                        op_rsp_valid_r <= 1'b0;
                    end
                end
                
                EVICT_PREPARE: begin
                    evict_valid_r <= 1'b1;
                    evict_addr_r <= {dir_array[lookup_set][victim_way].tag, lookup_set, 6'b000000};
                    evict_entry_r <= dir_array[lookup_set][victim_way].dir_entry;
                    
                    if (evict_ready) begin
                        evict_valid_r <= 1'b0;
                        // Clear the victim way
                        dir_array[lookup_set][victim_way].valid <= 1'b0;
                        dir_array[lookup_set][victim_way].dir_entry <= init_directory_entry();
                    end
                end
                
                default: begin
                    query_rsp_valid_r <= 1'b0;
                    op_rsp_valid_r <= 1'b0;
                    evict_valid_r <= 1'b0;
                end
            endcase
        end
    end
    
    // =============================================================================
    // Assertions for Verification
    // =============================================================================
    
    `ifdef FORMAL
        // Directory hit should only occur when entry is valid and tag matches
        assert property (@(posedge clk) disable iff (!rst_n)
            dir_hit |-> (dir_array[lookup_set][hit_way].valid && 
                        dir_array[lookup_set][hit_way].tag == lookup_tag));
        
        // LRU counter should not exceed maximum value
        assert property (@(posedge clk) disable iff (!rst_n)
            dir_array[lookup_set][victim_way].lru_counter <= (WAYS - 1));
        
        // Valid directory entry should have consistent state
        assert property (@(posedge clk) disable iff (!rst_n)
            dir_array[lookup_set][hit_way].valid |-> 
            (dir_array[lookup_set][hit_way].dir_entry.state != DIR_INVALID ||
             dir_array[lookup_set][hit_way].dir_entry.sharer_mask == 16'h0000));
    `endif

endmodule : directory_manager