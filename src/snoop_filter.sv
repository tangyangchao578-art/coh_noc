// =============================================================================
// Snoop Filter - Optimizes Snoop Request Distribution
// Requirements: 4.3, 4.5
// =============================================================================

import coh_noc_pkg::*;

module snoop_filter #(
    parameter int FILTER_ENTRIES = 1024,
    parameter int ADDR_WIDTH = 48,
    parameter int NODE_ID_WIDTH = 8,
    parameter int MAX_NODES = 16
)(
    input  logic clk,
    input  logic rst_n,
    
    // Snoop Request Interface
    input  logic                    snoop_req_valid,
    output logic                    snoop_req_ready,
    input  logic [ADDR_WIDTH-1:0]   snoop_req_addr,
    input  snp_opcode_e             snoop_req_opcode,
    input  logic [NODE_ID_WIDTH-1:0] snoop_req_src,
    
    // Filtered Snoop Output Interface
    output logic                    filtered_snoop_valid,
    input  logic                    filtered_snoop_ready,
    output logic [ADDR_WIDTH-1:0]   filtered_snoop_addr,
    output snp_opcode_e             filtered_snoop_opcode,
    output logic [MAX_NODES-1:0]    filtered_snoop_targets,  // Bitmask of targets
    output logic [NODE_ID_WIDTH-1:0] filtered_snoop_src,
    
    // Cache Line Tracking Interface (from Directory)
    input  logic                    track_valid,
    input  logic [ADDR_WIDTH-1:0]   track_addr,
    input  logic [NODE_ID_WIDTH-1:0] track_node_id,
    input  track_operation_e        track_op,
    
    // Filter Statistics Interface
    output logic [31:0]             total_snoops,
    output logic [31:0]             filtered_snoops,
    output logic [31:0]             broadcast_snoops,
    
    // Configuration Interface
    input  logic                    filter_enable,
    input  logic                    broadcast_mode,  // Force broadcast all snoops
    input  logic [3:0]              filter_threshold  // Min sharers for broadcast
);

    // =============================================================================
    // Tracking Operation Types
    // =============================================================================
    
    typedef enum logic [2:0] {
        TRACK_ADD_SHARER    = 3'b000,
        TRACK_REMOVE_SHARER = 3'b001,
        TRACK_SET_EXCLUSIVE = 3'b010,
        TRACK_SET_MODIFIED  = 3'b011,
        TRACK_INVALIDATE    = 3'b100,
        TRACK_EVICT         = 3'b101
    } track_operation_e;
    
    // =============================================================================
    // Filter Entry Structure
    // =============================================================================
    
    typedef struct packed {
        logic                   valid;
        logic [ADDR_WIDTH-7:0]  tag;           // Cache line tag (64-byte aligned)
        logic [MAX_NODES-1:0]   sharer_mask;   // Nodes that have this line
        logic [1:0]             lru_counter;   // LRU replacement
        logic                   dirty;         // Any node has dirty copy
        logic [NODE_ID_WIDTH-1:0] owner_id;    // Exclusive/Modified owner
    } filter_entry_t;
    
    // =============================================================================
    // Filter Storage Parameters
    // =============================================================================
    
    localparam int SETS = FILTER_ENTRIES / 4;  // 4-way set associative
    localparam int WAYS = 4;
    localparam int SET_BITS = $clog2(SETS);
    localparam int TAG_BITS = ADDR_WIDTH - SET_BITS - 6;  // 6 bits for 64-byte alignment
    
    // =============================================================================
    // Filter Storage Array
    // =============================================================================
    
    filter_entry_t filter_array [SETS-1:0][WAYS-1:0];
    
    // =============================================================================
    // Statistics Counters
    // =============================================================================
    
    logic [31:0] total_snoops_r;
    logic [31:0] filtered_snoops_r;
    logic [31:0] broadcast_snoops_r;
    
    assign total_snoops = total_snoops_r;
    assign filtered_snoops = filtered_snoops_r;
    assign broadcast_snoops = broadcast_snoops_r;
    
    // =============================================================================
    // Address Decomposition Functions
    // =============================================================================
    
    function automatic logic [TAG_BITS-1:0] get_tag(logic [ADDR_WIDTH-1:0] addr);
        return addr[ADDR_WIDTH-1:SET_BITS+6];
    endfunction
    
    function automatic logic [SET_BITS-1:0] get_set(logic [ADDR_WIDTH-1:0] addr);
        return addr[SET_BITS+6-1:6];
    endfunction
    
    // =============================================================================
    // Filter Lookup Logic
    // =============================================================================
    
    logic [WAYS-1:0] way_hit;
    logic [WAYS-1:0] way_valid;
    logic [$clog2(WAYS)-1:0] hit_way;
    logic [$clog2(WAYS)-1:0] victim_way;
    logic filter_hit;
    
    logic [TAG_BITS-1:0] lookup_tag;
    logic [SET_BITS-1:0] lookup_set;
    logic [ADDR_WIDTH-1:0] current_addr;
    
    // Current lookup address (snoop request or tracking update)
    always_comb begin
        if (track_valid) begin
            current_addr = track_addr;
        end else begin
            current_addr = snoop_req_addr;
        end
        
        lookup_tag = get_tag(current_addr);
        lookup_set = get_set(current_addr);
    end
    
    // Hit detection for each way
    always_comb begin
        for (int i = 0; i < WAYS; i++) begin
            way_hit[i] = filter_array[lookup_set][i].valid && 
                        (filter_array[lookup_set][i].tag == lookup_tag);
            way_valid[i] = filter_array[lookup_set][i].valid;
        end
    end
    
    assign filter_hit = |way_hit;
    
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
            if (!filter_array[lookup_set][i].valid) begin
                victim_way = i;
                break;
            end
        end
        
        // If all ways valid, find LRU way
        if (&way_valid) begin
            for (int i = 0; i < WAYS; i++) begin
                if (filter_array[lookup_set][i].lru_counter >= max_lru) begin
                    max_lru = filter_array[lookup_set][i].lru_counter;
                    victim_way = i;
                end
            end
        end
    end
    
    // =============================================================================
    // Snoop Filtering State Machine
    // =============================================================================
    
    typedef enum logic [1:0] {
        SF_IDLE,
        SF_LOOKUP,
        SF_RESPOND
    } sf_state_e;
    
    sf_state_e state, next_state;
    
    // Registered outputs
    logic                    filtered_snoop_valid_r;
    logic [ADDR_WIDTH-1:0]   filtered_snoop_addr_r;
    snp_opcode_e             filtered_snoop_opcode_r;
    logic [MAX_NODES-1:0]    filtered_snoop_targets_r;
    logic [NODE_ID_WIDTH-1:0] filtered_snoop_src_r;
    
    // =============================================================================
    // State Machine Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= SF_IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            SF_IDLE: begin
                if (snoop_req_valid) begin
                    next_state = SF_LOOKUP;
                end
            end
            
            SF_LOOKUP: begin
                next_state = SF_RESPOND;
            end
            
            SF_RESPOND: begin
                if (filtered_snoop_ready) begin
                    next_state = SF_IDLE;
                end
            end
        endcase
    end
    
    // =============================================================================
    // Interface Assignments
    // =============================================================================
    
    assign snoop_req_ready = (state == SF_IDLE) && !track_valid;
    assign filtered_snoop_valid = filtered_snoop_valid_r;
    assign filtered_snoop_addr = filtered_snoop_addr_r;
    assign filtered_snoop_opcode = filtered_snoop_opcode_r;
    assign filtered_snoop_targets = filtered_snoop_targets_r;
    assign filtered_snoop_src = filtered_snoop_src_r;
    
    // =============================================================================
    // Snoop Filtering and Tracking Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize filter array
            for (int i = 0; i < SETS; i++) begin
                for (int j = 0; j < WAYS; j++) begin
                    filter_array[i][j].valid <= 1'b0;
                    filter_array[i][j].tag <= '0;
                    filter_array[i][j].sharer_mask <= '0;
                    filter_array[i][j].lru_counter <= '0;
                    filter_array[i][j].dirty <= 1'b0;
                    filter_array[i][j].owner_id <= '0;
                end
            end
            
            // Initialize outputs
            filtered_snoop_valid_r <= 1'b0;
            filtered_snoop_addr_r <= '0;
            filtered_snoop_opcode_r <= SNP_SHARED;
            filtered_snoop_targets_r <= '0;
            filtered_snoop_src_r <= '0;
            
            // Initialize statistics
            total_snoops_r <= '0;
            filtered_snoops_r <= '0;
            broadcast_snoops_r <= '0;
            
        end else begin
            // Handle tracking updates (higher priority)
            if (track_valid) begin
                logic [$clog2(WAYS)-1:0] target_way;
                target_way = filter_hit ? hit_way : victim_way;
                
                case (track_op)
                    TRACK_ADD_SHARER: begin
                        if (filter_hit) begin
                            // Add sharer to existing entry
                            if (track_node_id < MAX_NODES) begin
                                filter_array[lookup_set][target_way].sharer_mask[track_node_id] <= 1'b1;
                            end
                        end else begin
                            // Allocate new entry
                            filter_array[lookup_set][target_way].valid <= 1'b1;
                            filter_array[lookup_set][target_way].tag <= lookup_tag;
                            filter_array[lookup_set][target_way].sharer_mask <= '0;
                            if (track_node_id < MAX_NODES) begin
                                filter_array[lookup_set][target_way].sharer_mask[track_node_id] <= 1'b1;
                            end
                            filter_array[lookup_set][target_way].dirty <= 1'b0;
                            filter_array[lookup_set][target_way].owner_id <= track_node_id;
                        end
                        
                        // Update LRU
                        filter_array[lookup_set][target_way].lru_counter <= 2'b00;
                        for (int i = 0; i < WAYS; i++) begin
                            if (i != target_way && filter_array[lookup_set][i].lru_counter < 2'b11) begin
                                filter_array[lookup_set][i].lru_counter <= filter_array[lookup_set][i].lru_counter + 1;
                            end
                        end
                    end
                    
                    TRACK_REMOVE_SHARER: begin
                        if (filter_hit && track_node_id < MAX_NODES) begin
                            filter_array[lookup_set][hit_way].sharer_mask[track_node_id] <= 1'b0;
                            
                            // If no more sharers, invalidate entry
                            if (filter_array[lookup_set][hit_way].sharer_mask == (16'h0001 << track_node_id)) begin
                                filter_array[lookup_set][hit_way].valid <= 1'b0;
                            end
                        end
                    end
                    
                    TRACK_SET_EXCLUSIVE: begin
                        if (filter_hit) begin
                            filter_array[lookup_set][hit_way].sharer_mask <= '0;
                            if (track_node_id < MAX_NODES) begin
                                filter_array[lookup_set][hit_way].sharer_mask[track_node_id] <= 1'b1;
                            end
                            filter_array[lookup_set][hit_way].owner_id <= track_node_id;
                            filter_array[lookup_set][hit_way].dirty <= 1'b0;
                        end
                    end
                    
                    TRACK_SET_MODIFIED: begin
                        if (filter_hit) begin
                            filter_array[lookup_set][hit_way].sharer_mask <= '0;
                            if (track_node_id < MAX_NODES) begin
                                filter_array[lookup_set][hit_way].sharer_mask[track_node_id] <= 1'b1;
                            end
                            filter_array[lookup_set][hit_way].owner_id <= track_node_id;
                            filter_array[lookup_set][hit_way].dirty <= 1'b1;
                        end
                    end
                    
                    TRACK_INVALIDATE: begin
                        if (filter_hit) begin
                            filter_array[lookup_set][hit_way].valid <= 1'b0;
                            filter_array[lookup_set][hit_way].sharer_mask <= '0;
                        end
                    end
                    
                    TRACK_EVICT: begin
                        if (filter_hit && track_node_id < MAX_NODES) begin
                            filter_array[lookup_set][hit_way].sharer_mask[track_node_id] <= 1'b0;
                        end
                    end
                endcase
            end
            
            // Handle snoop filtering
            case (state)
                SF_LOOKUP: begin
                    logic [MAX_NODES-1:0] target_mask;
                    logic should_broadcast;
                    int sharer_count;
                    
                    // Count sharers
                    sharer_count = 0;
                    if (filter_hit) begin
                        for (int i = 0; i < MAX_NODES; i++) begin
                            if (filter_array[lookup_set][hit_way].sharer_mask[i]) begin
                                sharer_count++;
                            end
                        end
                    end
                    
                    // Determine if we should broadcast or filter
                    should_broadcast = broadcast_mode || 
                                      !filter_enable || 
                                      !filter_hit || 
                                      (sharer_count >= filter_threshold);
                    
                    // Update statistics
                    total_snoops_r <= total_snoops_r + 1;
                    
                    if (should_broadcast) begin
                        // Broadcast to all nodes except source
                        target_mask = '1;
                        if (snoop_req_src < MAX_NODES) begin
                            target_mask[snoop_req_src] = 1'b0;
                        end
                        broadcast_snoops_r <= broadcast_snoops_r + 1;
                    end else begin
                        // Filter to only known sharers
                        target_mask = filter_array[lookup_set][hit_way].sharer_mask;
                        if (snoop_req_src < MAX_NODES) begin
                            target_mask[snoop_req_src] = 1'b0;  // Don't snoop source
                        end
                        filtered_snoops_r <= filtered_snoops_r + 1;
                    end
                    
                    // Generate filtered snoop
                    filtered_snoop_valid_r <= 1'b1;
                    filtered_snoop_addr_r <= snoop_req_addr;
                    filtered_snoop_opcode_r <= snoop_req_opcode;
                    filtered_snoop_targets_r <= target_mask;
                    filtered_snoop_src_r <= snoop_req_src;
                end
                
                SF_RESPOND: begin
                    if (filtered_snoop_ready) begin
                        filtered_snoop_valid_r <= 1'b0;
                    end
                end
                
                default: begin
                    filtered_snoop_valid_r <= 1'b0;
                end
            endcase
        end
    end
    
    // =============================================================================
    // Utility Functions for External Access
    // =============================================================================
    
    // Function to check if a node is tracked as a sharer
    function automatic logic is_node_tracked(
        input logic [ADDR_WIDTH-1:0] addr,
        input logic [NODE_ID_WIDTH-1:0] node_id
    );
        logic [TAG_BITS-1:0] tag;
        logic [SET_BITS-1:0] set_idx;
        
        tag = get_tag(addr);
        set_idx = get_set(addr);
        
        for (int i = 0; i < WAYS; i++) begin
            if (filter_array[set_idx][i].valid && 
                filter_array[set_idx][i].tag == tag &&
                node_id < MAX_NODES) begin
                return filter_array[set_idx][i].sharer_mask[node_id];
            end
        end
        return 1'b0;
    endfunction
    
    // Function to get sharer count for an address
    function automatic int get_sharer_count(
        input logic [ADDR_WIDTH-1:0] addr
    );
        logic [TAG_BITS-1:0] tag;
        logic [SET_BITS-1:0] set_idx;
        int count;
        
        tag = get_tag(addr);
        set_idx = get_set(addr);
        count = 0;
        
        for (int i = 0; i < WAYS; i++) begin
            if (filter_array[set_idx][i].valid && 
                filter_array[set_idx][i].tag == tag) begin
                for (int j = 0; j < MAX_NODES; j++) begin
                    if (filter_array[set_idx][i].sharer_mask[j]) begin
                        count++;
                    end
                end
                break;
            end
        end
        return count;
    endfunction
    
    // =============================================================================
    // Assertions for Verification
    // =============================================================================
    
    `ifdef FORMAL
        // Filter hit should only occur when entry is valid and tag matches
        assert property (@(posedge clk) disable iff (!rst_n)
            filter_hit |-> (filter_array[lookup_set][hit_way].valid && 
                           filter_array[lookup_set][hit_way].tag == lookup_tag));
        
        // Filtered targets should be subset of tracked sharers when filtering is enabled
        assert property (@(posedge clk) disable iff (!rst_n)
            (filtered_snoop_valid && filter_enable && filter_hit && !broadcast_mode) |->
            ((filtered_snoop_targets & filter_array[lookup_set][hit_way].sharer_mask) == 
             filtered_snoop_targets));
        
        // Statistics should be monotonically increasing
        assert property (@(posedge clk) disable iff (!rst_n)
            total_snoops >= $past(total_snoops));
        
        // Sum of filtered and broadcast should not exceed total
        assert property (@(posedge clk) disable iff (!rst_n)
            (filtered_snoops + broadcast_snoops) <= total_snoops);
    `endif

endmodule : snoop_filter