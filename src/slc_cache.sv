// =============================================================================
// System Level Cache (SLC) - 16-way Set Associative Cache
// Requirements: 4.2
// =============================================================================

import coh_noc_pkg::*;

module slc_cache #(
    parameter int CACHE_SIZE = SLC_SIZE,     // 1MB total cache size
    parameter int NUM_WAYS = SLC_WAYS,       // 16-way associative
    parameter int LINE_SIZE = 64,            // 64 bytes per cache line
    parameter int ADDR_WIDTH = 48
)(
    input  logic clk,
    input  logic rst_n,
    
    // Cache Access Interface
    input  logic                    req_valid,
    output logic                    req_ready,
    input  logic [ADDR_WIDTH-1:0]   req_addr,
    input  logic                    req_write,
    input  logic [511:0]            req_wdata,
    input  logic [63:0]             req_be,
    
    // Cache Response Interface
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic                    rsp_hit,
    output logic [511:0]            rsp_rdata,
    output logic                    rsp_dirty,
    
    // Victim/Writeback Interface
    output logic                    wb_valid,
    input  logic                    wb_ready,
    output logic [ADDR_WIDTH-1:0]   wb_addr,
    output logic [511:0]            wb_data
);

    // =============================================================================
    // Cache Parameters Calculation
    // =============================================================================
    
    localparam int SETS = CACHE_SIZE / (NUM_WAYS * LINE_SIZE);
    localparam int SET_BITS = $clog2(SETS);
    localparam int OFFSET_BITS = $clog2(LINE_SIZE);
    localparam int TAG_BITS = ADDR_WIDTH - SET_BITS - OFFSET_BITS;
    
    // =============================================================================
    // Cache Line Structure
    // =============================================================================
    
    typedef struct packed {
        logic                   valid;
        logic                   dirty;
        logic [TAG_BITS-1:0]    tag;
        logic [511:0]           data;
        logic [2:0]             lru_counter;  // LRU replacement policy
    } cache_line_t;
    
    // =============================================================================
    // Cache Storage Arrays
    // =============================================================================
    
    cache_line_t cache_array [SETS-1:0][NUM_WAYS-1:0];
    
    // =============================================================================
    // Address Decomposition
    // =============================================================================
    
    logic [TAG_BITS-1:0]    req_tag;
    logic [SET_BITS-1:0]    req_set;
    logic [OFFSET_BITS-1:0] req_offset;
    
    assign req_tag    = req_addr[ADDR_WIDTH-1:SET_BITS+OFFSET_BITS];
    assign req_set    = req_addr[SET_BITS+OFFSET_BITS-1:OFFSET_BITS];
    assign req_offset = req_addr[OFFSET_BITS-1:0];
    
    // =============================================================================
    // Cache Access State Machine
    // =============================================================================
    
    typedef enum logic [2:0] {
        IDLE,
        LOOKUP,
        HIT_RESPONSE,
        MISS_ALLOCATE,
        WRITEBACK
    } cache_state_e;
    
    cache_state_e state, next_state;
    
    // =============================================================================
    // Hit Detection and Way Selection
    // =============================================================================
    
    logic [NUM_WAYS-1:0] way_hit;
    logic [NUM_WAYS-1:0] way_valid;
    logic [$clog2(NUM_WAYS)-1:0] hit_way;
    logic [$clog2(NUM_WAYS)-1:0] victim_way;
    logic cache_hit;
    
    // Hit detection for each way
    always_comb begin
        for (int i = 0; i < NUM_WAYS; i++) begin
            way_hit[i] = cache_array[req_set][i].valid && 
                        (cache_array[req_set][i].tag == req_tag);
            way_valid[i] = cache_array[req_set][i].valid;
        end
    end
    
    assign cache_hit = |way_hit;
    
    // Priority encoder for hit way
    always_comb begin
        hit_way = 0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (way_hit[i]) begin
                hit_way = i;
                break;
            end
        end
    end
    
    // =============================================================================
    // LRU Replacement Policy
    // =============================================================================
    
    // Find victim way using LRU policy
    always_comb begin
        victim_way = 0;
        logic [2:0] max_lru = 0;
        
        // Find invalid way first
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (!cache_array[req_set][i].valid) begin
                victim_way = i;
                break;
            end
        end
        
        // If all ways valid, find LRU way
        if (&way_valid) begin
            for (int i = 0; i < NUM_WAYS; i++) begin
                if (cache_array[req_set][i].lru_counter >= max_lru) begin
                    max_lru = cache_array[req_set][i].lru_counter;
                    victim_way = i;
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
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (req_valid) begin
                    next_state = LOOKUP;
                end
            end
            
            LOOKUP: begin
                if (cache_hit) begin
                    next_state = HIT_RESPONSE;
                end else begin
                    // Check if victim way is dirty and needs writeback
                    if (cache_array[req_set][victim_way].valid && 
                        cache_array[req_set][victim_way].dirty) begin
                        next_state = WRITEBACK;
                    end else begin
                        next_state = MISS_ALLOCATE;
                    end
                end
            end
            
            HIT_RESPONSE: begin
                if (rsp_ready) begin
                    next_state = IDLE;
                end
            end
            
            WRITEBACK: begin
                if (wb_ready) begin
                    next_state = MISS_ALLOCATE;
                end
            end
            
            MISS_ALLOCATE: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // =============================================================================
    // Cache Operations
    // =============================================================================
    
    // Request ready signal
    assign req_ready = (state == IDLE);
    
    // Response signals
    assign rsp_valid = (state == HIT_RESPONSE);
    assign rsp_hit = cache_hit;
    assign rsp_rdata = cache_array[req_set][hit_way].data;
    assign rsp_dirty = cache_array[req_set][hit_way].dirty;
    
    // Writeback signals
    assign wb_valid = (state == WRITEBACK);
    assign wb_addr = {cache_array[req_set][victim_way].tag, req_set, {OFFSET_BITS{1'b0}}};
    assign wb_data = cache_array[req_set][victim_way].data;
    
    // =============================================================================
    // Cache Array Updates
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize cache array
            for (int i = 0; i < SETS; i++) begin
                for (int j = 0; j < NUM_WAYS; j++) begin
                    cache_array[i][j].valid <= 1'b0;
                    cache_array[i][j].dirty <= 1'b0;
                    cache_array[i][j].tag <= '0;
                    cache_array[i][j].data <= '0;
                    cache_array[i][j].lru_counter <= '0;
                end
            end
        end else begin
            case (state)
                HIT_RESPONSE: begin
                    if (rsp_ready) begin
                        // Update LRU counters on hit
                        for (int i = 0; i < NUM_WAYS; i++) begin
                            if (i == hit_way) begin
                                cache_array[req_set][i].lru_counter <= 3'b000;  // Most recently used
                            end else if (cache_array[req_set][i].lru_counter < cache_array[req_set][hit_way].lru_counter) begin
                                cache_array[req_set][i].lru_counter <= cache_array[req_set][i].lru_counter + 1;
                            end
                        end
                        
                        // Handle write hit
                        if (req_write) begin
                            cache_array[req_set][hit_way].dirty <= 1'b1;
                            // Apply byte enables to write data
                            for (int i = 0; i < 64; i++) begin
                                if (req_be[i]) begin
                                    cache_array[req_set][hit_way].data[i*8 +: 8] <= req_wdata[i*8 +: 8];
                                end
                            end
                        end
                    end
                end
                
                MISS_ALLOCATE: begin
                    // Allocate new cache line
                    cache_array[req_set][victim_way].valid <= 1'b1;
                    cache_array[req_set][victim_way].tag <= req_tag;
                    cache_array[req_set][victim_way].lru_counter <= 3'b000;  // Most recently used
                    
                    // Update LRU counters for other ways
                    for (int i = 0; i < NUM_WAYS; i++) begin
                        if (i != victim_way) begin
                            cache_array[req_set][i].lru_counter <= cache_array[req_set][i].lru_counter + 1;
                        end
                    end
                    
                    if (req_write) begin
                        cache_array[req_set][victim_way].dirty <= 1'b1;
                        // Apply byte enables to write data
                        for (int i = 0; i < 64; i++) begin
                            if (req_be[i]) begin
                                cache_array[req_set][victim_way].data[i*8 +: 8] <= req_wdata[i*8 +: 8];
                            end else begin
                                cache_array[req_set][victim_way].data[i*8 +: 8] <= 8'h00;  // Clear non-written bytes
                            end
                        end
                    end else begin
                        cache_array[req_set][victim_way].dirty <= 1'b0;
                        cache_array[req_set][victim_way].data <= '0;  // Will be filled by memory response
                    end
                end
                
                WRITEBACK: begin
                    if (wb_ready) begin
                        // Clear victim way after writeback
                        cache_array[req_set][victim_way].valid <= 1'b0;
                        cache_array[req_set][victim_way].dirty <= 1'b0;
                    end
                end
            endcase
        end
    end
    
    // =============================================================================
    // Assertions for Verification
    // =============================================================================
    
    `ifdef FORMAL
        // Cache hit should only occur when line is valid and tag matches
        assert property (@(posedge clk) disable iff (!rst_n)
            cache_hit |-> (cache_array[req_set][hit_way].valid && 
                          cache_array[req_set][hit_way].tag == req_tag));
        
        // LRU counter should not exceed maximum value
        assert property (@(posedge clk) disable iff (!rst_n)
            cache_array[req_set][victim_way].lru_counter <= (NUM_WAYS - 1));
        
        // Valid cache line should have proper tag
        assert property (@(posedge clk) disable iff (!rst_n)
            cache_array[req_set][hit_way].valid |-> 
            cache_array[req_set][hit_way].tag != '0 || req_tag == '0);
    `endif

endmodule : slc_cache