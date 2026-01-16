// =============================================================================
// L1 Cache - Local Cache for RN-F Node
// Requirements: 5.2
// =============================================================================

import coh_noc_pkg::*;

module l1_cache #(
    parameter CACHE_SIZE = 64*1024,  // 64KB
    parameter NUM_WAYS = 4,          // 4-way associative
    parameter LINE_SIZE = 64         // 64-byte cache line
)(
    input  logic clk,
    input  logic rst_n,
    
    // Cache Access Interface
    input  logic        access_valid,
    output logic        access_ready,
    input  logic        access_read,   // 1=read, 0=write
    input  logic [47:0] access_addr,
    input  logic [511:0] access_wdata,
    input  logic [63:0] access_be,     // Byte enable
    output logic        access_hit,
    output logic [511:0] access_rdata,
    output logic [3:0]  access_state,  // MESI state
    
    // Cache Line Fill Interface
    input  logic        fill_valid,
    output logic        fill_ready,
    input  logic [47:0] fill_addr,
    input  logic [511:0] fill_data,
    input  logic [3:0]  fill_state,    // MESI state
    
    // Cache Line Eviction Interface
    output logic        evict_valid,
    input  logic        evict_ready,
    output logic [47:0] evict_addr,
    output logic [511:0] evict_data,
    output logic        evict_dirty,
    
    // Snoop Interface
    input  logic        snoop_valid,
    output logic        snoop_ready,
    input  logic [47:0] snoop_addr,
    input  snp_opcode_e snoop_opcode,
    output logic        snoop_hit,
    output logic [3:0]  snoop_state,
    output logic [511:0] snoop_data
);

    // =============================================================================
    // Cache Parameters
    // =============================================================================
    
    localparam int NUM_SETS = CACHE_SIZE / (LINE_SIZE * NUM_WAYS);
    localparam int INDEX_WIDTH = $clog2(NUM_SETS);
    localparam int OFFSET_WIDTH = $clog2(LINE_SIZE);
    localparam int TAG_WIDTH = 48 - INDEX_WIDTH - OFFSET_WIDTH;
    
    // =============================================================================
    // MESI State Definitions
    // =============================================================================
    
    typedef enum logic [3:0] {
        MESI_INVALID   = 4'h0,
        MESI_SHARED    = 4'h1,
        MESI_EXCLUSIVE = 4'h2,
        MESI_MODIFIED  = 4'h3
    } mesi_state_e;
    
    // =============================================================================
    // Cache Line Structure
    // =============================================================================
    
    typedef struct packed {
        logic               valid;
        logic               dirty;
        mesi_state_e        state;
        logic [TAG_WIDTH-1:0] tag;
        logic [511:0]       data;
        logic [2:0]         lru_counter;  // LRU replacement policy
    } cache_line_t;
    
    // =============================================================================
    // Cache Storage
    // =============================================================================
    
    cache_line_t cache_array [NUM_SETS-1:0][NUM_WAYS-1:0];
    
    // =============================================================================
    // Address Decomposition
    // =============================================================================
    
    logic [TAG_WIDTH-1:0]    access_tag;
    logic [INDEX_WIDTH-1:0]  access_index;
    logic [OFFSET_WIDTH-1:0] access_offset;
    
    logic [TAG_WIDTH-1:0]    fill_tag;
    logic [INDEX_WIDTH-1:0]  fill_index;
    
    logic [TAG_WIDTH-1:0]    snoop_tag;
    logic [INDEX_WIDTH-1:0]  snoop_index;
    
    assign access_tag    = access_addr[47:47-TAG_WIDTH+1];
    assign access_index  = access_addr[47-TAG_WIDTH:OFFSET_WIDTH];
    assign access_offset = access_addr[OFFSET_WIDTH-1:0];
    
    assign fill_tag   = fill_addr[47:47-TAG_WIDTH+1];
    assign fill_index = fill_addr[47-TAG_WIDTH:OFFSET_WIDTH];
    
    assign snoop_tag   = snoop_addr[47:47-TAG_WIDTH+1];
    assign snoop_index = snoop_addr[47-TAG_WIDTH:OFFSET_WIDTH];
    
    // =============================================================================
    // Cache Lookup Logic
    // =============================================================================
    
    logic [NUM_WAYS-1:0] access_way_hit;
    logic [NUM_WAYS-1:0] snoop_way_hit;
    logic [$clog2(NUM_WAYS)-1:0] access_hit_way;
    logic [$clog2(NUM_WAYS)-1:0] snoop_hit_way;
    
    always_comb begin
        access_way_hit = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (cache_array[access_index][i].valid && 
                cache_array[access_index][i].tag == access_tag) begin
                access_way_hit[i] = 1'b1;
            end
        end
    end
    
    always_comb begin
        snoop_way_hit = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (cache_array[snoop_index][i].valid && 
                cache_array[snoop_index][i].tag == snoop_tag) begin
                snoop_way_hit[i] = 1'b1;
            end
        end
    end
    
    // Priority encoder for hit way
    always_comb begin
        access_hit_way = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (access_way_hit[i]) access_hit_way = i;
        end
    end
    
    always_comb begin
        snoop_hit_way = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (snoop_way_hit[i]) snoop_hit_way = i;
        end
    end
    
    assign access_hit = |access_way_hit;
    assign snoop_hit  = |snoop_way_hit;
    
    // =============================================================================
    // Cache Access Response
    // =============================================================================
    
    assign access_ready = 1'b1;  // Always ready for access
    assign access_rdata = access_hit ? cache_array[access_index][access_hit_way].data : '0;
    assign access_state = access_hit ? cache_array[access_index][access_hit_way].state : MESI_INVALID;
    
    // =============================================================================
    // Snoop Response
    // =============================================================================
    
    assign snoop_ready = 1'b1;  // Always ready for snoop
    assign snoop_state = snoop_hit ? cache_array[snoop_index][snoop_hit_way].state : MESI_INVALID;
    assign snoop_data  = snoop_hit ? cache_array[snoop_index][snoop_hit_way].data : '0;
    
    // =============================================================================
    // LRU Replacement Policy
    // =============================================================================
    
    logic [$clog2(NUM_WAYS)-1:0] lru_way;
    
    always_comb begin
        lru_way = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (!cache_array[fill_index][i].valid) begin
                lru_way = i;
                i = NUM_WAYS;  // Exit loop
            end else if (cache_array[fill_index][i].lru_counter >= 3'b111) begin
                lru_way = i;
            end
        end
    end
    
    // =============================================================================
    // Cache Fill Logic
    // =============================================================================
    
    assign fill_ready = 1'b1;  // Always ready for fill
    
    // =============================================================================
    // Cache Eviction Logic
    // =============================================================================
    
    logic evict_pending;
    
    assign evict_valid = evict_pending;
    assign evict_addr  = {cache_array[fill_index][lru_way].tag, fill_index, {OFFSET_WIDTH{1'b0}}};
    assign evict_data  = cache_array[fill_index][lru_way].data;
    assign evict_dirty = cache_array[fill_index][lru_way].dirty;
    
    // =============================================================================
    // Sequential Logic
    // =============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize cache to invalid state
            for (int i = 0; i < NUM_SETS; i++) begin
                for (int j = 0; j < NUM_WAYS; j++) begin
                    cache_array[i][j].valid <= 1'b0;
                    cache_array[i][j].dirty <= 1'b0;
                    cache_array[i][j].state <= MESI_INVALID;
                    cache_array[i][j].tag <= '0;
                    cache_array[i][j].data <= '0;
                    cache_array[i][j].lru_counter <= '0;
                end
            end
            evict_pending <= 1'b0;
        end else begin
            // Handle cache access (read/write)
            if (access_valid && access_ready) begin
                if (access_hit) begin
                    if (!access_read) begin
                        // Write hit - update data and mark dirty
                        for (int i = 0; i < 64; i++) begin
                            if (access_be[i]) begin
                                cache_array[access_index][access_hit_way].data[i*8 +: 8] <= access_wdata[i*8 +: 8];
                            end
                        end
                        cache_array[access_index][access_hit_way].dirty <= 1'b1;
                        cache_array[access_index][access_hit_way].state <= MESI_MODIFIED;
                    end
                    // Update LRU
                    cache_array[access_index][access_hit_way].lru_counter <= '0;
                    for (int i = 0; i < NUM_WAYS; i++) begin
                        if (i != access_hit_way && cache_array[access_index][i].valid) begin
                            cache_array[access_index][i].lru_counter <= 
                                cache_array[access_index][i].lru_counter + 1;
                        end
                    end
                end
            end
            
            // Handle cache fill
            if (fill_valid && fill_ready) begin
                // Check if eviction is needed
                if (cache_array[fill_index][lru_way].valid && 
                    cache_array[fill_index][lru_way].dirty) begin
                    evict_pending <= 1'b1;
                end
                
                // Fill cache line
                if (!evict_pending || (evict_pending && evict_ready)) begin
                    cache_array[fill_index][lru_way].valid <= 1'b1;
                    cache_array[fill_index][lru_way].dirty <= 1'b0;
                    cache_array[fill_index][lru_way].state <= fill_state;
                    cache_array[fill_index][lru_way].tag <= fill_tag;
                    cache_array[fill_index][lru_way].data <= fill_data;
                    cache_array[fill_index][lru_way].lru_counter <= '0;
                    
                    // Update LRU for other ways
                    for (int i = 0; i < NUM_WAYS; i++) begin
                        if (i != lru_way && cache_array[fill_index][i].valid) begin
                            cache_array[fill_index][i].lru_counter <= 
                                cache_array[fill_index][i].lru_counter + 1;
                        end
                    end
                    
                    evict_pending <= 1'b0;
                end
            end
            
            // Handle snoop requests
            if (snoop_valid && snoop_ready && snoop_hit) begin
                case (snoop_opcode)
                    SNP_SHARED: begin
                        // Transition to Shared state
                        if (cache_array[snoop_index][snoop_hit_way].state == MESI_EXCLUSIVE ||
                            cache_array[snoop_index][snoop_hit_way].state == MESI_MODIFIED) begin
                            cache_array[snoop_index][snoop_hit_way].state <= MESI_SHARED;
                            cache_array[snoop_index][snoop_hit_way].dirty <= 1'b0;
                        end
                    end
                    SNP_CLEAN, SNP_CLEAN_INVALID, SNP_MAKE_INVALID, SNP_UNIQUE: begin
                        // Invalidate cache line
                        cache_array[snoop_index][snoop_hit_way].valid <= 1'b0;
                        cache_array[snoop_index][snoop_hit_way].state <= MESI_INVALID;
                    end
                    default: begin
                        // No state change for other snoop types
                    end
                endcase
            end
        end
    end

endmodule : l1_cache
