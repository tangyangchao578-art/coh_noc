// =============================================================================
// coh_noc Types - Additional Type Definitions and Utility Functions
// =============================================================================

import coh_noc_pkg::*;

// =============================================================================
// Utility Functions for Flit Handling
// =============================================================================

// Function to pack REQ flit data
function automatic req_flit_t pack_req_flit(
    input req_opcode_e opcode,
    input logic [47:0] addr,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [2:0]  size,
    input logic [2:0]  mem_attr,
    input logic [3:0]  qos,
    input logic        ns,
    input logic        likely_shared,
    input logic        allow_retry,
    input logic        order
);
    req_flit_t flit;
    flit.opcode       = opcode;
    flit.addr         = addr;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.tgt_id       = tgt_id;
    flit.size         = size;
    flit.mem_attr     = mem_attr;
    flit.qos          = qos;
    flit.ns           = ns;
    flit.likely_shared = likely_shared;
    flit.allow_retry  = allow_retry;
    flit.order        = order;
    flit.pcrd_type    = 2'b00;
    flit.trace_tag    = 8'h00;
    flit.reserved     = 8'h00;
    return flit;
endfunction

// Function to pack RSP flit data
function automatic rsp_flit_t pack_rsp_flit(
    input rsp_opcode_e opcode,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [7:0]  dbid,
    input logic [1:0]  resp,
    input logic [1:0]  fwd_state
);
    rsp_flit_t flit;
    flit.opcode       = opcode;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.tgt_id       = tgt_id;
    flit.dbid         = dbid;
    flit.resp         = resp;
    flit.fwd_state    = fwd_state;
    flit.data_pull    = 2'b00;
    flit.pcrd_type    = 2'b00;
    flit.trace_tag    = 8'h00;
    flit.reserved     = 32'h00000000;
    return flit;
endfunction

// Function to pack DAT flit data
function automatic dat_flit_t pack_dat_flit(
    input dat_opcode_e opcode,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [7:0]  home_node_id,
    input logic [7:0]  dbid,
    input logic [511:0] data,
    input logic [63:0] be,
    input logic [2:0]  data_id,
    input logic [1:0]  resp
);
    dat_flit_t flit;
    flit.opcode       = opcode;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.tgt_id       = tgt_id;
    flit.home_node_id = home_node_id;
    flit.dbid         = dbid;
    flit.data         = data;
    flit.be           = be;
    flit.data_id      = data_id;
    flit.resp         = resp;
    flit.fwd_state    = 2'b00;
    flit.data_pull    = 2'b00;
    flit.ccid         = 2'b00;
    flit.data_check   = 2'b00;
    flit.poison       = 2'b00;
    flit.trace_tag    = 8'h00;
    flit.data_check_bits = 64'h0000000000000000;
    flit.reserved     = 16'h0000;
    return flit;
endfunction

// Function to pack SNP flit data
function automatic snp_flit_t pack_snp_flit(
    input snp_opcode_e opcode,
    input logic [47:3] addr,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  fwd_txn_id,
    input logic [7:0]  fwd_node_id
);
    snp_flit_t flit;
    flit.opcode       = opcode;
    flit.addr         = addr;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.fwd_txn_id   = fwd_txn_id;
    flit.fwd_node_id  = fwd_node_id;
    flit.do_not_goto_sd = 1'b0;
    flit.ret_to_src   = 1'b0;
    flit.trace_tag    = 8'h00;
    flit.reserved     = 16'h0000;
    return flit;
endfunction

// Function to extract virtual channel from opcode
function automatic virtual_channel_e get_virtual_channel_from_req(input req_opcode_e opcode);
    return VC_REQ;
endfunction

function automatic virtual_channel_e get_virtual_channel_from_rsp(input rsp_opcode_e opcode);
    return VC_RSP;
endfunction

function automatic virtual_channel_e get_virtual_channel_from_dat(input dat_opcode_e opcode);
    return VC_DAT;
endfunction

function automatic virtual_channel_e get_virtual_channel_from_snp(input snp_opcode_e opcode);
    return VC_SNP;
endfunction

// Function to check if SNP opcode is a forward snoop (for DCT)
function automatic logic is_snp_forward(input snp_opcode_e opcode);
    case (opcode)
        SNP_FWD_SHARED, SNP_FWD_CLEAN, SNP_FWD_ONCE, SNP_FWD_NOT_SHARED_DIRTY,
        SNP_FWD_UNIQUE, SNP_FWD_CLEAN_SHARED, SNP_FWD_CLEAN_INVALID, SNP_FWD_MAKE_INVALID:
            return 1'b1;
        default:
            return 1'b0;
    endcase
endfunction

// Function to check if REQ opcode carries data
function automatic logic req_has_data(input req_opcode_e opcode);
    case (opcode)
        REQ_WRITE_BACK_FULL, REQ_WRITE_CLEAN_FULL, REQ_WRITE_UNIQUE_FULL, 
        REQ_WRITE_UNIQUE_PTL, REQ_WRITE_NO_SNOOP_FULL, REQ_WRITE_NO_SNOOP_PTL,
        REQ_ATOMIC_STORE, REQ_ATOMIC_SWAP, REQ_ATOMIC_COMPARE:
            return 1'b1;
        default:
            return 1'b0;
    endcase
endfunction

// Function to check if RSP opcode carries data
function automatic logic rsp_has_data(input rsp_opcode_e opcode);
    case (opcode)
        RSP_COMP_DATA, RSP_DATA_SEPDATA:
            return 1'b1;
        default:
            return 1'b0;
    endcase
endfunction

// Function to calculate Manhattan distance for routing
function automatic logic [7:0] manhattan_distance(
    input coord_t src,
    input coord_t dst
);
    logic [7:0] x_dist, y_dist;
    x_dist = (src.x > dst.x) ? (src.x - dst.x) : (dst.x - src.x);
    y_dist = (src.y > dst.y) ? (src.y - dst.y) : (dst.y - src.y);
    return x_dist + y_dist;
endfunction

// Function to get next hop in X-Y routing
function automatic coord_t get_next_hop(
    input coord_t current,
    input coord_t target
);
    coord_t next_hop;
    
    // X-Y Dimension Order Routing
    if (current.x != target.x) begin
        // Route in X dimension first
        next_hop.x = (current.x < target.x) ? current.x + 1 : current.x - 1;
        next_hop.y = current.y;
    end else if (current.y != target.y) begin
        // Route in Y dimension
        next_hop.x = current.x;
        next_hop.y = (current.y < target.y) ? current.y + 1 : current.y - 1;
    end else begin
        // Already at target
        next_hop = current;
    end
    
    return next_hop;
endfunction

// =============================================================================
// Directory State Management Functions (Requirements 7.1, 7.2, 4.4)
// =============================================================================

// Function to initialize a directory entry
function automatic directory_entry_t init_directory_entry();
    directory_entry_t entry;
    entry.state = DIR_INVALID;
    entry.sharer_mask = 16'h0000;
    entry.owner_id = 8'h00;
    entry.dirty = 1'b0;
    return entry;
endfunction

// Function to add a sharer to directory entry
function automatic directory_entry_t add_sharer(
    input directory_entry_t entry,
    input logic [7:0] node_id
);
    directory_entry_t new_entry;
    logic [15:0] node_mask;
    
    new_entry = entry;
    
    // Add node to sharer mask using bit manipulation
    if (node_id < 16) begin
        node_mask = 16'h0001 << node_id;
        new_entry.sharer_mask = new_entry.sharer_mask | node_mask;
    end
    
    // Update state based on number of sharers
    if (new_entry.state == DIR_INVALID) begin
        new_entry.state = DIR_EXCLUSIVE;
        new_entry.owner_id = node_id;
    end else if (new_entry.state == DIR_EXCLUSIVE) begin
        new_entry.state = DIR_SHARED;
    end
    
    return new_entry;
endfunction

// Function to remove a sharer from directory entry
function automatic directory_entry_t remove_sharer(
    input directory_entry_t entry,
    input logic [7:0] node_id
);
    directory_entry_t new_entry;
    logic [15:0] node_mask;
    int sharer_count;
    
    new_entry = entry;
    
    // Remove node from sharer mask using bit manipulation
    if (node_id < 16) begin
        node_mask = 16'h0001 << node_id;
        new_entry.sharer_mask = new_entry.sharer_mask & ~node_mask;
    end
    
    // Count remaining sharers
    sharer_count = 0;
    for (int i = 0; i < 16; i++) begin
        if ((new_entry.sharer_mask >> i) & 1'b1) sharer_count++;
    end
    
    // Update state based on remaining sharers
    if (sharer_count == 0) begin
        new_entry.state = DIR_INVALID;
        new_entry.owner_id = 8'h00;
        new_entry.dirty = 1'b0;
    end else if (sharer_count == 1) begin
        new_entry.state = DIR_EXCLUSIVE;
        // Find the remaining sharer
        for (int i = 0; i < 16; i++) begin
            if ((new_entry.sharer_mask >> i) & 1'b1) begin
                new_entry.owner_id = i;
                i = 16; // Exit loop
            end
        end
    end
    
    return new_entry;
endfunction

// Function to transition directory state on write
function automatic directory_entry_t directory_write_transition(
    input directory_entry_t entry,
    input logic [7:0] writer_id
);
    directory_entry_t new_entry;
    logic [15:0] writer_mask;
    
    new_entry = entry;
    
    // Clear all sharers except writer using bit manipulation
    if (writer_id < 16) begin
        writer_mask = 16'h0001 << writer_id;
        new_entry.sharer_mask = writer_mask;
    end else begin
        new_entry.sharer_mask = 16'h0000;
    end
    
    // Transition to Modified state
    new_entry.state = DIR_MODIFIED;
    new_entry.owner_id = writer_id;
    new_entry.dirty = 1'b1;
    
    return new_entry;
endfunction

// Function to transition directory state on read
function automatic directory_entry_t directory_read_transition(
    input directory_entry_t entry,
    input logic [7:0] reader_id
);
    directory_entry_t new_entry;
    logic [15:0] reader_mask;
    
    new_entry = entry;
    
    // Add reader to sharers using bit manipulation
    if (reader_id < 16) begin
        reader_mask = 16'h0001 << reader_id;
        new_entry.sharer_mask = new_entry.sharer_mask | reader_mask;
    end
    
    // Update state based on current state
    case (entry.state)
        DIR_INVALID: begin
            new_entry.state = DIR_EXCLUSIVE;
            new_entry.owner_id = reader_id;
        end
        DIR_EXCLUSIVE: begin
            new_entry.state = DIR_SHARED;
        end
        DIR_MODIFIED: begin
            // Modified data needs to be written back
            new_entry.state = DIR_SHARED;
            new_entry.dirty = 1'b0;
        end
        DIR_SHARED: begin
            // Already shared, just add reader
            new_entry.state = DIR_SHARED;
        end
    endcase
    
    return new_entry;
endfunction

// Function to invalidate all sharers
function automatic directory_entry_t invalidate_all_sharers(
    input directory_entry_t entry
);
    directory_entry_t new_entry;
    
    new_entry = entry;
    new_entry.state = DIR_INVALID;
    new_entry.sharer_mask = 16'h0000;
    new_entry.owner_id = 8'h00;
    new_entry.dirty = 1'b0;
    
    return new_entry;
endfunction

// Function to check if a node is a sharer
function automatic logic is_sharer(
    input directory_entry_t entry,
    input logic [7:0] node_id
);
    logic [15:0] node_mask;
    
    if (node_id < 16) begin
        node_mask = 16'h0001 << node_id;
        return ((entry.sharer_mask & node_mask) != 16'h0000);
    end else begin
        return 1'b0;
    end
endfunction

// Function to get number of sharers
function automatic int get_sharer_count(
    input directory_entry_t entry
);
    int count;
    count = 0;
    for (int i = 0; i < 16; i++) begin
        if ((entry.sharer_mask >> i) & 1'b1) count++;
    end
    return count;
endfunction

// Function to check if directory entry is valid
function automatic logic is_directory_valid(
    input directory_entry_t entry
);
    return (entry.state != DIR_INVALID);
endfunction

// Function to check if directory entry is dirty
function automatic logic is_directory_dirty(
    input directory_entry_t entry
);
    return entry.dirty;
endfunction

// Helper function to convert directory state to string
function automatic string directory_state_to_string(
    input directory_state_e state
);
    case (state)
        DIR_INVALID:   return "DIR_INVALID";
        DIR_SHARED:    return "DIR_SHARED";
        DIR_EXCLUSIVE: return "DIR_EXCLUSIVE";
        DIR_MODIFIED:  return "DIR_MODIFIED";
        default:       return "UNKNOWN";
    endcase
endfunction
