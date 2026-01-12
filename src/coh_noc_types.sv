// =============================================================================
// coh_noc Types - Additional Type Definitions and Utility Functions
// =============================================================================

import coh_noc_pkg::*;

// =============================================================================
// Utility Functions for Flit Handling
// =============================================================================

// Function to pack flit data
function automatic flit_t pack_flit(
    input chi_opcode_e opcode,
    input logic [47:0] addr,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [3:0]  size,
    input logic [2:0]  mem_attr,
    input logic [7:0]  qos,
    input logic [511:0] data
);
    flit_t flit;
    flit.opcode   = opcode;
    flit.addr     = addr;
    flit.txn_id   = txn_id;
    flit.src_id   = src_id;
    flit.tgt_id   = tgt_id;
    flit.size     = size;
    flit.mem_attr = mem_attr;
    flit.qos      = qos;
    flit.data     = data;
    return flit;
endfunction

// Function to extract virtual channel from opcode
function automatic virtual_channel_e get_virtual_channel(input chi_opcode_e opcode);
    case (opcode)
        REQ_READ_SHARED, REQ_READ_CLEAN, REQ_READ_UNIQUE,
        REQ_WRITE_BACK, REQ_WRITE_CLEAN, REQ_WRITE_UNIQUE:
            return VC_REQ;
        
        RSP_COMP_ACK, RSP_READ_RECEIPT, RSP_COMP_DATA:
            return VC_RSP;
        
        SNP_SHARED, SNP_CLEAN, SNP_UNIQUE:
            return VC_SNP;
        
        default:
            return VC_DAT;  // Default to data channel
    endcase
endfunction

// Function to check if opcode carries data
function automatic logic has_data(input chi_opcode_e opcode);
    case (opcode)
        REQ_WRITE_BACK, REQ_WRITE_CLEAN, REQ_WRITE_UNIQUE, RSP_COMP_DATA:
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