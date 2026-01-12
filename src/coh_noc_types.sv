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
    flit.trace_tag    = 16'h0000;
    flit.reserved     = 8'h00;
    return flit;
endfunction

// Function to pack RSP flit data
function automatic rsp_flit_t pack_rsp_flit(
    input rsp_opcode_e opcode,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [1:0]  resp,
    input logic [1:0]  fwd_state
);
    rsp_flit_t flit;
    flit.opcode       = opcode;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.tgt_id       = tgt_id;
    flit.resp         = resp;
    flit.fwd_state    = fwd_state;
    flit.data_pull    = 2'b00;
    flit.cb_id        = 3'b000;
    flit.pcrd_type    = 2'b00;
    flit.trace_tag    = 16'h0000;
    flit.reserved     = 32'h00000000;
    return flit;
endfunction

// Function to pack DAT flit data
function automatic dat_flit_t pack_dat_flit(
    input dat_opcode_e opcode,
    input logic [11:0] txn_id,
    input logic [7:0]  src_id,
    input logic [7:0]  tgt_id,
    input logic [511:0] data,
    input logic [2:0]  data_id,
    input logic [1:0]  resp
);
    dat_flit_t flit;
    flit.opcode       = opcode;
    flit.txn_id       = txn_id;
    flit.src_id       = src_id;
    flit.tgt_id       = tgt_id;
    flit.data         = data;
    flit.data_id      = data_id;
    flit.resp         = resp;
    flit.home_node_id = 2'b00;
    flit.fwd_state    = 2'b00;
    flit.cb_id        = 3'b000;
    flit.ccid         = 2'b00;
    flit.data_check   = 2'b00;
    flit.poison       = 2'b00;
    flit.trace_tag    = 16'h0000;
    flit.data_check_bits = 64'h0000000000000000;
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
    flit.trace_tag    = 16'h0000;
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