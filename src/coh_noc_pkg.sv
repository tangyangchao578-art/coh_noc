// =============================================================================
// coh_noc Package - Core Data Types and Protocol Definitions
// =============================================================================

package coh_noc_pkg;

    // =============================================================================
    // CHI Protocol Operation Codes (Requirements 2.1, 2.2)
    // =============================================================================
    
    // REQ Channel Opcodes
    typedef enum logic [7:0] {
        REQ_READ_SHARED     = 8'h01,
        REQ_READ_CLEAN      = 8'h02,
        REQ_READ_ONCE       = 8'h03,
        REQ_READ_NO_SNOOP   = 8'h04,
        REQ_READ_UNIQUE     = 8'h07,
        REQ_CLEAN_SHARED    = 8'h08,
        REQ_CLEAN_INVALID   = 8'h09,
        REQ_MAKE_INVALID    = 8'h0D,
        REQ_WRITE_BACK_FULL = 8'h18,
        REQ_WRITE_CLEAN_FULL= 8'h19,
        REQ_WRITE_UNIQUE_FULL = 8'h1A,
        REQ_WRITE_UNIQUE_PTL = 8'h1B,
        REQ_WRITE_NO_SNOOP_FULL = 8'h1C,
        REQ_WRITE_NO_SNOOP_PTL = 8'h1D,
        REQ_ATOMIC_STORE    = 8'h20,
        REQ_ATOMIC_LOAD     = 8'h21,
        REQ_ATOMIC_SWAP     = 8'h22,
        REQ_ATOMIC_COMPARE  = 8'h23,
        REQ_DVM_OP          = 8'h24
    } req_opcode_e;
    
    // RSP Channel Opcodes
    typedef enum logic [7:0] {
        RSP_COMP_ACK        = 8'h14,
        RSP_READ_RECEIPT    = 8'h15,
        RSP_COMP            = 8'h16,
        RSP_COMP_DATA       = 8'h52,
        RSP_DATA_SEPDATA    = 8'h53,
        RSP_RETRY_ACK       = 8'h17,
        RSP_PCR_GRANT_ACK   = 8'h18
    } rsp_opcode_e;
    
    // DAT Channel Opcodes
    typedef enum logic [7:0] {
        DAT_DATA_FLIT       = 8'h00,
        DAT_COMP_DATA       = 8'h52,
        DAT_NON_COPY_BACK_WR_DATA = 8'h54,
        DAT_COPY_BACK_WR_DATA = 8'h55,
        DAT_DATA_SEP_DATA   = 8'h53
    } dat_opcode_e;
    
    // SNP Channel Opcodes
    typedef enum logic [7:0] {
        SNP_SHARED          = 8'h20,
        SNP_CLEAN           = 8'h21,
        SNP_ONCE            = 8'h22,
        SNP_NOT_SHARED_DIRTY = 8'h23,
        SNP_UNIQUE          = 8'h24,
        SNP_CLEAN_SHARED    = 8'h25,
        SNP_CLEAN_INVALID   = 8'h26,
        SNP_MAKE_INVALID    = 8'h27,
        SNP_DVM_OP          = 8'h28,
        // Forward Snoop Opcodes for DCT (Direct Cache Transfer)
        SNP_FWD_SHARED      = 8'h30,
        SNP_FWD_CLEAN       = 8'h31,
        SNP_FWD_ONCE        = 8'h32,
        SNP_FWD_NOT_SHARED_DIRTY = 8'h33,
        SNP_FWD_UNIQUE      = 8'h34,
        SNP_FWD_CLEAN_SHARED = 8'h35,
        SNP_FWD_CLEAN_INVALID = 8'h36,
        SNP_FWD_MAKE_INVALID = 8'h37
    } snp_opcode_e;

    // =============================================================================
    // Virtual Channel Definitions (Requirements 2.3, 2.4, 2.5, 2.6)
    // =============================================================================
    
    typedef enum logic [1:0] {
        VC_REQ = 2'b00,  // Request Virtual Channel
        VC_RSP = 2'b01,  // Response Virtual Channel
        VC_DAT = 2'b10,  // Data Virtual Channel
        VC_SNP = 2'b11   // Snoop Virtual Channel
    } virtual_channel_e;

    // =============================================================================
    // CHI Flit Structures by Channel (Requirements 2.1, 2.2)
    // =============================================================================
    
    // REQ Channel Flit Structure
    typedef struct packed {
        logic [7:0]   opcode;      // CHI Request Opcode
        logic [47:0]  addr;        // 48-bit Physical Address  
        logic [11:0]  txn_id;      // Transaction ID
        logic [7:0]   src_id;      // Source Node ID
        logic [7:0]   tgt_id;      // Target Node ID
        logic [2:0]   size;        // Transfer Size (2^size bytes)
        logic [2:0]   mem_attr;    // Memory Attributes
        logic [3:0]   qos;         // Quality of Service
        logic         ns;          // Non-secure
        logic         likely_shared; // Likely Shared hint
        logic         allow_retry; // Allow Retry
        logic         order;       // Ordering requirement
        logic [1:0]   pcrd_type;   // P-Credit Type
        logic [7:0]   trace_tag;   // Trace Tag (8-bit)
        logic [7:0]   reserved;    // Reserved bits
        logic [614:0] padding;     // Padding to match dat_flit_t size (731 bits)
    } req_flit_t;
    
    // RSP Channel Flit Structure  
    typedef struct packed {
        logic [7:0]   opcode;      // CHI Response Opcode
        logic [11:0]  txn_id;      // Transaction ID
        logic [7:0]   src_id;      // Source Node ID
        logic [7:0]   tgt_id;      // Target Node ID
        logic [7:0]   dbid;        // Data Buffer ID
        logic [1:0]   resp;        // Response status
        logic [1:0]   fwd_state;   // Forward State
        logic [1:0]   data_pull;   // Data Pull
        logic [1:0]   pcrd_type;   // P-Credit Type
        logic [7:0]   trace_tag;   // Trace Tag (8-bit)
        logic [31:0]  reserved;    // Reserved bits
        logic [638:0] padding;     // Padding to match dat_flit_t size (731 bits)
    } rsp_flit_t;
    
    // DAT Channel Flit Structure
    typedef struct packed {
        logic [7:0]   opcode;      // CHI Data Opcode
        logic [11:0]  txn_id;      // Transaction ID
        logic [7:0]   src_id;      // Source Node ID
        logic [7:0]   tgt_id;      // Target Node ID
        logic [7:0]   home_node_id; // Home Node ID
        logic [7:0]   dbid;        // Data Buffer ID
        logic [1:0]   resp;        // Response status
        logic [1:0]   fwd_state;   // Forward State
        logic [1:0]   data_pull;   // Data Pull
        logic [2:0]   data_id;     // Data ID (for multi-flit data)
        logic [1:0]   ccid;        // Critical Chunk ID
        logic [63:0]  be;          // Byte Enable (64 bits for 512-bit data)
        logic [1:0]   data_check;  // Data Check
        logic [1:0]   poison;      // Poison
        logic [7:0]   trace_tag;   // Trace Tag (8-bit)
        logic [511:0] data;        // 512-bit Data Payload
        logic [63:0]  data_check_bits; // Data Check/ECC bits
        logic [15:0]  reserved;    // Reserved bits
    } dat_flit_t;
    
    // SNP Channel Flit Structure
    typedef struct packed {
        logic [7:0]   opcode;      // CHI Snoop Opcode
        logic [47:3]  addr;        // Address (aligned to 64-byte)
        logic [11:0]  txn_id;      // Transaction ID
        logic [7:0]   src_id;      // Source Node ID
        logic [7:0]   fwd_txn_id;  // Forward Transaction ID
        logic [7:0]   fwd_node_id; // Forward Node ID
        logic         do_not_goto_sd; // Do Not Go To SD
        logic         ret_to_src;  // Return to Source
        logic [7:0]   trace_tag;   // Trace Tag (8-bit)
        logic [15:0]  reserved;    // Reserved bits
        logic [615:0] padding;     // Padding to match dat_flit_t size (731 bits)
    } snp_flit_t;
    
    // Generic Flit Union for easier handling
    typedef union packed {
        req_flit_t req;
        rsp_flit_t rsp;
        dat_flit_t dat;
        snp_flit_t snp;
    } flit_u;

    // =============================================================================
    // Directory State Definitions (Requirements 7.1, 7.2, 4.4)
    // =============================================================================
    
    typedef enum logic [3:0] {
        DIR_INVALID   = 4'h0,
        DIR_SHARED    = 4'h1,
        DIR_EXCLUSIVE = 4'h2,
        DIR_MODIFIED  = 4'h3
    } directory_state_e;

    typedef struct packed {
        directory_state_e state;       // MESI State
        logic [15:0]      sharer_mask; // Sharer Bitmask
        logic [7:0]       owner_id;    // Owner Node ID
        logic             dirty;       // Dirty Bit
    } directory_entry_t;

    // =============================================================================
    // Network Coordinates and Routing
    // =============================================================================
    
    typedef struct packed {
        logic [3:0] x;
        logic [3:0] y;
    } coord_t;

    // =============================================================================
    // Flow Control Parameters
    // =============================================================================
    
    parameter int CREDIT_COUNT_WIDTH = 8;
    parameter int MAX_CREDITS = 255;
    parameter int VC_BUFFER_DEPTH = 16;

    // =============================================================================
    // Cache Parameters
    // =============================================================================
    
    parameter int SLC_SIZE = 1024*1024;  // 1MB System Level Cache
    parameter int SLC_WAYS = 16;         // 16-way associative
    parameter int L1_SIZE = 64*1024;     // 64KB L1 Cache
    parameter int L1_WAYS = 4;           // 4-way associative

endpackage : coh_noc_pkg