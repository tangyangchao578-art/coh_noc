// =============================================================================
// coh_noc Package - Core Data Types and Protocol Definitions
// =============================================================================

package coh_noc_pkg;

    // =============================================================================
    // CHI Protocol Operation Codes (Requirements 2.1, 2.2)
    // =============================================================================
    
    typedef enum logic [7:0] {
        // Request Channel Opcodes
        REQ_READ_SHARED     = 8'h01,
        REQ_READ_CLEAN      = 8'h02,
        REQ_READ_UNIQUE     = 8'h07,
        REQ_WRITE_BACK      = 8'h08,
        REQ_WRITE_CLEAN     = 8'h09,
        REQ_WRITE_UNIQUE    = 8'h18,
        
        // Response Channel Opcodes
        RSP_COMP_ACK        = 8'h14,
        RSP_READ_RECEIPT    = 8'h15,
        RSP_COMP_DATA       = 8'h52,
        
        // Snoop Channel Opcodes
        SNP_SHARED          = 8'h20,
        SNP_CLEAN           = 8'h21,
        SNP_UNIQUE          = 8'h22
    } chi_opcode_e;

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
    // Flit Structure Definition (Requirements 2.1, 2.2)
    // =============================================================================
    
    typedef struct packed {
        logic [7:0]   opcode;      // CHI Operation Code
        logic [47:0]  addr;        // 48-bit Physical Address
        logic [11:0]  txn_id;      // Transaction ID
        logic [7:0]   src_id;      // Source Node ID
        logic [7:0]   tgt_id;      // Target Node ID
        logic [3:0]   size;        // Data Size
        logic [2:0]   mem_attr;    // Memory Attributes
        logic [7:0]   qos;         // Quality of Service
        logic [511:0] data;        // Data Payload (optional)
    } flit_t;

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