// =============================================================================
// XP Port Interface - Crosspoint Router Port Interface
// =============================================================================

import coh_noc_pkg::*;

interface xp_port_if #(
    parameter CHANNEL_TYPE = "REQ"  // "REQ", "RSP", "DAT", "SNP"
);
    
    // =============================================================================
    // Flit Transmission Signals
    // =============================================================================
    
    logic        valid;        // Valid flit present
    logic        ready;        // Ready to accept flit
    flit_u       flit;         // Flit data (union of all channel types)
    logic [1:0]  vc_id;        // Virtual Channel ID
    
    // =============================================================================
    // Flow Control Signals
    // =============================================================================
    
    logic [CREDIT_COUNT_WIDTH-1:0] credit_count;   // Available credits
    logic                          credit_return;  // Credit return signal
    
    // =============================================================================
    // Channel Type Identification
    // =============================================================================
    
    logic [1:0] channel_type;  // 00=REQ, 01=RSP, 10=DAT, 11=SNP
    
    // =============================================================================
    // Modports for Master and Slave
    // =============================================================================
    
    modport master (
        output valid,
        input  ready,
        output flit,
        output vc_id,
        output channel_type,
        input  credit_count,
        output credit_return
    );
    
    modport slave (
        input  valid,
        output ready,
        input  flit,
        input  vc_id,
        input  channel_type,
        output credit_count,
        input  credit_return
    );

endinterface : xp_port_if