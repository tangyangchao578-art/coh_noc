// =============================================================================
// XP Port Interface - Crosspoint Router Port Interface
// =============================================================================

import coh_noc_pkg::*;

interface xp_port_if;
    
    // =============================================================================
    // Flit Transmission Signals
    // =============================================================================
    
    logic        valid;        // Valid flit present
    logic        ready;        // Ready to accept flit
    flit_t       flit;         // Flit data
    logic [3:0]  vc_id;        // Virtual Channel ID
    
    // =============================================================================
    // Flow Control Signals
    // =============================================================================
    
    logic [CREDIT_COUNT_WIDTH-1:0] credit_count;   // Available credits
    logic                          credit_return;  // Credit return signal
    
    // =============================================================================
    // Modports for Master and Slave
    // =============================================================================
    
    modport master (
        output valid,
        input  ready,
        output flit,
        output vc_id,
        input  credit_count,
        output credit_return
    );
    
    modport slave (
        input  valid,
        output ready,
        input  flit,
        input  vc_id,
        output credit_count,
        input  credit_return
    );

endinterface : xp_port_if