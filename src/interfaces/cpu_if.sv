// =============================================================================
// CPU Interface - Interface between CPU and RN-F Node
// =============================================================================

import coh_noc_pkg::*;

interface cpu_if;
    
    // =============================================================================
    // CPU Request Signals
    // =============================================================================
    
    logic        req_valid;     // Request valid
    logic        req_ready;     // Request ready
    logic        req_read;      // Read request (1) or Write (0)
    logic [47:0] req_addr;      // Request address
    logic [3:0]  req_size;      // Request size
    logic [511:0] req_data;     // Write data
    logic [7:0]  req_qos;       // Quality of Service
    
    // =============================================================================
    // CPU Response Signals
    // =============================================================================
    
    logic        rsp_valid;     // Response valid
    logic        rsp_ready;     // Response ready
    logic [511:0] rsp_data;     // Response data
    logic        rsp_error;     // Response error
    logic [11:0] rsp_txn_id;    // Response transaction ID
    
    // =============================================================================
    // Modports for Master and Slave
    // =============================================================================
    
    modport master (
        output req_valid,
        input  req_ready,
        output req_read,
        output req_addr,
        output req_size,
        output req_data,
        output req_qos,
        input  rsp_valid,
        output rsp_ready,
        input  rsp_data,
        input  rsp_error,
        input  rsp_txn_id
    );
    
    modport slave (
        input  req_valid,
        output req_ready,
        input  req_read,
        input  req_addr,
        input  req_size,
        input  req_data,
        input  req_qos,
        output rsp_valid,
        input  rsp_ready,
        output rsp_data,
        output rsp_error,
        output rsp_txn_id
    );

endinterface : cpu_if