// =============================================================================
// DDR Interface - Interface to DDR/HBM Memory Controller
// =============================================================================

interface ddr_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 512
);
    
    // =============================================================================
    // DDR Command Interface
    // =============================================================================
    
    logic                       cmd_valid;    // Command valid
    logic                       cmd_ready;    // Command ready
    logic                       cmd_read;     // Read command (1) or Write (0)
    logic [ADDR_WIDTH-1:0]      cmd_addr;     // Command address
    logic [7:0]                 cmd_len;      // Burst length
    logic [2:0]                 cmd_size;     // Transfer size
    
    // =============================================================================
    // DDR Write Data Interface
    // =============================================================================
    
    logic                       wr_valid;     // Write data valid
    logic                       wr_ready;     // Write data ready
    logic [DATA_WIDTH-1:0]      wr_data;      // Write data
    logic [DATA_WIDTH/8-1:0]    wr_strb;      // Write data strobes
    logic                       wr_last;      // Write data last
    
    // =============================================================================
    // DDR Read Data Interface
    // =============================================================================
    
    logic                       rd_valid;     // Read data valid
    logic                       rd_ready;     // Read data ready
    logic [DATA_WIDTH-1:0]      rd_data;      // Read data
    logic                       rd_last;      // Read data last
    logic [1:0]                 rd_resp;      // Read response
    
    // =============================================================================
    // DDR Status Interface
    // =============================================================================
    
    logic                       init_done;    // Initialization complete
    logic                       cal_done;     // Calibration complete
    logic                       error;        // Error indication
    
    // =============================================================================
    // Modports for Master and Slave
    // =============================================================================
    
    modport master (
        output cmd_valid, cmd_read, cmd_addr, cmd_len, cmd_size,
        input  cmd_ready,
        output wr_valid, wr_data, wr_strb, wr_last,
        input  wr_ready,
        input  rd_valid, rd_data, rd_last, rd_resp,
        output rd_ready,
        input  init_done, cal_done, error
    );
    
    modport slave (
        input  cmd_valid, cmd_read, cmd_addr, cmd_len, cmd_size,
        output cmd_ready,
        input  wr_valid, wr_data, wr_strb, wr_last,
        output wr_ready,
        output rd_valid, rd_data, rd_last, rd_resp,
        input  rd_ready,
        output init_done, cal_done, error
    );

endinterface : ddr_if