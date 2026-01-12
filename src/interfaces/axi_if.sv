// =============================================================================
// AXI Interface - Standard AXI4 Interface for Memory Access
// =============================================================================

interface axi_if #(
    parameter int ADDR_WIDTH = 48,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8
);
    
    // =============================================================================
    // AXI Write Address Channel
    // =============================================================================
    
    logic [ID_WIDTH-1:0]    awid;     // Write address ID
    logic [ADDR_WIDTH-1:0]  awaddr;   // Write address
    logic [7:0]             awlen;    // Burst length
    logic [2:0]             awsize;   // Burst size
    logic [1:0]             awburst;  // Burst type
    logic                   awlock;   // Lock type
    logic [3:0]             awcache;  // Cache type
    logic [2:0]             awprot;   // Protection type
    logic [3:0]             awqos;    // Quality of Service
    logic                   awvalid;  // Write address valid
    logic                   awready;  // Write address ready
    
    // =============================================================================
    // AXI Write Data Channel
    // =============================================================================
    
    logic [DATA_WIDTH-1:0]      wdata;    // Write data
    logic [DATA_WIDTH/8-1:0]    wstrb;    // Write strobes
    logic                       wlast;    // Write last
    logic                       wvalid;   // Write valid
    logic                       wready;   // Write ready
    
    // =============================================================================
    // AXI Write Response Channel
    // =============================================================================
    
    logic [ID_WIDTH-1:0]    bid;      // Response ID
    logic [1:0]             bresp;    // Write response
    logic                   bvalid;   // Write response valid
    logic                   bready;   // Response ready
    
    // =============================================================================
    // AXI Read Address Channel
    // =============================================================================
    
    logic [ID_WIDTH-1:0]    arid;     // Read address ID
    logic [ADDR_WIDTH-1:0]  araddr;   // Read address
    logic [7:0]             arlen;    // Burst length
    logic [2:0]             arsize;   // Burst size
    logic [1:0]             arburst;  // Burst type
    logic                   arlock;   // Lock type
    logic [3:0]             arcache;  // Cache type
    logic [2:0]             arprot;   // Protection type
    logic [3:0]             arqos;    // Quality of Service
    logic                   arvalid;  // Read address valid
    logic                   arready;  // Read address ready
    
    // =============================================================================
    // AXI Read Data Channel
    // =============================================================================
    
    logic [ID_WIDTH-1:0]    rid;      // Read ID
    logic [DATA_WIDTH-1:0]  rdata;    // Read data
    logic [1:0]             rresp;    // Read response
    logic                   rlast;    // Read last
    logic                   rvalid;   // Read valid
    logic                   rready;   // Read ready
    
    // =============================================================================
    // Modports for Master and Slave
    // =============================================================================
    
    modport master (
        output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awvalid,
        input  awready,
        output wdata, wstrb, wlast, wvalid,
        input  wready,
        input  bid, bresp, bvalid,
        output bready,
        output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arvalid,
        input  arready,
        input  rid, rdata, rresp, rlast, rvalid,
        output rready
    );
    
    modport slave (
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awvalid,
        output awready,
        input  wdata, wstrb, wlast, wvalid,
        output wready,
        output bid, bresp, bvalid,
        input  bready,
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arvalid,
        output arready,
        output rid, rdata, rresp, rlast, rvalid,
        input  rready
    );

endinterface : axi_if