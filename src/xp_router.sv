// =============================================================================
// XP Router Top-Level Module - Crosspoint Router with Integrated Components
// Requirements: 3.1, 1.1
// =============================================================================

import coh_noc_pkg::*;

module xp_router #(
    parameter int X_COORD = 0,
    parameter int Y_COORD = 0,
    parameter int BUFFER_DEPTH = 16,
    parameter int NUM_VCS = 4,
    parameter int MAX_CREDITS = 16
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // =============================================================================
    // Network Ports (North, South, East, West)
    // =============================================================================
    
    // North Port
    input  logic        north_in_valid,
    output logic        north_in_ready,
    input  flit_u       north_in_flit,
    input  logic [1:0]  north_in_vc_id,
    input  logic        north_in_credit_return,
    
    output logic        north_out_valid,
    input  logic        north_out_ready,
    output flit_u       north_out_flit,
    output logic [1:0]  north_out_vc_id,
    output logic [CREDIT_COUNT_WIDTH-1:0] north_out_credit_count,
    
    // South Port
    input  logic        south_in_valid,
    output logic        south_in_ready,
    input  flit_u       south_in_flit,
    input  logic [1:0]  south_in_vc_id,
    input  logic        south_in_credit_return,
    
    output logic        south_out_valid,
    input  logic        south_out_ready,
    output flit_u       south_out_flit,
    output logic [1:0]  south_out_vc_id,
    output logic [CREDIT_COUNT_WIDTH-1:0] south_out_credit_count,
    
    // East Port
    input  logic        east_in_valid,
    output logic        east_in_ready,
    input  flit_u       east_in_flit,
    input  logic [1:0]  east_in_vc_id,
    input  logic        east_in_credit_return,
    
    output logic        east_out_valid,
    input  logic        east_out_ready,
    output flit_u       east_out_flit,
    output logic [1:0]  east_out_vc_id,
    output logic [CREDIT_COUNT_WIDTH-1:0] east_out_credit_count,
    
    // West Port
    input  logic        west_in_valid,
    output logic        west_in_ready,
    input  flit_u       west_in_flit,
    input  logic [1:0]  west_in_vc_id,
    input  logic        west_in_credit_return,
    
    output logic        west_out_valid,
    input  logic        west_out_ready,
    output flit_u       west_out_flit,
    output logic [1:0]  west_out_vc_id,
    output logic [CREDIT_COUNT_WIDTH-1:0] west_out_credit_count,
    
    // Local Port (for attached devices)
    input  logic        local_in_valid,
    output logic        local_in_ready,
    input  flit_u       local_in_flit,
    input  logic [1:0]  local_in_vc_id,
    input  logic        local_in_credit_return,
    
    output logic        local_out_valid,
    input  logic        local_out_ready,
    output flit_u       local_out_flit,
    output logic [1:0]  local_out_vc_id,
    output logic [CREDIT_COUNT_WIDTH-1:0] local_out_credit_count
);

    // =============================================================================
    // Port Definitions
    // =============================================================================
    
    typedef enum logic [2:0] {
        PORT_NORTH = 3'd0,
        PORT_SOUTH = 3'd1,
        PORT_EAST  = 3'd2,
        PORT_WEST  = 3'd3,
        PORT_LOCAL = 3'd4
    } port_e;
    
    localparam int NUM_PORTS = 5;
    
    // =============================================================================
    // Internal Signals
    // =============================================================================
    
    // Input port signals (array indexed by port)
    logic [NUM_PORTS-1:0] in_valid;
    logic [NUM_PORTS-1:0] in_ready;
    flit_u [NUM_PORTS-1:0] in_flit;
    logic [1:0] in_vc_id [NUM_PORTS-1:0];
    
    // Output port signals (array indexed by port)
    logic [NUM_PORTS-1:0] out_valid;
    logic [NUM_PORTS-1:0] out_ready;
    flit_u [NUM_PORTS-1:0] out_flit;
    logic [1:0] out_vc_id [NUM_PORTS-1:0];
    
    // Routing computation signals
    logic [2:0] route_port [NUM_PORTS-1:0];
    logic [NUM_PORTS-1:0] route_valid;
    
    // Buffer management signals per input port
    logic [NUM_PORTS-1:0] buf_wr_en;
    logic [1:0] buf_wr_vc_id [NUM_PORTS-1:0];
    flit_u buf_wr_data [NUM_PORTS-1:0];
    logic [3:0] buf_vc_full [NUM_PORTS-1:0];
    logic [3:0] buf_vc_almost_full [NUM_PORTS-1:0];
    
    logic [NUM_PORTS-1:0] buf_rd_en;
    logic [1:0] buf_rd_vc_id [NUM_PORTS-1:0];
    flit_u buf_rd_data [NUM_PORTS-1:0];
    logic [3:0] buf_vc_empty [NUM_PORTS-1:0];
    logic [3:0] buf_vc_almost_empty [NUM_PORTS-1:0];
    
    logic [7:0] buf_vc_count [NUM_PORTS-1:0][NUM_VCS-1:0];
    logic [7:0] buf_vc_free_slots [NUM_PORTS-1:0][NUM_VCS-1:0];
    
    // Flow control signals per output port
    logic [CREDIT_COUNT_WIDTH-1:0] fc_credit_count [NUM_PORTS-1:0][NUM_VCS-1:0];
    logic [NUM_VCS-1:0] fc_credit_available [NUM_PORTS-1:0];
    logic [NUM_PORTS-1:0] fc_consume_credit;
    logic [1:0] fc_consume_vc_id [NUM_PORTS-1:0];
    logic [NUM_PORTS-1:0] fc_return_credit;
    logic [1:0] fc_return_vc_id [NUM_PORTS-1:0];
    logic [NUM_VCS-1:0] fc_backpressure [NUM_PORTS-1:0];
    
    // Arbitration signals
    logic [NUM_PORTS-1:0][NUM_PORTS-1:0] arb_request;  // [output_port][input_port]
    logic [NUM_PORTS-1:0][NUM_PORTS-1:0] arb_grant;    // [output_port][input_port]
    
    // =============================================================================
    // Map Interface Signals to Internal Arrays
    // =============================================================================
    
    // Input port mapping
    assign in_valid[PORT_NORTH] = north_in_valid;
    assign in_valid[PORT_SOUTH] = south_in_valid;
    assign in_valid[PORT_EAST]  = east_in_valid;
    assign in_valid[PORT_WEST]  = west_in_valid;
    assign in_valid[PORT_LOCAL] = local_in_valid;
    
    assign north_in_ready = in_ready[PORT_NORTH];
    assign south_in_ready = in_ready[PORT_SOUTH];
    assign east_in_ready  = in_ready[PORT_EAST];
    assign west_in_ready  = in_ready[PORT_WEST];
    assign local_in_ready = in_ready[PORT_LOCAL];
    
    assign in_flit[PORT_NORTH] = north_in_flit;
    assign in_flit[PORT_SOUTH] = south_in_flit;
    assign in_flit[PORT_EAST]  = east_in_flit;
    assign in_flit[PORT_WEST]  = west_in_flit;
    assign in_flit[PORT_LOCAL] = local_in_flit;
    
    assign in_vc_id[PORT_NORTH] = north_in_vc_id;
    assign in_vc_id[PORT_SOUTH] = south_in_vc_id;
    assign in_vc_id[PORT_EAST]  = east_in_vc_id;
    assign in_vc_id[PORT_WEST]  = west_in_vc_id;
    assign in_vc_id[PORT_LOCAL] = local_in_vc_id;
    
    // Output port mapping
    assign north_out_valid = out_valid[PORT_NORTH];
    assign south_out_valid = out_valid[PORT_SOUTH];
    assign east_out_valid  = out_valid[PORT_EAST];
    assign west_out_valid  = out_valid[PORT_WEST];
    assign local_out_valid = out_valid[PORT_LOCAL];
    
    assign out_ready[PORT_NORTH] = north_out_ready;
    assign out_ready[PORT_SOUTH] = south_out_ready;
    assign out_ready[PORT_EAST]  = east_out_ready;
    assign out_ready[PORT_WEST]  = west_out_ready;
    assign out_ready[PORT_LOCAL] = local_out_ready;
    
    assign north_out_flit = out_flit[PORT_NORTH];
    assign south_out_flit = out_flit[PORT_SOUTH];
    assign east_out_flit  = out_flit[PORT_EAST];
    assign west_out_flit  = out_flit[PORT_WEST];
    assign local_out_flit = out_flit[PORT_LOCAL];
    
    assign north_out_vc_id = out_vc_id[PORT_NORTH];
    assign south_out_vc_id = out_vc_id[PORT_SOUTH];
    assign east_out_vc_id  = out_vc_id[PORT_EAST];
    assign west_out_vc_id  = out_vc_id[PORT_WEST];
    assign local_out_vc_id = out_vc_id[PORT_LOCAL];
    
    // =============================================================================
    // Routing Computation Units (one per input port)
    // =============================================================================
    
    genvar p;
    generate
        for (p = 0; p < NUM_PORTS; p++) begin : gen_route_compute
            xp_router_compute #(
                .X_COORD(X_COORD),
                .Y_COORD(Y_COORD)
            ) route_compute_inst (
                .clk(clk),
                .rst_n(rst_n),
                .flit_valid(in_valid[p]),
                .target_id(in_flit[p].req.tgt_id),  // Use req flit target_id
                .output_port(route_port[p]),
                .route_valid(route_valid[p])
            );
        end
    endgenerate
    
    // =============================================================================
    // Virtual Channel Buffer Managers (one per input port)
    // =============================================================================
    
    generate
        for (p = 0; p < NUM_PORTS; p++) begin : gen_vc_buffers
            vc_buffer_manager #(
                .BUFFER_DEPTH(BUFFER_DEPTH),
                .NUM_VCS(NUM_VCS)
            ) vc_buf_mgr_inst (
                .clk(clk),
                .rst_n(rst_n),
                
                // Write interface
                .wr_en(buf_wr_en[p]),
                .wr_vc_id(buf_wr_vc_id[p]),
                .wr_data(buf_wr_data[p]),
                .vc_full(buf_vc_full[p]),
                .vc_almost_full(buf_vc_almost_full[p]),
                
                // Read interface
                .rd_en(buf_rd_en[p]),
                .rd_vc_id(buf_rd_vc_id[p]),
                .rd_data(buf_rd_data[p]),
                .vc_empty(buf_vc_empty[p]),
                .vc_almost_empty(buf_vc_almost_empty[p]),
                
                // Status signals
                .vc_count(buf_vc_count[p]),
                .vc_free_slots(buf_vc_free_slots[p])
            );
        end
    endgenerate
    
    // =============================================================================
    // Credit Flow Control Units (one per output port)
    // =============================================================================
    
    generate
        for (p = 0; p < NUM_PORTS; p++) begin : gen_flow_control
            credit_flow_control #(
                .MAX_CREDITS(MAX_CREDITS),
                .NUM_VCS(NUM_VCS)
            ) flow_ctrl_inst (
                .clk(clk),
                .rst_n(rst_n),
                
                // Credit tracking
                .credit_count(fc_credit_count[p]),
                .credit_available(fc_credit_available[p]),
                
                // Credit consumption
                .consume_credit(fc_consume_credit[p]),
                .consume_vc_id(fc_consume_vc_id[p]),
                
                // Credit return
                .return_credit(fc_return_credit[p]),
                .return_vc_id(fc_return_vc_id[p]),
                
                // Backpressure
                .backpressure(fc_backpressure[p])
            );
        end
    endgenerate
    
    // =============================================================================
    // Input Stage: Buffer Write Logic
    // =============================================================================
    
    always_comb begin
        for (int i = 0; i < NUM_PORTS; i++) begin
            // Write to buffer when valid input and buffer not full
            buf_wr_en[i] = in_valid[i] && !buf_vc_full[i][in_vc_id[i]];
            buf_wr_vc_id[i] = in_vc_id[i];
            buf_wr_data[i] = in_flit[i];
            
            // Ready when buffer has space
            in_ready[i] = !buf_vc_full[i][in_vc_id[i]];
        end
    end
    
    // =============================================================================
    // Arbitration Logic: Round-Robin Arbiter per Output Port
    // =============================================================================
    
    // Arbitration request generation
    always_comb begin
        for (int out_p = 0; out_p < NUM_PORTS; out_p++) begin
            for (int in_p = 0; in_p < NUM_PORTS; in_p++) begin
                // Request if: buffer not empty, routed to this output, and credits available
                arb_request[out_p][in_p] = !buf_vc_empty[in_p][buf_rd_vc_id[in_p]] &&
                                           route_valid[in_p] &&
                                           (route_port[in_p] == out_p) &&
                                           fc_credit_available[out_p][buf_rd_vc_id[in_p]];
            end
        end
    end
    
    // Simple priority arbiter (lower port number has priority)
    // In a real design, this would be round-robin or weighted fair queuing
    always_comb begin
        for (int out_p = 0; out_p < NUM_PORTS; out_p++) begin
            arb_grant[out_p] = '0;
            
            // Priority encoder: grant to lowest requesting port
            for (int in_p = 0; in_p < NUM_PORTS; in_p++) begin
                if (arb_request[out_p][in_p] && arb_grant[out_p] == '0) begin
                    arb_grant[out_p][in_p] = 1'b1;
                end
            end
        end
    end
    
    // =============================================================================
    // Output Stage: Crossbar Switch and Output Logic
    // =============================================================================
    
    always_comb begin
        // Default values
        for (int p = 0; p < NUM_PORTS; p++) begin
            buf_rd_en[p] = 1'b0;
            buf_rd_vc_id[p] = 2'b00;
            out_valid[p] = 1'b0;
            out_flit[p] = '0;
            out_vc_id[p] = 2'b00;
            fc_consume_credit[p] = 1'b0;
            fc_consume_vc_id[p] = 2'b00;
        end
        
        // For each output port, check which input port won arbitration
        for (int out_p = 0; out_p < NUM_PORTS; out_p++) begin
            for (int in_p = 0; in_p < NUM_PORTS; in_p++) begin
                if (arb_grant[out_p][in_p]) begin
                    // Read from granted input buffer
                    buf_rd_en[in_p] = 1'b1;
                    buf_rd_vc_id[in_p] = in_vc_id[in_p];  // Use same VC as input
                    
                    // Drive output port
                    out_valid[out_p] = 1'b1;
                    out_flit[out_p] = buf_rd_data[in_p];
                    out_vc_id[out_p] = in_vc_id[in_p];
                    
                    // Consume credit when flit is sent
                    fc_consume_credit[out_p] = out_ready[out_p];
                    fc_consume_vc_id[out_p] = in_vc_id[in_p];
                end
            end
        end
    end
    
    // =============================================================================
    // Credit Return Logic
    // =============================================================================
    
    // Return credits to upstream routers when we consume flits from our buffers
    always_comb begin
        for (int p = 0; p < NUM_PORTS; p++) begin
            fc_return_credit[p] = buf_wr_en[p];
            fc_return_vc_id[p] = buf_wr_vc_id[p];
        end
    end
    
    // Map credit counts to output interfaces
    assign north_out_credit_count = fc_credit_count[PORT_NORTH][north_out_vc_id];
    assign south_out_credit_count = fc_credit_count[PORT_SOUTH][south_out_vc_id];
    assign east_out_credit_count  = fc_credit_count[PORT_EAST][east_out_vc_id];
    assign west_out_credit_count  = fc_credit_count[PORT_WEST][west_out_vc_id];
    assign local_out_credit_count = fc_credit_count[PORT_LOCAL][local_out_vc_id];
    
    // Handle credit returns from downstream
    assign fc_return_credit[PORT_NORTH] = north_in_credit_return;
    assign fc_return_credit[PORT_SOUTH] = south_in_credit_return;
    assign fc_return_credit[PORT_EAST]  = east_in_credit_return;
    assign fc_return_credit[PORT_WEST]  = west_in_credit_return;
    assign fc_return_credit[PORT_LOCAL] = local_in_credit_return;

endmodule : xp_router
