// =============================================================================
// XP Router Computation Unit - X-Y Dimension Order Routing
// Requirements: 1.2, 3.4
// =============================================================================

import coh_noc_pkg::*;

module xp_router_compute #(
    parameter int X_COORD = 0,
    parameter int Y_COORD = 0
)(
    input  logic        clk,
    input  logic        rst_n,
    
    // Input flit information
    input  logic        flit_valid,
    input  logic [7:0]  target_id,
    
    // Output port selection
    output logic [2:0]  output_port,  // 0=North, 1=South, 2=East, 3=West, 4=Local
    output logic        route_valid
);

    // Port encoding
    typedef enum logic [2:0] {
        PORT_NORTH = 3'd0,
        PORT_SOUTH = 3'd1,
        PORT_EAST  = 3'd2,
        PORT_WEST  = 3'd3,
        PORT_LOCAL = 3'd4
    } port_e;
    
    // Current router coordinates
    coord_t current_coord;
    coord_t target_coord;
    
    // Assign current coordinates
    assign current_coord.x = X_COORD[3:0];
    assign current_coord.y = Y_COORD[3:0];
    
    // Extract target coordinates from target_id
    // Assuming target_id encoding: [7:4] = Y coordinate, [3:0] = X coordinate
    assign target_coord.x = target_id[3:0];
    assign target_coord.y = target_id[7:4];
    
    // =============================================================================
    // X-Y Dimension Order Routing Logic
    // Requirements: 1.2, 3.4
    // 
    // Algorithm:
    // 1. If current X != target X, route in X dimension (East/West)
    // 2. Else if current Y != target Y, route in Y dimension (North/South)
    // 3. Else route to local port (destination reached)
    // =============================================================================
    
    always_comb begin
        route_valid = flit_valid;
        
        if (!flit_valid) begin
            output_port = PORT_LOCAL;
        end else begin
            // X-Y Dimension Order Routing
            if (current_coord.x != target_coord.x) begin
                // Route in X dimension first
                if (current_coord.x < target_coord.x) begin
                    output_port = PORT_EAST;
                end else begin
                    output_port = PORT_WEST;
                end
            end else if (current_coord.y != target_coord.y) begin
                // Route in Y dimension
                if (current_coord.y < target_coord.y) begin
                    output_port = PORT_SOUTH;  // Assuming Y increases southward
                end else begin
                    output_port = PORT_NORTH;  // Assuming Y decreases northward
                end
            end else begin
                // Destination reached - route to local port
                output_port = PORT_LOCAL;
            end
        end
    end
    
    // =============================================================================
    // Assertions for Verification (commented out for iverilog compatibility)
    // =============================================================================
    
    // synthesis translate_off
    /*
    // Assert that output port is valid
    property valid_output_port;
        @(posedge clk) disable iff (!rst_n)
        flit_valid |-> (output_port inside {PORT_NORTH, PORT_SOUTH, PORT_EAST, PORT_WEST, PORT_LOCAL});
    endproperty
    assert property (valid_output_port) else $error("Invalid output port selected");
    
    // Assert that local port is selected only when at destination
    property local_port_at_destination;
        @(posedge clk) disable iff (!rst_n)
        (flit_valid && output_port == PORT_LOCAL) |-> 
            (current_coord.x == target_coord.x && current_coord.y == target_coord.y);
    endproperty
    assert property (local_port_at_destination) else $error("Local port selected but not at destination");
    
    // Assert X-Y dimension order: X dimension routed before Y dimension
    property xy_dimension_order;
        @(posedge clk) disable iff (!rst_n)
        (flit_valid && (output_port == PORT_NORTH || output_port == PORT_SOUTH)) |-> 
            (current_coord.x == target_coord.x);
    endproperty
    assert property (xy_dimension_order) else $error("Y dimension routed before X dimension");
    */
    // synthesis translate_on

endmodule : xp_router_compute
