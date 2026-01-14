// =============================================================================
// 2D Mesh Network Topology Generator
// Requirements: 1.1, 1.4
// =============================================================================

import coh_noc_pkg::*;

module mesh_2d_network #(
    parameter int MESH_SIZE_X = 3,      // Number of columns
    parameter int MESH_SIZE_Y = 3,      // Number of rows
    parameter int BUFFER_DEPTH = 16,
    parameter int NUM_VCS = 4,
    parameter int MAX_CREDITS = 16
)(
    input  logic clk,
    input  logic rst_n,
    
    // =============================================================================
    // Local Device Ports - One per XP node
    // =============================================================================
    
    // Local input ports (from devices to network)
    input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_in_valid,
    output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_in_ready,
    input  flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_in_flit,
    input  logic [1:0] local_in_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0],
    input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_in_credit_return,
    
    // Local output ports (from network to devices)
    output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_out_valid,
    input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_out_ready,
    output flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_out_flit,
    output logic [1:0] local_out_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0],
    output logic [CREDIT_COUNT_WIDTH-1:0] local_out_credit_count [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]
);

    // =============================================================================
    // Internal Connection Signals Between Routers
    // =============================================================================
    
    // East-going connections (from router[x][y] east port to router[x+1][y] west port)
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] east_going_valid;
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] east_going_ready;
    flit_u [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] east_going_flit;
    logic [1:0] east_going_vc_id [MESH_SIZE_X:0][MESH_SIZE_Y-1:0];
    logic [CREDIT_COUNT_WIDTH-1:0] east_going_credit_count [MESH_SIZE_X:0][MESH_SIZE_Y-1:0];
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] east_going_credit_return;
    
    // West-going connections (from router[x][y] west port to router[x-1][y] east port)
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] west_going_valid;
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] west_going_ready;
    flit_u [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] west_going_flit;
    logic [1:0] west_going_vc_id [MESH_SIZE_X:0][MESH_SIZE_Y-1:0];
    logic [CREDIT_COUNT_WIDTH-1:0] west_going_credit_count [MESH_SIZE_X:0][MESH_SIZE_Y-1:0];
    logic [MESH_SIZE_X:0][MESH_SIZE_Y-1:0] west_going_credit_return;
    
    // North-going connections (from router[x][y] north port to router[x][y+1] south port)
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] north_going_valid;
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] north_going_ready;
    flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] north_going_flit;
    logic [1:0] north_going_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y:0];
    logic [CREDIT_COUNT_WIDTH-1:0] north_going_credit_count [MESH_SIZE_X-1:0][MESH_SIZE_Y:0];
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] north_going_credit_return;
    
    // South-going connections (from router[x][y] south port to router[x][y-1] north port)
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] south_going_valid;
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] south_going_ready;
    flit_u [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] south_going_flit;
    logic [1:0] south_going_vc_id [MESH_SIZE_X-1:0][MESH_SIZE_Y:0];
    logic [CREDIT_COUNT_WIDTH-1:0] south_going_credit_count [MESH_SIZE_X-1:0][MESH_SIZE_Y:0];
    logic [MESH_SIZE_X-1:0][MESH_SIZE_Y:0] south_going_credit_return;

    // =============================================================================
    // Generate 2D Mesh of XP Routers
    // =============================================================================
    
    genvar x, y;
    generate
        for (x = 0; x < MESH_SIZE_X; x++) begin : gen_mesh_x
            for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_mesh_y
                
                // Instantiate XP router at position (x, y)
                xp_router #(
                    .X_COORD(x),
                    .Y_COORD(y),
                    .BUFFER_DEPTH(BUFFER_DEPTH),
                    .NUM_VCS(NUM_VCS),
                    .MAX_CREDITS(MAX_CREDITS)
                ) xp_router_inst (
                    .clk(clk),
                    .rst_n(rst_n),
                    
                    // North port - receives from south_going[x][y+1], sends to north_going[x][y+1]
                    .north_in_valid(south_going_valid[x][y+1]),
                    .north_in_ready(south_going_ready[x][y+1]),
                    .north_in_flit(south_going_flit[x][y+1]),
                    .north_in_vc_id(south_going_vc_id[x][y+1]),
                    .north_in_credit_return(south_going_credit_return[x][y+1]),
                    
                    .north_out_valid(north_going_valid[x][y+1]),
                    .north_out_ready(north_going_ready[x][y+1]),
                    .north_out_flit(north_going_flit[x][y+1]),
                    .north_out_vc_id(north_going_vc_id[x][y+1]),
                    .north_out_credit_count(north_going_credit_count[x][y+1]),
                    
                    // South port - receives from north_going[x][y], sends to south_going[x][y]
                    .south_in_valid(north_going_valid[x][y]),
                    .south_in_ready(north_going_ready[x][y]),
                    .south_in_flit(north_going_flit[x][y]),
                    .south_in_vc_id(north_going_vc_id[x][y]),
                    .south_in_credit_return(north_going_credit_return[x][y]),
                    
                    .south_out_valid(south_going_valid[x][y]),
                    .south_out_ready(south_going_ready[x][y]),
                    .south_out_flit(south_going_flit[x][y]),
                    .south_out_vc_id(south_going_vc_id[x][y]),
                    .south_out_credit_count(south_going_credit_count[x][y]),
                    
                    // East port - receives from west_going[x+1][y], sends to east_going[x+1][y]
                    .east_in_valid(west_going_valid[x+1][y]),
                    .east_in_ready(west_going_ready[x+1][y]),
                    .east_in_flit(west_going_flit[x+1][y]),
                    .east_in_vc_id(west_going_vc_id[x+1][y]),
                    .east_in_credit_return(west_going_credit_return[x+1][y]),
                    
                    .east_out_valid(east_going_valid[x+1][y]),
                    .east_out_ready(east_going_ready[x+1][y]),
                    .east_out_flit(east_going_flit[x+1][y]),
                    .east_out_vc_id(east_going_vc_id[x+1][y]),
                    .east_out_credit_count(east_going_credit_count[x+1][y]),
                    
                    // West port - receives from east_going[x][y], sends to west_going[x][y]
                    .west_in_valid(east_going_valid[x][y]),
                    .west_in_ready(east_going_ready[x][y]),
                    .west_in_flit(east_going_flit[x][y]),
                    .west_in_vc_id(east_going_vc_id[x][y]),
                    .west_in_credit_return(east_going_credit_return[x][y]),
                    
                    .west_out_valid(west_going_valid[x][y]),
                    .west_out_ready(west_going_ready[x][y]),
                    .west_out_flit(west_going_flit[x][y]),
                    .west_out_vc_id(west_going_vc_id[x][y]),
                    .west_out_credit_count(west_going_credit_count[x][y]),
                    
                    // Local port
                    .local_in_valid(local_in_valid[x][y]),
                    .local_in_ready(local_in_ready[x][y]),
                    .local_in_flit(local_in_flit[x][y]),
                    .local_in_vc_id(local_in_vc_id[x][y]),
                    .local_in_credit_return(local_in_credit_return[x][y]),
                    
                    .local_out_valid(local_out_valid[x][y]),
                    .local_out_ready(local_out_ready[x][y]),
                    .local_out_flit(local_out_flit[x][y]),
                    .local_out_vc_id(local_out_vc_id[x][y]),
                    .local_out_credit_count(local_out_credit_count[x][y])
                );
                
            end
        end
    endgenerate
    
    // =============================================================================
    // Boundary Condition Handling - Tie off edge ports
    // =============================================================================
    
    generate
        // Left edge (x = 0): tie off west boundary
        for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_boundary_west
            assign east_going_valid[0][y] = 1'b0;
            assign east_going_flit[0][y] = '0;
            assign east_going_vc_id[0][y] = 2'b00;
            assign east_going_credit_count[0][y] = '0;
            assign east_going_credit_return[0][y] = 1'b0;
            assign west_going_ready[0][y] = 1'b0;
        end
        
        // Right edge (x = MESH_SIZE_X): tie off east boundary
        for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_boundary_east
            assign west_going_valid[MESH_SIZE_X][y] = 1'b0;
            assign west_going_flit[MESH_SIZE_X][y] = '0;
            assign west_going_vc_id[MESH_SIZE_X][y] = 2'b00;
            assign west_going_credit_count[MESH_SIZE_X][y] = '0;
            assign west_going_credit_return[MESH_SIZE_X][y] = 1'b0;
            assign east_going_ready[MESH_SIZE_X][y] = 1'b0;
        end
        
        // Bottom edge (y = 0): tie off south boundary
        for (x = 0; x < MESH_SIZE_X; x++) begin : gen_boundary_south
            assign north_going_valid[x][0] = 1'b0;
            assign north_going_flit[x][0] = '0;
            assign north_going_vc_id[x][0] = 2'b00;
            assign north_going_credit_count[x][0] = '0;
            assign north_going_credit_return[x][0] = 1'b0;
            assign south_going_ready[x][0] = 1'b0;
        end
        
        // Top edge (y = MESH_SIZE_Y): tie off north boundary
        for (x = 0; x < MESH_SIZE_X; x++) begin : gen_boundary_north
            assign south_going_valid[x][MESH_SIZE_Y] = 1'b0;
            assign south_going_flit[x][MESH_SIZE_Y] = '0;
            assign south_going_vc_id[x][MESH_SIZE_Y] = 2'b00;
            assign south_going_credit_count[x][MESH_SIZE_Y] = '0;
            assign south_going_credit_return[x][MESH_SIZE_Y] = 1'b0;
            assign north_going_ready[x][MESH_SIZE_Y] = 1'b0;
        end
    endgenerate

endmodule : mesh_2d_network
