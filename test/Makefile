# Makefile for coh_noc Property-Based Tests and Unit Tests

# Simulator selection (default: iverilog)
SIM ?= iverilog

# Source files
SRC_DIR = ../src
TEST_DIR = .

SOURCES = \
	$(SRC_DIR)/coh_noc_pkg.sv \
	$(SRC_DIR)/coh_noc_types.sv

# XP Router implementation files
XP_ROUTER_SOURCES = \
	$(SRC_DIR)/xp_router_compute.sv \
	$(SRC_DIR)/vc_buffer.sv \
	$(SRC_DIR)/vc_buffer_manager.sv \
	$(SRC_DIR)/credit_flow_control.sv \
	$(SRC_DIR)/xp_router.sv

# Test files
TESTS = \
	tb_flit_properties.sv \
	tb_directory_properties.sv \
	tb_xp_router_unit.sv

# Simulation output
SIM_OUT = sim_out
VVP_OUT = test.vvp

# Targets
.PHONY: all clean test_flit test_directory test_xp_router_unit test_routing test_vc_buffer test_flow_control test_xp_router_properties test_router_all

all: test_flit test_directory test_xp_router_unit

# Run all router-related tests (for checkpoint)
test_router_all: test_routing test_vc_buffer test_flow_control test_xp_router_properties test_xp_router_unit

# Test Flit properties
test_flit: tb_flit_properties.sv $(SOURCES)
	@echo "==================================================================="
	@echo "Running Property Test: Flit Virtual Channel Integrity"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o $(VVP_OUT) $(SOURCES) tb_flit_properties.sv
	vvp $(VVP_OUT)
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) tb_flit_properties.sv -o simv
	./simv
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Directory properties
test_directory: tb_directory_properties.sv $(SOURCES)
	@echo "==================================================================="
	@echo "Running Property Test: Directory State Consistency"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o $(VVP_OUT) $(SOURCES) tb_directory_properties.sv
	vvp $(VVP_OUT)
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) tb_directory_properties.sv -o simv
	./simv
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test XP Router Unit Tests
test_xp_router_unit: tb_xp_router_unit.sv $(SOURCES) $(XP_ROUTER_SOURCES)
	@echo "==================================================================="
	@echo "Running Unit Tests: XP Router Edge Cases and Error Conditions"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_xp_unit.vvp $(SOURCES) $(XP_ROUTER_SOURCES) tb_xp_router_unit.sv
	vvp test_xp_unit.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(XP_ROUTER_SOURCES) tb_xp_router_unit.sv -o simv_xp_unit
	./simv_xp_unit
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Routing Algorithm Properties
test_routing: tb_routing_properties.sv $(SOURCES) $(SRC_DIR)/xp_router_compute.sv
	@echo "==================================================================="
	@echo "Running Property Test: X-Y Dimension-Order Routing Correctness"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_routing.vvp $(SOURCES) $(SRC_DIR)/xp_router_compute.sv tb_routing_properties.sv
	vvp test_routing.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/xp_router_compute.sv tb_routing_properties.sv -o simv_routing
	./simv_routing
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test VC Buffer Properties
test_vc_buffer: tb_vc_buffer_properties.sv $(SOURCES) $(SRC_DIR)/vc_buffer.sv $(SRC_DIR)/vc_buffer_manager.sv
	@echo "==================================================================="
	@echo "Running Property Test: Virtual Channel Isolation"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_vc_buffer.vvp $(SOURCES) $(SRC_DIR)/vc_buffer.sv $(SRC_DIR)/vc_buffer_manager.sv tb_vc_buffer_properties.sv
	vvp test_vc_buffer.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/vc_buffer.sv $(SRC_DIR)/vc_buffer_manager.sv tb_vc_buffer_properties.sv -o simv_vc_buffer
	./simv_vc_buffer
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Flow Control Properties
test_flow_control: tb_flow_control_properties.sv $(SOURCES) $(SRC_DIR)/credit_flow_control.sv
	@echo "==================================================================="
	@echo "Running Property Test: Credit Flow Control & Buffer Backpressure"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_flow_control.vvp $(SOURCES) $(SRC_DIR)/credit_flow_control.sv tb_flow_control_properties.sv
	vvp test_flow_control.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/credit_flow_control.sv tb_flow_control_properties.sv -o simv_flow_control
	./simv_flow_control
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test XP Router Properties
test_xp_router_properties: tb_xp_router_properties.sv $(SOURCES) $(XP_ROUTER_SOURCES)
	@echo "==================================================================="
	@echo "Running Property Test: Flit Forwarding Correctness"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_xp_router.vvp $(SOURCES) $(XP_ROUTER_SOURCES) tb_xp_router_properties.sv
	vvp test_xp_router.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(XP_ROUTER_SOURCES) tb_xp_router_properties.sv -o simv_xp_router
	./simv_xp_router
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Clean build artifacts
clean:
	rm -rf $(SIM_OUT) $(VVP_OUT) test_xp_unit.vvp test_routing.vvp test_vc_buffer.vvp test_flow_control.vvp test_xp_router.vvp simv simv_xp_unit simv_routing simv_vc_buffer simv_flow_control simv_xp_router simv.daidir csrc ucli.key *.log *.vcd

.DEFAULT_GOAL := all

# Test Mesh Topology Properties
test_mesh_topology: tb_mesh_topology_properties.sv $(SOURCES)
	@echo "==================================================================="
	@echo "Running Property Test: 2D Mesh Topology Connectivity"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_mesh_topology.vvp $(SOURCES) tb_mesh_topology_properties.sv
	vvp test_mesh_topology.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) tb_mesh_topology_properties.sv -o simv_mesh_topology
	./simv_mesh_topology
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Deadlock Prevention Properties
test_deadlock: tb_deadlock_properties.sv $(SOURCES)
	@echo "==================================================================="
	@echo "Running Property Test: Routing Deadlock Freedom"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_deadlock.vvp $(SOURCES) tb_deadlock_properties.sv
	vvp test_deadlock.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) tb_deadlock_properties.sv -o simv_deadlock
	./simv_deadlock
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif
