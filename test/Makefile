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
	rm -rf $(SIM_OUT) $(VVP_OUT) test_xp_unit.vvp test_routing.vvp test_vc_buffer.vvp test_flow_control.vvp test_xp_router.vvp test_mesi.vvp test_snoop_filter.vvp simv simv_xp_unit simv_routing simv_vc_buffer simv_flow_control simv_xp_router simv_mesi simv_snoop_filter simv.daidir csrc ucli.key *.log *.vcd

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

# Test SLC Cache Properties
test_slc: tb_slc_properties.sv $(SOURCES) $(SRC_DIR)/slc_cache.sv
	@echo "==================================================================="
	@echo "Running Property Test: System Level Cache Functionality"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_slc.vvp $(SOURCES) $(SRC_DIR)/slc_cache.sv tb_slc_properties.sv
	vvp test_slc.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/slc_cache.sv tb_slc_properties.sv -o simv_slc
	./simv_slc
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test MESI State Machine Properties
test_mesi: tb_mesi_properties.sv $(SOURCES) $(SRC_DIR)/mesi_state_machine.sv
	@echo "==================================================================="
	@echo "Running Property Test: MESI State Machine Correctness"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_mesi.vvp $(SOURCES) $(SRC_DIR)/mesi_state_machine.sv tb_mesi_properties.sv
	vvp test_mesi.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/mesi_state_machine.sv tb_mesi_properties.sv -o simv_mesi
	./simv_mesi
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Snoop Filter Properties
test_snoop_filter: tb_snoop_filter_properties.sv $(SOURCES) $(SRC_DIR)/snoop_filter.sv
	@echo "==================================================================="
	@echo "Running Property Test: Snoop Filter Optimization"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_snoop_filter.vvp $(SOURCES) $(SRC_DIR)/snoop_filter.sv tb_snoop_filter_properties.sv
	vvp test_snoop_filter.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/snoop_filter.sv tb_snoop_filter_properties.sv -o simv_snoop_filter
	./simv_snoop_filter
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test HN-F Integration
test_hn_f_integration: tb_hn_f_integration.sv $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/axi_if.sv $(SRC_DIR)/slc_cache.sv $(SRC_DIR)/directory_manager.sv $(SRC_DIR)/mesi_state_machine.sv $(SRC_DIR)/snoop_filter.sv $(SRC_DIR)/hn_f.sv
	@echo "==================================================================="
	@echo "Running Integration Test: HN-F Complete Coherency Flow"
	@echo "Task: 8.2 编写 HN-F 集成测试"
	@echo "Requirements: 4.1, 4.2, 4.3, 4.4"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_hn_f_integration.vvp $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/axi_if.sv $(SRC_DIR)/slc_cache.sv $(SRC_DIR)/directory_manager.sv $(SRC_DIR)/mesi_state_machine.sv $(SRC_DIR)/snoop_filter.sv $(SRC_DIR)/hn_f.sv tb_hn_f_integration.sv
	vvp test_hn_f_integration.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/axi_if.sv $(SRC_DIR)/slc_cache.sv $(SRC_DIR)/directory_manager.sv $(SRC_DIR)/mesi_state_machine.sv $(SRC_DIR)/snoop_filter.sv $(SRC_DIR)/hn_f.sv tb_hn_f_integration.sv -o simv_hn_f_integration
	./simv_hn_f_integration
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test SN-F Multi-Channel Parallel Access Properties
test_sn_f_multichannel: tb_sn_f_multichannel_properties.sv $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/ddr_if.sv $(SRC_DIR)/sn_f.sv
	@echo "==================================================================="
	@echo "Running Property Test: SN-F Multi-Channel Parallel Access"
	@echo "Feature: coh-noc-architecture, Property 16"
	@echo "Task: 10.4 为多通道访问编写属性测试"
	@echo "Requirements: 6.4"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	@echo "WARNING: This test requires SystemVerilog features not supported by Iverilog"
	@echo "Please use VCS, Xcelium, or Questa simulator"
	@exit 1
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/ddr_if.sv $(SRC_DIR)/sn_f.sv tb_sn_f_multichannel_properties.sv -o simv_sn_f_multichannel
	./simv_sn_f_multichannel
else ifeq ($(SIM),xcelium)
	xrun -sv -timescale 1ns/1ps $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/ddr_if.sv $(SRC_DIR)/sn_f.sv tb_sn_f_multichannel_properties.sv
else ifeq ($(SIM),questa)
	vlog -sv $(SOURCES) $(SRC_DIR)/interfaces/xp_port_if.sv $(SRC_DIR)/interfaces/ddr_if.sv $(SRC_DIR)/sn_f.sv tb_sn_f_multichannel_properties.sv
	vsim -c tb_sn_f_multichannel_properties -do "run -all; quit"
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif

# Test Error Handling (Simplified)
test_error_handling: tb_error_handling_simple.sv $(SOURCES)
	@echo "==================================================================="
	@echo "Running Error Handling Tests"
	@echo "Task: 13.3 编写错误处理测试"
	@echo "Testing error detection, reporting, and recovery mechanisms"
	@echo "==================================================================="
ifeq ($(SIM),iverilog)
	iverilog -g2012 -o test_error_handling_simple.vvp $(SOURCES) tb_error_handling_simple.sv
	vvp test_error_handling_simple.vvp
else ifeq ($(SIM),vcs)
	vcs -sverilog -full64 +v2k -timescale=1ns/1ps $(SOURCES) tb_error_handling_simple.sv -o simv_error_handling
	./simv_error_handling
else
	@echo "Unsupported simulator: $(SIM)"
	@exit 1
endif
