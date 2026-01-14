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
.PHONY: all clean test_flit test_directory test_xp_router_unit

all: test_flit test_directory test_xp_router_unit

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

# Clean build artifacts
clean:
	rm -rf $(SIM_OUT) $(VVP_OUT) test_xp_unit.vvp simv simv_xp_unit simv.daidir csrc ucli.key *.log *.vcd

.DEFAULT_GOAL := all
