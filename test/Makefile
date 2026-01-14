# Makefile for coh_noc Property-Based Tests

# Simulator selection (default: iverilog)
SIM ?= iverilog

# Source files
SRC_DIR = ../src
TEST_DIR = .

SOURCES = \
	$(SRC_DIR)/coh_noc_pkg.sv \
	$(SRC_DIR)/coh_noc_types.sv

# Test files
TESTS = \
	tb_flit_properties.sv \
	tb_directory_properties.sv

# Simulation output
SIM_OUT = sim_out
VVP_OUT = test.vvp

# Targets
.PHONY: all clean test_flit test_directory

all: test_flit test_directory

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

# Clean build artifacts
clean:
	rm -rf $(SIM_OUT) $(VVP_OUT) simv simv.daidir csrc ucli.key *.log *.vcd

.DEFAULT_GOAL := all
