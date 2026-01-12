# =============================================================================
# coh_noc SystemVerilog File List
# =============================================================================

# Core package and type definitions
+incdir+src
+incdir+src/interfaces

# Package files (must be compiled first)
src/coh_noc_pkg.sv
src/coh_noc_types.sv

# Interface definitions
src/interfaces/xp_port_if.sv
src/interfaces/cpu_if.sv
src/interfaces/axi_if.sv
src/interfaces/ddr_if.sv