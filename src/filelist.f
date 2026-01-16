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

# Core modules
src/vc_buffer.sv
src/vc_buffer_manager.sv
src/credit_flow_control.sv
src/xp_router_compute.sv
src/xp_router.sv
src/mesh_2d_network.sv
src/slc_cache.sv
src/directory_manager.sv
src/mesi_state_machine.sv
src/snoop_filter.sv
src/l1_cache.sv
src/rn_f.sv
src/hn_f.sv
src/sn_f.sv

# System integration modules
src/coh_noc_config.sv
src/coh_noc_system.sv
src/coh_noc_system_configurable.sv
