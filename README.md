# coh_noc - Coherent Network-on-Chip Architecture

## Overview

coh_noc is a high-performance on-chip coherent interconnect network system that implements a 2D Mesh topology based on a simplified AMBA CHI protocol. The system targets ARM CMN-600/700 architecture compatibility and supports cache coherency protocols for multi-core processors.

## Project Structure

```
src/
├── coh_noc_pkg.sv          # Core package with data types and protocol definitions
├── coh_noc_types.sv        # Utility functions and additional type definitions
├── filelist.f              # SystemVerilog compilation file list
└── interfaces/
    ├── xp_port_if.sv        # XP Crosspoint router port interface
    ├── cpu_if.sv            # CPU interface for RN-F nodes
    ├── axi_if.sv            # AXI4 interface for memory access
    └── ddr_if.sv            # DDR/HBM memory controller interface
```

## Key Components

### Core Data Types
- **flit_t**: Basic network packet structure following CHI protocol
- **chi_opcode_e**: CHI protocol operation codes for different transaction types
- **virtual_channel_e**: Virtual channel definitions (REQ, RSP, DAT, SNP)
- **directory_entry_t**: Directory state tracking for cache coherency

### Interfaces
- **xp_port_if**: Standardized port interface for XP router connections
- **cpu_if**: Interface between CPU and RN-F request nodes
- **axi_if**: Standard AXI4 interface for memory transactions
- **ddr_if**: Simplified DDR/HBM memory controller interface

### Network Architecture
- 2D Mesh topology with XP (Crosspoint) routers
- X-Y dimension order routing for deadlock prevention
- Credit-based flow control with virtual channel support
- Support for HN-F, RN-F, and SN-F node types

## Requirements Addressed

This implementation addresses the following requirements:
- **2.1, 2.2**: CHI protocol data structures and operation codes
- **2.3-2.6**: Virtual channel support (REQ, RSP, DAT, SNP)
- **Interface definitions**: Foundation for all node types and network connections

## Next Steps

The project structure is now established. Subsequent tasks will implement:
1. Flit data structures and CHI operation handling
2. XP router core functionality with routing algorithms
3. HN-F coherency home nodes with system-level cache
4. RN-F request nodes with CPU interfaces
5. SN-F slave nodes with memory controller interfaces
6. Complete system integration and testing

## Compilation

Use the provided filelist for SystemVerilog compilation:
```bash
vcs -f src/filelist.f
```

Or with other simulators:
```bash
xvlog -f src/filelist.f
```