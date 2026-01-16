# CoH NoC System Integration

This document describes the system-level integration of the coherent Network-on-Chip (NoC) architecture.

## Overview

The CoH NoC system integrates the following components into a complete coherent interconnect:

- **2D Mesh Network**: Provides the physical topology and routing infrastructure
- **RN-F Nodes**: Request nodes that proxy CPU memory accesses
- **HN-F Nodes**: Home nodes that maintain cache coherence
- **SN-F Nodes**: Slave nodes that interface with memory controllers

## System Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    CoH NoC System                           │
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐                │
│  │  CPU 0   │  │  CPU 1   │  │  CPU 2   │                │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘                │
│       │             │             │                        │
│  ┌────▼─────┐  ┌───▼──────┐  ┌───▼──────┐                │
│  │  RN-F 0  │  │  RN-F 1  │  │  RN-F 2  │                │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘                │
│       │             │             │                        │
│  ┌────▼─────────────▼─────────────▼──────┐                │
│  │                                        │                │
│  │         2D Mesh Network (3x3)         │                │
│  │                                        │                │
│  └────┬─────────────┬─────────────┬──────┘                │
│       │             │             │                        │
│  ┌────▼─────┐  ┌───▼──────┐  ┌───▼──────┐                │
│  │  HN-F 0  │  │  HN-F 1  │  │  SN-F 0  │                │
│  │  (SLC)   │  │  (SLC)   │  │  (DDR)   │                │
│  └──────────┘  └──────────┘  └────┬─────┘                │
│                                    │                        │
│                               ┌────▼─────┐                 │
│                               │  Memory  │                 │
│                               └──────────┘                 │
└─────────────────────────────────────────────────────────────┘
```

## Module Hierarchy

### Top-Level Modules

1. **coh_noc_system** (`src/coh_noc_system.sv`)
   - Fixed configuration system with compile-time parameters
   - Instantiates mesh network and all node types
   - Handles node-to-mesh connections
   - Provides system status outputs

2. **coh_noc_system_configurable** (`src/coh_noc_system_configurable.sv`)
   - Runtime configurable system
   - Includes configuration interface
   - Supports dynamic mesh sizing and node placement

3. **coh_noc_config** (`src/coh_noc_config.sv`)
   - Configuration register interface
   - Mesh size configuration
   - Node placement configuration
   - Buffer and flow control parameters

## Configuration

### Fixed Configuration (coh_noc_system)

Parameters:
- `MESH_SIZE_X`: Mesh width (default: 3)
- `MESH_SIZE_Y`: Mesh height (default: 3)
- `NUM_RN_F`: Number of RN-F nodes (default: 4)
- `NUM_HN_F`: Number of HN-F nodes (default: 2)
- `NUM_SN_F`: Number of SN-F nodes (default: 2)
- `SN_F_CHANNELS`: Memory channels per SN-F (default: 4)

### Runtime Configuration (coh_noc_system_configurable)

Configuration registers (accessed via cfg_* interface):

| Address | Register | Description |
|---------|----------|-------------|
| 0x0000 | System Control | Lock, reset, enable bits |
| 0x0004 | Mesh Size | X size [7:0], Y size [15:8] |
| 0x0008 | Node Counts | RN-F[7:0], HN-F[15:8], SN-F[23:16] |
| 0x000C | Buffer Config | Depth[7:0], VCs[10:8], Credits[23:16] |
| 0x0010 | SN-F Config | Channels[3:0] |
| 0x0100+ | Node Placement | X, Y, Type, ID per node |

## Node Placement

The system uses a placement table to map nodes to mesh positions:

```systemverilog
// Example placement for 3x3 mesh:
// (0,0): RN-F 0    (1,0): RN-F 1    (2,0): RN-F 2
// (0,1): RN-F 3    (1,1): HN-F 0    (2,1): HN-F 1
// (0,2): SN-F 0    (1,2): SN-F 1    (2,2): Empty
```

Node types:
- `2'b00`: Empty (no node)
- `2'b01`: RN-F (Request Node)
- `2'b10`: HN-F (Home Node)
- `2'b11`: SN-F (Slave Node)

## Interfaces

### CPU Interface (cpu_if)

Used by RN-F nodes to connect to CPUs:
- Request channel: valid, ready, read, addr, size, data, qos
- Response channel: valid, ready, data, error, txn_id

### Memory Interface (ddr_if)

Used by SN-F nodes to connect to memory controllers:
- Command channel: valid, ready, read, addr, len, size
- Write data channel: valid, ready, data, strb, last
- Read data channel: valid, ready, data, last, resp

### Network Interface (xp_port_if)

Used for mesh network connections:
- Flit transmission: valid, ready, flit, vc_id
- Flow control: credit_count, credit_return
- Channel type identification

## Data Flow

### Read Transaction Flow

1. CPU issues read request to RN-F
2. RN-F checks L1 cache
3. On miss, RN-F sends REQ to HN-F via mesh
4. HN-F checks SLC and directory
5. HN-F may send SNP to other RN-Fs
6. HN-F sends REQ to SN-F if needed
7. SN-F accesses memory
8. Data returns via DAT channel
9. HN-F updates SLC and directory
10. Data forwarded to requesting RN-F
11. RN-F updates L1 and responds to CPU

### Write Transaction Flow

1. CPU issues write request to RN-F
2. RN-F sends REQ to HN-F via mesh
3. HN-F invalidates other copies via SNP
4. HN-F grants exclusive access
5. RN-F updates L1 cache
6. Write-back to memory via SN-F (if needed)
7. Response sent to CPU

## Testing

### System Integration Test

The system integration test (`test/tb_system_integration.sv`) validates:

1. **Basic Read/Write**: Single CPU read and write operations
2. **Cache Coherence**: Multi-CPU access to shared data
3. **Parallel Access**: Concurrent operations from multiple CPUs
4. **Stress Test**: Random access patterns

### Running Tests

```bash
# Compile and run system integration test
cd test
make test_system_integration

# View waveforms
gtkwave test_system_integration.vcd
```

### Test Scenarios

#### Test 1: Basic Read/Write
- CPU 0 writes data to address 0x1000
- CPU 0 reads back from address 0x1000
- Verifies data integrity

#### Test 2: Cache Coherence
- CPU 0 writes data to address 0x2000
- CPU 1 reads from address 0x2000
- Verifies coherent data is returned

#### Test 3: Parallel Access
- All CPUs write to different addresses simultaneously
- Each CPU reads back its own data
- Verifies no interference between transactions

#### Test 4: Stress Test
- 100 random read/write operations
- Random CPU selection
- Random address generation
- Verifies system stability under load

## Performance Characteristics

### Latency

- **L1 Hit**: 1-2 cycles
- **SLC Hit**: 10-15 cycles
- **Memory Access**: 50-100 cycles
- **Coherence Snoop**: 20-30 cycles

### Throughput

- **Per-Link Bandwidth**: 512 bits/cycle
- **Aggregate Bandwidth**: Scales with mesh size
- **Memory Bandwidth**: 4 channels × 512 bits/cycle per SN-F

### Scalability

- Mesh size: Up to 8×8 (configurable)
- RN-F nodes: Up to 16
- HN-F nodes: Up to 8
- SN-F nodes: Up to 8

## Requirements Coverage

This system integration addresses all requirements:

- **Req 1.1, 1.4**: 2D Mesh topology with configurable size
- **Req 2.1-2.6**: CHI protocol with all virtual channels
- **Req 3.1-3.5**: XP router with routing and flow control
- **Req 4.1-4.6**: HN-F with SLC, directory, and MESI
- **Req 5.1-5.5**: RN-F with L1 cache and CPU interface
- **Req 6.1-6.4**: SN-F with memory interface and multi-channel
- **Req 7.1-7.5**: Directory mechanism for coherence
- **Req 8.1-8.4**: Credit-based flow control

## Future Enhancements

1. **Dynamic Reconfiguration**: Hot-swappable node configuration
2. **Power Management**: Clock gating and power domains
3. **QoS Support**: Priority-based arbitration
4. **Error Recovery**: Retry mechanisms and error correction
5. **Performance Monitoring**: Transaction counters and profiling
6. **Formal Verification**: Model checking for deadlock freedom

## References

- ARM AMBA CHI Specification
- ARM CMN-600/700 Technical Reference Manual
- Design Document: `.kiro/specs/coh-noc-architecture/design.md`
- Requirements Document: `.kiro/specs/coh-noc-architecture/requirements.md`
