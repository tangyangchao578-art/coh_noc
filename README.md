# coh_noc - Coherent Network-on-Chip Architecture

## Overview

coh_noc is a high-performance on-chip coherent interconnect network system that implements a 2D Mesh topology based on the AMBA CHI (Coherent Hub Interface) protocol. The system targets ARM CMN-600/700 architecture compatibility and supports cache coherency protocols for multi-core processors.

## Project Structure

```
src/
├── coh_noc_pkg.sv          # Core package with CHI protocol definitions
├── coh_noc_types.sv        # Utility functions and type conversions
├── filelist.f              # SystemVerilog compilation file list
└── interfaces/
    ├── xp_port_if.sv        # XP Crosspoint router port interface
    ├── cpu_if.sv            # CPU interface for RN-F nodes
    ├── axi_if.sv            # AXI4 interface for memory access
    └── ddr_if.sv            # DDR/HBM memory controller interface
```

## CHI Protocol Implementation

### Channel-Specific Flit Formats

The implementation follows the official AMBA CHI specification with separate flit structures for each channel:

#### REQ Channel (Request)
- **req_flit_t**: Contains request opcodes, addressing, transaction management
- **Key Fields**: opcode, addr[47:0], txn_id, src_id, tgt_id, size, mem_attr, qos
- **Special Fields**: likely_shared, allow_retry, order, ns (non-secure)

#### RSP Channel (Response)  
- **rsp_flit_t**: Contains response opcodes and completion status
- **Key Fields**: opcode, txn_id, src_id, tgt_id, resp, fwd_state
- **Special Fields**: data_pull, cb_id (copy-back ID), pcrd_type

#### DAT Channel (Data)
- **dat_flit_t**: Contains data payload and data-specific metadata
- **Key Fields**: opcode, txn_id, data[511:0], dbid, be[63:0], data_id
- **Special Fields**: 
  - **DBID**: Data Buffer ID - 用于标识数据缓冲区，在写事务中由HN分配给RN
  - **BE**: Byte Enable - 64位字节使能信号，指示512位数据中哪些字节有效
  - **DataID**: 数据标识符 - 用于多flit数据传输中标识数据块顺序
  - **CCID**: Critical Chunk ID - 关键数据块标识符
  - **Poison**: 毒化位 - 指示数据是否被毒化（错误数据）
  - **DataCheck**: 数据校验位 - 用于数据完整性检查

#### SNP Channel (Snoop)
- **snp_flit_t**: Contains snoop requests for cache coherency
- **Key Fields**: opcode, addr[47:3], txn_id, src_id, fwd_txn_id
- **Special Fields**: do_not_goto_sd, ret_to_src, fwd_node_id

### CHI Operation Codes

#### Request Channel Opcodes
- **Read Operations**: ReadShared, ReadClean, ReadOnce, ReadUnique
- **Write Operations**: WriteBackFull, WriteCleanFull, WriteUniqueFull
- **Cache Maintenance**: CleanShared, CleanInvalid, MakeInvalid
- **Atomic Operations**: AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare

#### Response Channel Opcodes
- **Completion**: CompAck, Comp, CompData
- **Flow Control**: ReadReceipt, RetryAck, PCrGrant

#### Data Channel Opcodes
- **Data Transfer**: DataFlit, CompData, NonCopyBackWrData
- **Separated Data**: DataSepData

#### Snoop Channel Opcodes
- **Coherency**: SnpShared, SnpClean, SnpOnce, SnpUnique
- **Invalidation**: SnpCleanInvalid, SnpMakeInvalid

### Virtual Channels

The system supports four virtual channels as defined by CHI:
- **VC_REQ (00)**: Request channel for memory operations
- **VC_RSP (01)**: Response channel for completions
- **VC_DAT (10)**: Data channel for payload transfer
- **VC_SNP (11)**: Snoop channel for coherency operations

### CHI协议关键概念

#### DBID (Data Buffer ID)
DBID是CHI协议中的重要概念，用于写事务的数据缓冲区管理：
- **分配**: 由Home Node (HN-F)分配给Request Node (RN-F)
- **用途**: 标识RN-F应该将写数据发送到HN-F的哪个数据缓冲区
- **生命周期**: 在DBIDResp响应中发送给RN-F，RN-F在后续的写数据flit中使用
- **宽度**: 8位，支持最多256个并发数据缓冲区

#### 字节使能 (BE - Byte Enable)
- **宽度**: 64位，对应512位数据的每个字节
- **功能**: 指示数据flit中哪些字节包含有效数据
- **用途**: 支持部分写操作和非对齐访问

#### 数据ID (DataID)
- **用途**: 在多flit数据传输中标识数据块的顺序
- **宽度**: 3位，支持最多8个数据flit
- **应用**: 大于64字节的数据传输需要多个flit

- **Packet-Based Communication**: Each channel uses specific flit formats
- **Transaction ID Management**: 12-bit TxnID for transaction tracking
- **Node ID Addressing**: 8-bit source and target node identification
- **Quality of Service**: QoS support for traffic prioritization
- **Memory Attributes**: Support for different memory types and caching policies
- **Trace Support**: Trace tags for debugging and performance analysis
- **Error Handling**: Poison bits and data check mechanisms

## Network Architecture

### 2D Mesh Topology
- XP (Crosspoint) routers form the mesh interconnect
- X-Y dimension order routing for deadlock prevention
- Credit-based flow control with virtual channel support
- Support for HN-F, RN-F, and SN-F node types

### Node Types
- **RN-F**: Fully coherent request nodes (CPUs, GPUs)
- **HN-F**: Fully coherent home nodes (coherency controllers)
- **SN-F**: Slave nodes (memory controllers)

## Requirements Addressed

This corrected implementation addresses:
- **2.1, 2.2**: Accurate CHI protocol flit formats and operation codes
- **2.3-2.6**: Proper virtual channel support (REQ, RSP, DAT, SNP)
- **Interface definitions**: Foundation for all node types and network connections

## Compilation

Use the provided filelist for SystemVerilog compilation:
```bash
vcs -f src/filelist.f
```

Or with other simulators:
```bash
xvlog -f src/filelist.f
```

## Changes from Previous Version

1. **Separated Flit Structures**: Individual structures for each CHI channel
2. **Accurate Field Definitions**: Based on official CHI specification
3. **Extended Opcode Support**: Complete set of CHI opcodes per channel
4. **Proper Field Widths**: Correct bit widths for all protocol fields
5. **Channel-Specific Functions**: Separate utility functions for each channel type