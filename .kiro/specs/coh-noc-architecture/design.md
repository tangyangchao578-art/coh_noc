# 设计文档

## 概述

coh_noc 是一个高性能片上一致性互连网络系统，采用 2D Mesh 拓扑结构，基于简化版 AMBA CHI 协议实现。系统支持多核处理器之间的缓存一致性通信，提供可扩展的网络架构，对标 ARM CMN-600/700 的功能特性。

## 架构

### 系统架构图

```mermaid
graph TB
    subgraph "2D Mesh Network"
        XP00[XP(0,0)] --- XP01[XP(0,1)] --- XP02[XP(0,2)]
        XP10[XP(1,0)] --- XP11[XP(1,1)] --- XP12[XP(1,2)]
        XP20[XP(2,0)] --- XP21[XP(2,1)] --- XP22[XP(2,2)]
        
        XP00 --- XP10 --- XP20
        XP01 --- XP11 --- XP21
        XP02 --- XP12 --- XP22
    end
    
    RNF1[RN-F CPU0] --- XP00
    RNF2[RN-F CPU1] --- XP01
    HNF1[HN-F Cache] --- XP11
    HNF2[HN-F Cache] --- XP12
    SNF1[SN-F DDR0] --- XP20
    SNF2[SN-F DDR1] --- XP21
```

### 拓扑结构设计

系统采用 2D Mesh 网格拓扑，每个网格节点为 XP (Crosspoint) 路由器。网格支持：
- X-Y 维序路由算法，确保无死锁
- 可配置的网格尺寸 (N×M)
- 每个 XP 节点支持最多 4 个本地设备连接

### 路由算法

采用 X-Y 维序路由：
1. 首先在 X 维度路由到目标列
2. 然后在 Y 维度路由到目标行
3. 保证路由的确定性和无死锁特性

## 组件和接口

### XP (Crosspoint) 路由器

#### 功能描述
XP 是网格中的路由节点，负责 Flit 的转发和流量控制。

#### 接口定义
```systemverilog
interface xp_port_if;
    // Flit 传输接口
    logic        valid;
    logic        ready;
    flit_t       flit;
    logic [3:0]  vc_id;    // 虚拟通道 ID
    
    // 流控信号
    logic [7:0]  credit_count;
    logic        credit_return;
endinterface

module xp_router #(
    parameter X_COORD = 0,
    parameter Y_COORD = 0
)(
    input  clk,
    input  rst_n,
    
    // 网格端口 (North, South, East, West)
    xp_port_if.slave  north_in,
    xp_port_if.master north_out,
    xp_port_if.slave  south_in,
    xp_port_if.master south_out,
    xp_port_if.slave  east_in,
    xp_port_if.master east_out,
    xp_port_if.slave  west_in,
    xp_port_if.master west_out,
    
    // 本地设备端口
    xp_port_if.slave  local_in,
    xp_port_if.master local_out
);
```

#### 内部结构
- **路由计算单元**: 根据目标地址计算输出端口
- **虚拟通道缓冲区**: 每个 VC 独立的 FIFO 缓冲区
- **仲裁器**: 处理多个输入端口到同一输出端口的竞争
- **流控单元**: 管理信用计数和背压

### HN-F (Home Node Fully-coherent)

#### 功能描述
HN-F 是系统的一致性控制点，包含系统级缓存和目录机制。

#### 接口定义
```systemverilog
module hn_f #(
    parameter CACHE_SIZE = 1024*1024,  // 1MB SLC
    parameter NUM_WAYS = 16,
    parameter DIRECTORY_ENTRIES = 4096
)(
    input clk,
    input rst_n,
    
    // 网络接口
    xp_port_if.master req_out,    // REQ 通道输出
    xp_port_if.slave  req_in,     // REQ 通道输入
    xp_port_if.master rsp_out,    // RSP 通道输出
    xp_port_if.slave  rsp_in,     // RSP 通道输入
    xp_port_if.master dat_out,    // DAT 通道输出
    xp_port_if.slave  dat_in,     // DAT 通道输入
    xp_port_if.master snp_out,    // SNP 通道输出
    xp_port_if.slave  snp_in,     // SNP 通道输入
    
    // 内存接口 (到 SN-F)
    axi_if.master mem_if
);
```

#### 内部组件
- **系统级缓存 (SLC)**: 16-way 组相联缓存
- **目录表**: 追踪缓存行的共享状态
- **监听过滤器**: 优化 snoop 请求的发送
- **一致性状态机**: 处理 MESI 协议状态转换

### RN-F (Request Node Fully-coherent)

#### 功能描述
RN-F 代理 CPU 发起内存访问请求，维护本地缓存一致性。

#### 接口定义
```systemverilog
module rn_f #(
    parameter CACHE_SIZE = 64*1024,   // 64KB L1 Cache
    parameter NUM_WAYS = 4
)(
    input clk,
    input rst_n,
    
    // CPU 接口
    cpu_if.slave cpu_req,
    cpu_if.master cpu_rsp,
    
    // 网络接口
    xp_port_if.master req_out,
    xp_port_if.slave  rsp_in,
    xp_port_if.slave  dat_in,
    xp_port_if.slave  snp_in,
    xp_port_if.master snp_rsp_out
);
```

### SN-F (Slave Node)

#### 功能描述
SN-F 提供到内存控制器的接口，处理内存访问请求。

#### 接口定义
```systemverilog
module sn_f (
    input clk,
    input rst_n,
    
    // 网络接口
    xp_port_if.slave  req_in,
    xp_port_if.master rsp_out,
    xp_port_if.master dat_out,
    
    // DDR/HBM 接口
    ddr_if.master ddr_ctrl
);
```

## 数据模型

### Flit 格式定义

```systemverilog
typedef struct packed {
    logic [7:0]   opcode;      // CHI 操作码
    logic [47:0]  addr;        // 48位物理地址
    logic [11:0]  txn_id;      // 事务 ID
    logic [7:0]   src_id;      // 源节点 ID
    logic [7:0]   tgt_id;      // 目标节点 ID
    logic [3:0]   size;        // 数据大小
    logic [2:0]   mem_attr;    // 内存属性
    logic [7:0]   qos;         // 服务质量
    logic [511:0] data;        // 数据载荷 (可选)
} flit_t;
```

### CHI 操作码定义

```systemverilog
typedef enum logic [7:0] {
    // Request 通道操作码
    REQ_READ_SHARED     = 8'h01,
    REQ_READ_CLEAN      = 8'h02,
    REQ_READ_UNIQUE     = 8'h07,
    REQ_WRITE_BACK      = 8'h08,
    REQ_WRITE_CLEAN     = 8'h09,
    REQ_WRITE_UNIQUE    = 8'h18,
    
    // Response 通道操作码
    RSP_COMP_ACK        = 8'h14,
    RSP_READ_RECEIPT    = 8'h15,
    RSP_COMP_DATA       = 8'h52,
    
    // Snoop 通道操作码
    SNP_SHARED          = 8'h20,
    SNP_CLEAN           = 8'h21,
    SNP_UNIQUE          = 8'h22
} chi_opcode_e;
```

### 目录状态定义

```systemverilog
typedef struct packed {
    logic [3:0]   state;       // MESI 状态
    logic [15:0]  sharer_mask; // 共享者位掩码
    logic [7:0]   owner_id;    // 拥有者节点 ID
    logic         dirty;       // 脏位
} directory_entry_t;

typedef enum logic [3:0] {
    DIR_INVALID   = 4'h0,
    DIR_SHARED    = 4'h1,
    DIR_EXCLUSIVE = 4'h2,
    DIR_MODIFIED  = 4'h3
} directory_state_e;
```

## 正确性属性

*属性是一个特征或行为，应该在系统的所有有效执行中保持为真——本质上是关于系统应该做什么的正式陈述。属性作为人类可读规范和机器可验证正确性保证之间的桥梁。*

现在我需要使用 prework 工具来分析验收标准的可测试性：

基于预工作分析，我将验收标准转换为可测试的正确性属性：

### 属性 1: 2D Mesh 拓扑连接性
*对于任意* 网格尺寸配置，系统应该正确建立 2D Mesh 拓扑连接，每个内部节点有 4 个邻居，边界节点有相应数量的邻居
**验证需求: Requirements 1.1, 1.4**

### 属性 2: X-Y 维序路由正确性  
*对于任意* 源坐标和目标坐标，路由算法应该生成先 X 维后 Y 维的路径，且路径长度为曼哈顿距离
**验证需求: Requirements 1.2, 3.4**

### 属性 3: 路由无死锁性
*对于任意* 流量模式和网络配置，系统不应该出现循环等待导致的死锁状态
**验证需求: Requirements 1.3**

### 属性 4: 虚拟通道功能完整性
*对于任意* CHI 消息类型，系统应该正确支持 REQ、RSP、DAT、SNP 四个虚拟通道的传输
**验证需求: Requirements 2.3, 2.4, 2.5, 2.6**

### 属性 5: Flit 转发正确性
*对于任意* 输入 Flit 和目标地址，XP 路由器应该将 Flit 转发到正确的输出端口
**验证需求: Requirements 3.1**

### 属性 6: 信用流控机制
*对于任意* 网络负载情况，系统应该正确维护信用计数，防止缓冲区溢出和下溢
**验证需求: Requirements 3.2, 8.1**

### 属性 7: 虚拟通道隔离性
*对于任意* 虚拟通道组合，不同 VC 的数据应该在独立缓冲区中处理，不会相互干扰
**验证需求: Requirements 3.5, 8.3**

### 属性 8: 缓冲区背压机制
*对于任意* 缓冲区满的情况，系统应该正确实施背压，停止数据发送直到空间可用
**验证需求: Requirements 3.3, 8.2, 8.4**

### 属性 9: 系统级缓存功能
*对于任意* 缓存访问请求，HN-F 的 SLC 应该正确处理缓存命中和未命中情况
**验证需求: Requirements 4.2**

### 属性 10: Directory 状态一致性
*对于任意* 缓存行操作，Directory 应该准确追踪缓存行在各 RN-F 节点的副本状态
**验证需求: Requirements 4.4, 7.1, 7.2, 7.3**

### 属性 11: Snoop 过滤优化
*对于任意* 缓存一致性操作，系统应该只向持有相关缓存行副本的节点发送 snoop 请求
**验证需求: Requirements 4.3, 4.5, 7.5**

### 属性 12: MESI 状态机正确性
*对于任意* 缓存一致性状态转换，系统应该遵循 MESI 协议的状态转换规则
**验证需求: Requirements 4.6**

### 属性 13: RN-F 代理功能
*对于任意* CPU 内存访问请求，RN-F 应该正确转换为相应的网络消息并处理响应
**验证需求: Requirements 5.1, 5.4**

### 属性 14: Snoop 响应正确性
*对于任意* 接收到的 snoop 请求，RN-F 应该根据本地缓存状态返回正确的响应
**验证需求: Requirements 5.3**

### 属性 15: 内存接口协议转换
*对于任意* 网络内存访问请求，SN-F 应该正确转换为内存控制器协议格式
**验证需求: Requirements 6.1, 6.2**

### 属性 16: 多通道并行访问
*对于任意* 并发内存访问请求，SN-F 应该正确处理多个内存通道的并行访问
**验证需求: Requirements 6.4**

## 错误处理

### 网络错误处理
- **Flit 损坏检测**: 使用 CRC 校验检测传输错误
- **超时处理**: 对长时间未响应的事务进行超时处理
- **重传机制**: 支持错误 Flit 的重传

### 一致性错误处理  
- **Directory 不一致**: 检测并修复 Directory 状态不一致
- **重复响应**: 处理重复的缓存一致性响应
- **孤儿事务**: 清理未完成的事务

### 流控错误处理
- **信用泄漏**: 检测并修复信用计数错误
- **死锁检测**: 实现死锁检测和恢复机制
- **缓冲区溢出**: 防止缓冲区溢出导致的数据丢失

## 测试策略

### 双重测试方法
系统采用单元测试和基于属性的测试相结合的方法：

**单元测试**:
- 验证特定示例和边界情况
- 测试组件间的集成点
- 验证错误条件和异常处理
- 专注于具体的功能验证

**基于属性的测试**:
- 验证跨所有输入的通用属性
- 通过随机化实现全面的输入覆盖
- 每个属性测试运行最少 100 次迭代
- 使用标签格式: **Feature: coh-noc-architecture, Property {number}: {property_text}**

### 测试配置
- **属性测试库**: 使用 SystemVerilog 的 UVM 随机化功能
- **最小迭代次数**: 每个属性测试 100 次迭代
- **覆盖率目标**: 代码覆盖率 > 95%，功能覆盖率 > 90%
- **测试环境**: 支持多种网格配置和流量模式

### 验证方法
- **形式化验证**: 对关键属性进行形式化证明
- **仿真验证**: 大规模系统级仿真
- **FPGA 原型**: 在 FPGA 上验证实际性能
- **回归测试**: 自动化回归测试套件