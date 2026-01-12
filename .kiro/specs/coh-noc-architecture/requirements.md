# 需求文档

## 介绍

coh_noc 是一个片上一致性互连网络项目，目标是对标 ARM CMN-600/700 的架构。该系统需要实现高性能的片上网络通信，支持多核处理器之间的缓存一致性协议，并提供可扩展的 2D Mesh 拓扑结构。

## 术语表

- **XP (Crosspoint)**: 网格路由器节点，负责 Flit 转发和流控
- **HN-F (Home Node Fully-coherent)**: 完全一致性主节点，系统的一致性控制点
- **RN-F (Request Node Fully-coherent)**: 完全一致性请求节点，代理 CPU 的请求
- **SN-F (Slave Node)**: 从节点，内存控制器接口
- **Flit**: 流控制单元，网络传输的基本数据包
- **CHI (Coherent Hub Interface)**: ARM 一致性集线器接口协议
- **SLC (System Level Cache)**: 系统级缓存
- **Directory**: 目录机制，追踪缓存行副本的分布状态

## 需求

### 需求 1: 2D Mesh 拓扑结构

**用户故事:** 作为系统架构师，我希望实现 2D Mesh 网格拓扑结构，以便提供可扩展的片上网络连接。

#### 验收标准

1. THE System SHALL 实现 2D Mesh 网格拓扑结构，类似于 CMN 的 XP Crosspoint grid
2. WHEN 节点需要通信时，THE System SHALL 使用 X-Y 维序路由算法
3. THE System SHALL 防止路由死锁的发生
4. THE System SHALL 支持网格的动态扩展和配置

### 需求 2: AMBA CHI 通信协议

**用户故事:** 作为网络协议设计师，我希望基于简化版 AMBA CHI 协议实现通信，以便与 ARM 生态系统兼容。

#### 验收标准

1. THE System SHALL 实现基于简化版 AMBA CHI 协议的通信机制
2. THE System SHALL 定义符合 CHI 协议规范的 Flit 格式，包含必要的控制字段和数据载荷
3. THE System SHALL 支持 REQ (Request) 物理/虚拟通道
4. THE System SHALL 支持 RSP (Response) 物理/虚拟通道
5. THE System SHALL 支持 DAT (Data) 物理/虚拟通道
6. THE System SHALL 支持 SNP (Snoop) 物理/虚拟通道

### 需求 3: XP Crosspoint 路由器

**用户故事:** 作为网络设计师，我希望实现 XP 路由器节点，以便在网格中转发数据包并进行流量控制。

#### 验收标准

1. THE XP_Router SHALL 转发接收到的 Flit 到正确的输出端口
2. THE XP_Router SHALL 实现基于信用的流量控制机制
3. WHEN 输出端口繁忙时，THE XP_Router SHALL 缓存 Flit 直到端口可用
4. THE XP_Router SHALL 根据 X-Y 维序路由算法计算路由路径
5. THE XP_Router SHALL 维护每个虚拟通道的独立缓冲区

### 需求 4: HN-F 一致性主节点

**用户故事:** 作为缓存一致性设计师，我希望实现 HN-F 节点，以便作为系统的一致性控制点。

#### 验收标准

1. THE HN_F SHALL 作为系统的 Point of Coherency
2. THE HN_F SHALL 包含系统级缓存 (SLC) 功能
3. THE HN_F SHALL 实现监听过滤器 (Snoop Filter) 功能
4. THE HN_F SHALL 维护 directory 状态以追踪缓存行副本
5. WHEN 接收到缓存请求时，THE HN_F SHALL 根据 directory 状态决定是否需要发送 snoop 请求
6. THE HN_F SHALL 实现类似 MESI 协议的缓存一致性状态机

### 需求 5: RN-F 请求节点

**用户故事:** 作为 CPU 接口设计师，我希望实现 RN-F 节点，以便代理 CPU 发起内存访问请求。

#### 验收标准

1. THE RN_F SHALL 代理 CPU 发起读写请求
2. THE RN_F SHALL 维护本地缓存一致性状态
3. WHEN 接收到 snoop 请求时，THE RN_F SHALL 响应缓存行状态
4. THE RN_F SHALL 处理缓存未命中并向 HN-F 发送请求
5. THE RN_F SHALL 实现写回和写穿透策略

### 需求 6: SN-F 内存接口节点

**用户故事:** 作为内存子系统设计师，我希望实现 SN-F 节点，以便连接到 DDR/HBM 内存控制器。

#### 验收标准

1. THE SN_F SHALL 提供到 DDR/HBM 内存控制器的接口
2. WHEN 接收到内存访问请求时，THE SN_F SHALL 转换为内存控制器协议
3. THE SN_F SHALL 处理内存访问的延迟和带宽管理
4. THE SN_F SHALL 支持多个内存通道的并行访问

### 需求 7: Directory 机制

**用户故事:** 作为一致性协议设计师，我希望实现 directory 机制，以便高效地维护缓存一致性。

#### 验收标准

1. THE Directory SHALL 追踪每个缓存行在哪些 RN-F 节点中有副本
2. THE Directory SHALL 维护每个缓存行的一致性状态
3. WHEN 缓存行状态改变时，THE Directory SHALL 更新相应的状态信息
4. THE Directory SHALL 支持 MESI 或类似的一致性协议状态
5. THE Directory SHALL 优化 snoop 请求的发送，只向持有副本的节点发送

### 需求 8: 流量控制机制

**用户故事:** 作为网络性能优化师，我希望实现高效的流量控制，以便防止网络拥塞并保证服务质量。

#### 验收标准

1. THE System SHALL 实现基于信用的流量控制机制
2. WHEN 接收缓冲区满时，THE System SHALL 停止发送数据直到有可用空间
3. THE System SHALL 为每个虚拟通道维护独立的信用计数
4. THE System SHALL 支持背压机制以防止缓冲区溢出