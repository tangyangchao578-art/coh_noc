# XP Router Unit Tests

## Overview
This document describes the unit tests created for the XP Router module to test edge cases, error conditions, and port contention handling as specified in Requirements 3.1 and 3.3.

## Test File
- **File**: `tb_xp_router_unit.sv`
- **Requirements**: 3.1 (Flit forwarding), 3.3 (Buffering when output port busy)

## Test Cases

### 1. Reset Behavior (Requirement 3.1)
- **Purpose**: Verify that router properly initializes on reset
- **Test**: Checks that all outputs are inactive during reset
- **Edge Case**: System initialization

### 2. Buffer Full Backpressure (Requirement 3.3)
- **Purpose**: Verify that router asserts backpressure when buffer is full
- **Test**: Sends flits until buffer is full, verifies ready signal deasserts
- **Edge Case**: Buffer overflow prevention

### 3. Output Port Busy Buffering (Requirement 3.3)
- **Purpose**: Verify that flits are buffered when output port is busy
- **Test**: Blocks output port, sends flit, verifies buffering, then unblocks and verifies forwarding
- **Error Condition**: Output port unavailable

### 4. Port Contention - Same Output Port (Requirements 3.1, 3.3)
- **Purpose**: Verify arbitration when multiple inputs target the same output
- **Test**: Sends flits from north and south ports both targeting east port
- **Edge Case**: Multiple inputs competing for same output

### 5. Port Contention - Different VCs (Requirements 3.1, 3.3)
- **Purpose**: Verify that different VCs can be forwarded independently
- **Test**: Sends flits on different virtual channels targeting same output
- **Edge Case**: VC isolation during contention

### 6. Simultaneous Multi-Port Input (Requirement 3.1)
- **Purpose**: Verify router handles inputs from multiple ports simultaneously
- **Test**: Sends flits from all 5 ports simultaneously with different targets
- **Edge Case**: Maximum input load

### 7. Zero Credit Blocking (Requirement 3.3)
- **Purpose**: Verify that transmission stops when credits are exhausted
- **Test**: Sends more flits than available credits, verifies credit consumption
- **Error Condition**: Credit exhaustion

### 8. Edge Case Target Coordinates (Requirement 3.1)
- **Purpose**: Verify router handles edge case coordinates
- **Test**: Sends flit with maximum coordinate values (0xF, 0xF)
- **Edge Case**: Boundary coordinates

### 9. Same Node Loopback (Requirement 3.1)
- **Purpose**: Verify router handles flits destined for itself
- **Test**: Sends flit from local port targeting same router coordinates
- **Edge Case**: Self-targeting flit

## Running the Tests

### Using Makefile
```bash
make test_xp_router_unit
```

### Manual Compilation
```bash
iverilog -g2012 -o test_xp_unit.vvp \
    ../src/coh_noc_pkg.sv \
    ../src/coh_noc_types.sv \
    ../src/xp_router_compute.sv \
    ../src/vc_buffer.sv \
    ../src/vc_buffer_manager.sv \
    ../src/credit_flow_control.sv \
    ../src/xp_router.sv \
    tb_xp_router_unit.sv

vvp test_xp_unit.vvp
```

## Test Coverage

The unit tests complement the existing property-based tests by focusing on:
- **Specific edge cases** that are difficult to generate randomly
- **Error conditions** that require precise setup
- **Port contention scenarios** with known inputs and expected outputs
- **Boundary conditions** like buffer full, zero credits, and maximum coordinates

## Notes

- Tests use minimal, focused scenarios to verify specific behaviors
- Each test is independent and cleans up after itself
- Tests verify both correct operation and proper error handling
- Iverilog compatibility: Replaced `break` statements with loop index manipulation
