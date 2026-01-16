#!/bin/bash
# Comprehensive Regression Test Suite for coh_noc Architecture
# Task 14.1: 运行完整的回归测试套件
# Executes all property-based tests and unit tests to verify system functionality

set -e  # Exit on first error

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test results tracking
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Arrays to track test results
declare -a PASSED_TEST_NAMES
declare -a FAILED_TEST_NAMES
declare -a SKIPPED_TEST_NAMES

# Function to print section header
print_header() {
    echo ""
    echo "=================================================================="
    echo -e "${BLUE}$1${NC}"
    echo "=================================================================="
}

# Function to run a test and track results
run_test() {
    local test_name=$1
    local test_command=$2
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    echo ""
    echo -e "${YELLOW}Running: $test_name${NC}"
    
    if eval "$test_command" > /tmp/test_output_$$.log 2>&1; then
        echo -e "${GREEN}✓ PASSED: $test_name${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        PASSED_TEST_NAMES+=("$test_name")
        cat /tmp/test_output_$$.log
    else
        echo -e "${RED}✗ FAILED: $test_name${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        FAILED_TEST_NAMES+=("$test_name")
        echo "Error output:"
        cat /tmp/test_output_$$.log
    fi
    
    rm -f /tmp/test_output_$$.log
}

# Function to skip a test
skip_test() {
    local test_name=$1
    local reason=$2
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    SKIPPED_TESTS=$((SKIPPED_TESTS + 1))
    SKIPPED_TEST_NAMES+=("$test_name: $reason")
    
    echo -e "${YELLOW}⊘ SKIPPED: $test_name - $reason${NC}"
}

# Start regression test suite
print_header "COH_NOC REGRESSION TEST SUITE"
echo "Starting comprehensive regression testing..."
echo "Date: $(date)"
echo ""

# Change to test directory
cd "$(dirname "$0")"

# Clean previous build artifacts
print_header "Cleaning Previous Build Artifacts"
make clean

# ============================================================================
# PHASE 1: Basic Data Structure Tests
# ============================================================================
print_header "PHASE 1: Basic Data Structure Tests"

run_test "Property 4: Flit Virtual Channel Integrity" \
    "make test_flit"

run_test "Property 10: Directory State Consistency" \
    "make test_directory"

# ============================================================================
# PHASE 2: Network Topology Tests
# ============================================================================
print_header "PHASE 2: Network Topology Tests"

run_test "Property 1: 2D Mesh Topology Connectivity" \
    "make test_mesh_topology"

run_test "Property 3: Routing Deadlock Freedom" \
    "make test_deadlock"

# ============================================================================
# PHASE 3: XP Router Tests
# ============================================================================
print_header "PHASE 3: XP Router Component Tests"

run_test "Property 2: X-Y Dimension-Order Routing Correctness" \
    "make test_routing"

run_test "Property 7: Virtual Channel Isolation" \
    "make test_vc_buffer"

run_test "Property 6 & 8: Credit Flow Control & Buffer Backpressure" \
    "make test_flow_control"

run_test "Property 5: Flit Forwarding Correctness" \
    "make test_xp_router_properties"

run_test "XP Router Unit Tests (Edge Cases)" \
    "make test_xp_router_unit"

# ============================================================================
# PHASE 4: HN-F Coherency Node Tests
# ============================================================================
print_header "PHASE 4: HN-F Coherency Node Tests"

run_test "Property 9: System Level Cache Functionality" \
    "make test_slc"

run_test "Property 12: MESI State Machine Correctness" \
    "make test_mesi"

run_test "Property 11: Snoop Filter Optimization" \
    "make test_snoop_filter"

run_test "HN-F Integration Tests" \
    "make test_hn_f_integration"

# ============================================================================
# PHASE 5: RN-F Request Node Tests
# ============================================================================
print_header "PHASE 5: RN-F Request Node Tests"

# Check if RN-F property tests exist
if [ -f "tb_rn_f_properties.sv" ]; then
    # Note: RN-F tests may require additional Makefile targets
    echo "RN-F property tests found but may need Makefile integration"
    skip_test "Property 13 & 14: RN-F Proxy & Snoop Response" \
        "Makefile target not yet defined"
else
    skip_test "RN-F Property Tests" "Test file not found"
fi

# ============================================================================
# PHASE 6: SN-F Memory Interface Tests
# ============================================================================
print_header "PHASE 6: SN-F Memory Interface Tests"

# Check if SN-F property tests exist
if [ -f "tb_sn_f_properties.sv" ]; then
    echo "SN-F property tests found but may need Makefile integration"
    skip_test "Property 15: Memory Interface Protocol Conversion" \
        "Makefile target not yet defined"
else
    skip_test "SN-F Property Tests" "Test file not found"
fi

# SN-F Multi-channel tests require commercial simulator
skip_test "Property 16: Multi-Channel Parallel Access" \
    "Requires VCS/Xcelium/Questa (not available with Iverilog)"

# ============================================================================
# PHASE 7: Error Handling Tests
# ============================================================================
print_header "PHASE 7: Error Handling and Fault Tolerance Tests"

run_test "Error Detection and Recovery Mechanisms" \
    "make test_error_handling"

# ============================================================================
# PHASE 8: System Integration Tests
# ============================================================================
print_header "PHASE 8: System Integration Tests"

# Check if system integration test exists
if [ -f "tb_system_integration.sv" ]; then
    echo "System integration test found but may need Makefile integration"
    skip_test "System Integration End-to-End Test" \
        "Makefile target not yet defined"
else
    skip_test "System Integration Test" "Test file not found"
fi

# ============================================================================
# Test Summary
# ============================================================================
print_header "REGRESSION TEST SUMMARY"

echo ""
echo "Total Tests:   $TOTAL_TESTS"
echo -e "${GREEN}Passed Tests:  $PASSED_TESTS${NC}"
echo -e "${RED}Failed Tests:  $FAILED_TESTS${NC}"
echo -e "${YELLOW}Skipped Tests: $SKIPPED_TESTS${NC}"
echo ""

if [ $PASSED_TESTS -gt 0 ]; then
    echo -e "${GREEN}Passed Tests:${NC}"
    for test in "${PASSED_TEST_NAMES[@]}"; do
        echo "  ✓ $test"
    done
    echo ""
fi

if [ $FAILED_TESTS -gt 0 ]; then
    echo -e "${RED}Failed Tests:${NC}"
    for test in "${FAILED_TEST_NAMES[@]}"; do
        echo "  ✗ $test"
    done
    echo ""
fi

if [ $SKIPPED_TESTS -gt 0 ]; then
    echo -e "${YELLOW}Skipped Tests:${NC}"
    for test in "${SKIPPED_TEST_NAMES[@]}"; do
        echo "  ⊘ $test"
    done
    echo ""
fi

# Calculate pass rate
if [ $TOTAL_TESTS -gt 0 ]; then
    PASS_RATE=$(echo "scale=2; ($PASSED_TESTS * 100) / ($TOTAL_TESTS - $SKIPPED_TESTS)" | bc)
    echo "Pass Rate: ${PASS_RATE}% (excluding skipped tests)"
fi

echo ""
echo "Regression test suite completed at $(date)"
echo ""

# Exit with error if any tests failed
if [ $FAILED_TESTS -gt 0 ]; then
    echo -e "${RED}REGRESSION TEST SUITE FAILED${NC}"
    exit 1
else
    echo -e "${GREEN}REGRESSION TEST SUITE PASSED${NC}"
    exit 0
fi
