# Comprehensive Regression Test Suite for coh_noc Architecture
# Task 14.1: 运行完整的回归测试套件
# Executes all property-based tests and unit tests to verify system functionality

# Test results tracking
$script:TotalTests = 0
$script:PassedTests = 0
$script:FailedTests = 0
$script:SkippedTests = 0
$script:PassedTestNames = @()
$script:FailedTestNames = @()
$script:SkippedTestNames = @()

# Function to print section header
function Print-Header {
    param([string]$Message)
    Write-Host ""
    Write-Host "==================================================================" -ForegroundColor Blue
    Write-Host $Message -ForegroundColor Blue
    Write-Host "==================================================================" -ForegroundColor Blue
}

# Function to run a test and track results
function Run-Test {
    param(
        [string]$TestName,
        [string]$TestCommand
    )
    
    $script:TotalTests++
    
    Write-Host ""
    Write-Host "Running: $TestName" -ForegroundColor Yellow
    
    try {
        $output = Invoke-Expression $TestCommand 2>&1
        $exitCode = $LASTEXITCODE
        
        if ($exitCode -eq 0) {
            Write-Host "✓ PASSED: $TestName" -ForegroundColor Green
            $script:PassedTests++
            $script:PassedTestNames += $TestName
            Write-Host $output
        } else {
            Write-Host "✗ FAILED: $TestName" -ForegroundColor Red
            $script:FailedTests++
            $script:FailedTestNames += $TestName
            Write-Host "Error output:" -ForegroundColor Red
            Write-Host $output
        }
    } catch {
        Write-Host "✗ FAILED: $TestName (Exception)" -ForegroundColor Red
        $script:FailedTests++
        $script:FailedTestNames += $TestName
        Write-Host "Exception: $_" -ForegroundColor Red
    }
}

# Function to skip a test
function Skip-Test {
    param(
        [string]$TestName,
        [string]$Reason
    )
    
    $script:TotalTests++
    $script:SkippedTests++
    $script:SkippedTestNames += "$TestName`: $Reason"
    
    Write-Host "⊘ SKIPPED: $TestName - $Reason" -ForegroundColor Yellow
}

# Start regression test suite
Print-Header "COH_NOC REGRESSION TEST SUITE"
Write-Host "Starting comprehensive regression testing..."
Write-Host "Date: $(Get-Date)"
Write-Host ""

# Change to test directory
Set-Location $PSScriptRoot

# Clean previous build artifacts
Print-Header "Cleaning Previous Build Artifacts"
make clean

# ============================================================================
# PHASE 1: Basic Data Structure Tests
# ============================================================================
Print-Header "PHASE 1: Basic Data Structure Tests"

Run-Test "Property 4: Flit Virtual Channel Integrity" "make test_flit"
Run-Test "Property 10: Directory State Consistency" "make test_directory"

# ============================================================================
# PHASE 2: Network Topology Tests
# ============================================================================
Print-Header "PHASE 2: Network Topology Tests"

Run-Test "Property 1: 2D Mesh Topology Connectivity" "make test_mesh_topology"
Run-Test "Property 3: Routing Deadlock Freedom" "make test_deadlock"

# ============================================================================
# PHASE 3: XP Router Tests
# ============================================================================
Print-Header "PHASE 3: XP Router Component Tests"

Run-Test "Property 2: X-Y Dimension-Order Routing Correctness" "make test_routing"
Run-Test "Property 7: Virtual Channel Isolation" "make test_vc_buffer"
Run-Test "Property 6 & 8: Credit Flow Control & Buffer Backpressure" "make test_flow_control"
Run-Test "Property 5: Flit Forwarding Correctness" "make test_xp_router_properties"
Run-Test "XP Router Unit Tests (Edge Cases)" "make test_xp_router_unit"

# ============================================================================
# PHASE 4: HN-F Coherency Node Tests
# ============================================================================
Print-Header "PHASE 4: HN-F Coherency Node Tests"

Run-Test "Property 9: System Level Cache Functionality" "make test_slc"
Run-Test "Property 12: MESI State Machine Correctness" "make test_mesi"
Run-Test "Property 11: Snoop Filter Optimization" "make test_snoop_filter"
Run-Test "HN-F Integration Tests" "make test_hn_f_integration"

# ============================================================================
# PHASE 5: RN-F Request Node Tests
# ============================================================================
Print-Header "PHASE 5: RN-F Request Node Tests"

if (Test-Path "tb_rn_f_properties.sv") {
    Write-Host "RN-F property tests found but may need Makefile integration"
    Skip-Test "Property 13 & 14: RN-F Proxy & Snoop Response" "Makefile target not yet defined"
} else {
    Skip-Test "RN-F Property Tests" "Test file not found"
}

# ============================================================================
# PHASE 6: SN-F Memory Interface Tests
# ============================================================================
Print-Header "PHASE 6: SN-F Memory Interface Tests"

if (Test-Path "tb_sn_f_properties.sv") {
    Write-Host "SN-F property tests found but may need Makefile integration"
    Skip-Test "Property 15: Memory Interface Protocol Conversion" "Makefile target not yet defined"
} else {
    Skip-Test "SN-F Property Tests" "Test file not found"
}

Skip-Test "Property 16: Multi-Channel Parallel Access" "Requires VCS/Xcelium/Questa (not available with Iverilog)"

# ============================================================================
# PHASE 7: Error Handling Tests
# ============================================================================
Print-Header "PHASE 7: Error Handling and Fault Tolerance Tests"

Run-Test "Error Detection and Recovery Mechanisms" "make test_error_handling"

# ============================================================================
# PHASE 8: System Integration Tests
# ============================================================================
Print-Header "PHASE 8: System Integration Tests"

if (Test-Path "tb_system_integration.sv") {
    Write-Host "System integration test found but may need Makefile integration"
    Skip-Test "System Integration End-to-End Test" "Makefile target not yet defined"
} else {
    Skip-Test "System Integration Test" "Test file not found"
}

# ============================================================================
# Test Summary
# ============================================================================
Print-Header "REGRESSION TEST SUMMARY"

Write-Host ""
Write-Host "Total Tests:   $script:TotalTests"
Write-Host "Passed Tests:  $script:PassedTests" -ForegroundColor Green
Write-Host "Failed Tests:  $script:FailedTests" -ForegroundColor Red
Write-Host "Skipped Tests: $script:SkippedTests" -ForegroundColor Yellow
Write-Host ""

if ($script:PassedTests -gt 0) {
    Write-Host "Passed Tests:" -ForegroundColor Green
    foreach ($test in $script:PassedTestNames) {
        Write-Host "  ✓ $test"
    }
    Write-Host ""
}

if ($script:FailedTests -gt 0) {
    Write-Host "Failed Tests:" -ForegroundColor Red
    foreach ($test in $script:FailedTestNames) {
        Write-Host "  ✗ $test"
    }
    Write-Host ""
}

if ($script:SkippedTests -gt 0) {
    Write-Host "Skipped Tests:" -ForegroundColor Yellow
    foreach ($test in $script:SkippedTestNames) {
        Write-Host "  ⊘ $test"
    }
    Write-Host ""
}

# Calculate pass rate
if ($script:TotalTests -gt 0) {
    $effectiveTests = $script:TotalTests - $script:SkippedTests
    if ($effectiveTests -gt 0) {
        $passRate = [math]::Round(($script:PassedTests * 100) / $effectiveTests, 2)
        Write-Host "Pass Rate: $passRate% (excluding skipped tests)"
    }
}

Write-Host ""
Write-Host "Regression test suite completed at $(Get-Date)"
Write-Host ""

# Exit with error if any tests failed
if ($script:FailedTests -gt 0) {
    Write-Host "REGRESSION TEST SUITE FAILED" -ForegroundColor Red
    exit 1
} else {
    Write-Host "REGRESSION TEST SUITE PASSED" -ForegroundColor Green
    exit 0
}
