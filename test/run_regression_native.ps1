# Comprehensive Regression Test Suite for coh_noc Architecture
# Task 14.1: 运行完整的回归测试套件
# Native PowerShell version - runs tests directly with iverilog

# Test results tracking
$script:TotalTests = 0
$script:PassedTests = 0
$script:FailedTests = 0
$script:SkippedTests = 0
$script:PassedTestNames = @()
$script:FailedTestNames = @()
$script:SkippedTestNames = @()

# Source files
$SRC_DIR = "../src"
$SOURCES = @(
    "$SRC_DIR/coh_noc_pkg.sv",
    "$SRC_DIR/coh_noc_types.sv"
)

# Function to print section header
function Print-Header {
    param([string]$Message)
    Write-Host ""
    Write-Host "==================================================================" -ForegroundColor Blue
    Write-Host $Message -ForegroundColor Blue
    Write-Host "==================================================================" -ForegroundColor Blue
}

# Function to run iverilog test
function Run-IverilogTest {
    param(
        [string]$TestName,
        [string]$TestBench,
        [string[]]$AdditionalSources = @(),
        [string]$OutputVVP = "test_temp.vvp"
    )
    
    $script:TotalTests++
    
    Write-Host ""
    Write-Host "Running: $TestName" -ForegroundColor Yellow
    
    # Combine all source files
    $allSources = $SOURCES + $AdditionalSources + @($TestBench)
    
    try {
        # Compile with iverilog
        Write-Host "  Compiling..." -ForegroundColor Cyan
        $compileArgs = @("-g2012", "-o", $OutputVVP) + $allSources
        $compileOutput = & iverilog $compileArgs 2>&1
        
        if ($LASTEXITCODE -ne 0) {
            Write-Host "✗ FAILED: $TestName (Compilation Error)" -ForegroundColor Red
            $script:FailedTests++
            $script:FailedTestNames += "$TestName (Compilation)"
            Write-Host $compileOutput -ForegroundColor Red
            return
        }
        
        # Run simulation with vvp
        Write-Host "  Simulating..." -ForegroundColor Cyan
        $simOutput = & vvp $OutputVVP 2>&1
        
        if ($LASTEXITCODE -ne 0) {
            Write-Host "✗ FAILED: $TestName (Simulation Error)" -ForegroundColor Red
            $script:FailedTests++
            $script:FailedTestNames += "$TestName (Simulation)"
            Write-Host $simOutput -ForegroundColor Red
            return
        }
        
        # Check for test failures in output
        $outputStr = $simOutput | Out-String
        if ($outputStr -match "FAIL|ERROR|ASSERTION FAILED") {
            Write-Host "✗ FAILED: $TestName (Test Assertion Failed)" -ForegroundColor Red
            $script:FailedTests++
            $script:FailedTestNames += "$TestName (Assertion)"
            Write-Host $simOutput
        } else {
            Write-Host "✓ PASSED: $TestName" -ForegroundColor Green
            $script:PassedTests++
            $script:PassedTestNames += $TestName
            Write-Host $simOutput
        }
        
        # Clean up
        if (Test-Path $OutputVVP) {
            Remove-Item $OutputVVP -Force
        }
        
    } catch {
        Write-Host "✗ FAILED: $TestName (Exception)" -ForegroundColor Red
        $script:FailedTests++
        $script:FailedTestNames += "$TestName (Exception)"
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
Write-Host "Simulator: Icarus Verilog"
Write-Host ""

# Change to test directory
Set-Location $PSScriptRoot

# Clean previous build artifacts
Print-Header "Cleaning Previous Build Artifacts"
Get-ChildItem -Filter "*.vvp" | Remove-Item -Force -ErrorAction SilentlyContinue
Get-ChildItem -Filter "*.vcd" | Remove-Item -Force -ErrorAction SilentlyContinue
Write-Host "Cleaned build artifacts"

# ============================================================================
# PHASE 1: Basic Data Structure Tests
# ============================================================================
Print-Header "PHASE 1: Basic Data Structure Tests"

Run-IverilogTest `
    -TestName "Property 4: Flit Virtual Channel Integrity" `
    -TestBench "tb_flit_properties.sv" `
    -OutputVVP "test_flit.vvp"

Run-IverilogTest `
    -TestName "Property 10: Directory State Consistency" `
    -TestBench "tb_directory_properties.sv" `
    -OutputVVP "test_dir.vvp"

# ============================================================================
# PHASE 2: Network Topology Tests
# ============================================================================
Print-Header "PHASE 2: Network Topology Tests"

Run-IverilogTest `
    -TestName "Property 1: 2D Mesh Topology Connectivity" `
    -TestBench "tb_mesh_topology_properties.sv" `
    -OutputVVP "test_mesh.vvp"

Run-IverilogTest `
    -TestName "Property 3: Routing Deadlock Freedom" `
    -TestBench "tb_deadlock_properties.sv" `
    -OutputVVP "test_deadlock.vvp"

# ============================================================================
# PHASE 3: XP Router Tests
# ============================================================================
Print-Header "PHASE 3: XP Router Component Tests"

$XP_ROUTER_SOURCES = @(
    "$SRC_DIR/xp_router_compute.sv",
    "$SRC_DIR/vc_buffer.sv",
    "$SRC_DIR/vc_buffer_manager.sv",
    "$SRC_DIR/credit_flow_control.sv",
    "$SRC_DIR/xp_router.sv"
)

Run-IverilogTest `
    -TestName "Property 2: X-Y Dimension-Order Routing Correctness" `
    -TestBench "tb_routing_properties.sv" `
    -AdditionalSources @("$SRC_DIR/xp_router_compute.sv") `
    -OutputVVP "test_routing.vvp"

Run-IverilogTest `
    -TestName "Property 7: Virtual Channel Isolation" `
    -TestBench "tb_vc_buffer_properties.sv" `
    -AdditionalSources @("$SRC_DIR/vc_buffer.sv", "$SRC_DIR/vc_buffer_manager.sv") `
    -OutputVVP "test_vc_buffer.vvp"

Run-IverilogTest `
    -TestName "Property 6 & 8: Credit Flow Control & Buffer Backpressure" `
    -TestBench "tb_flow_control_properties.sv" `
    -AdditionalSources @("$SRC_DIR/credit_flow_control.sv") `
    -OutputVVP "test_flow_control.vvp"

Run-IverilogTest `
    -TestName "Property 5: Flit Forwarding Correctness" `
    -TestBench "tb_xp_router_properties.sv" `
    -AdditionalSources $XP_ROUTER_SOURCES `
    -OutputVVP "test_xp_router.vvp"

Run-IverilogTest `
    -TestName "XP Router Unit Tests (Edge Cases)" `
    -TestBench "tb_xp_router_unit.sv" `
    -AdditionalSources $XP_ROUTER_SOURCES `
    -OutputVVP "test_xp_unit.vvp"

# ============================================================================
# PHASE 4: HN-F Coherency Node Tests
# ============================================================================
Print-Header "PHASE 4: HN-F Coherency Node Tests"

Run-IverilogTest `
    -TestName "Property 9: System Level Cache Functionality" `
    -TestBench "tb_slc_properties.sv" `
    -AdditionalSources @("$SRC_DIR/slc_cache.sv") `
    -OutputVVP "test_slc.vvp"

Run-IverilogTest `
    -TestName "Property 12: MESI State Machine Correctness" `
    -TestBench "tb_mesi_properties.sv" `
    -AdditionalSources @("$SRC_DIR/mesi_state_machine.sv") `
    -OutputVVP "test_mesi.vvp"

Run-IverilogTest `
    -TestName "Property 11: Snoop Filter Optimization" `
    -TestBench "tb_snoop_filter_properties.sv" `
    -AdditionalSources @("$SRC_DIR/snoop_filter.sv") `
    -OutputVVP "test_snoop_filter.vvp"

$HN_F_SOURCES = @(
    "$SRC_DIR/interfaces/xp_port_if.sv",
    "$SRC_DIR/interfaces/axi_if.sv",
    "$SRC_DIR/slc_cache.sv",
    "$SRC_DIR/directory_manager.sv",
    "$SRC_DIR/mesi_state_machine.sv",
    "$SRC_DIR/snoop_filter.sv",
    "$SRC_DIR/hn_f.sv"
)

Run-IverilogTest `
    -TestName "HN-F Integration Tests" `
    -TestBench "tb_hn_f_integration.sv" `
    -AdditionalSources $HN_F_SOURCES `
    -OutputVVP "test_hn_f.vvp"

# ============================================================================
# PHASE 5: RN-F Request Node Tests
# ============================================================================
Print-Header "PHASE 5: RN-F Request Node Tests"

if (Test-Path "tb_rn_f_properties.sv") {
    $RN_F_SOURCES = @(
        "$SRC_DIR/interfaces/xp_port_if.sv",
        "$SRC_DIR/interfaces/cpu_if.sv",
        "$SRC_DIR/l1_cache.sv",
        "$SRC_DIR/rn_f.sv"
    )
    
    Run-IverilogTest `
        -TestName "Property 13 & 14: RN-F Proxy & Snoop Response" `
        -TestBench "tb_rn_f_properties.sv" `
        -AdditionalSources $RN_F_SOURCES `
        -OutputVVP "test_rn_f.vvp"
} else {
    Skip-Test "RN-F Property Tests" "Test file not found"
}

# ============================================================================
# PHASE 6: SN-F Memory Interface Tests
# ============================================================================
Print-Header "PHASE 6: SN-F Memory Interface Tests"

if (Test-Path "tb_sn_f_properties.sv") {
    $SN_F_SOURCES = @(
        "$SRC_DIR/interfaces/xp_port_if.sv",
        "$SRC_DIR/interfaces/ddr_if.sv",
        "$SRC_DIR/sn_f.sv"
    )
    
    Run-IverilogTest `
        -TestName "Property 15: Memory Interface Protocol Conversion" `
        -TestBench "tb_sn_f_properties.sv" `
        -AdditionalSources $SN_F_SOURCES `
        -OutputVVP "test_sn_f.vvp"
} else {
    Skip-Test "SN-F Property Tests" "Test file not found"
}

Skip-Test "Property 16: Multi-Channel Parallel Access" "Requires VCS/Xcelium/Questa (not available with Iverilog)"

# ============================================================================
# PHASE 7: Error Handling Tests
# ============================================================================
Print-Header "PHASE 7: Error Handling and Fault Tolerance Tests"

Run-IverilogTest `
    -TestName "Error Detection and Recovery Mechanisms" `
    -TestBench "tb_error_handling_simple.sv" `
    -OutputVVP "test_error.vvp"

# ============================================================================
# PHASE 8: System Integration Tests
# ============================================================================
Print-Header "PHASE 8: System Integration Tests"

if (Test-Path "tb_system_integration.sv") {
    $SYSTEM_SOURCES = @(
        "$SRC_DIR/interfaces/xp_port_if.sv",
        "$SRC_DIR/interfaces/cpu_if.sv",
        "$SRC_DIR/interfaces/axi_if.sv",
        "$SRC_DIR/interfaces/ddr_if.sv",
        "$SRC_DIR/mesh_2d_network.sv",
        "$SRC_DIR/coh_noc_system.sv"
    )
    
    Run-IverilogTest `
        -TestName "System Integration End-to-End Test" `
        -TestBench "tb_system_integration.sv" `
        -AdditionalSources $SYSTEM_SOURCES `
        -OutputVVP "test_system.vvp"
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
