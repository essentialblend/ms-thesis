# Input root dir
param([string]$mainRoot)

# Validate root file
if(-not (Test-Path $mainRoot))
{
  Write-Host "`nError: Agda root file '$mainRoot' not found." -ForegroundColor Red
  exit 1
}

Write-Host "`n========================================"
Write-Host "--------- Verifying Ring Axioms --------"
Write-Host "========================================`n"

# Validate agda exec in PATH
if(-not(Get-Command agda -ErrorAction SilentlyContinue))
{
  Write-Host "`nError: 'agda' not found. Please install Agda or add it to PATH...`n" -ForegroundColor Red
  exit 1
}

# Run agda command to type-check proofs
& agda --ignore-interfaces -i . $mainRoot
$exitCode = $LASTEXITCODE

# Print success/failure 
if($exitCode -eq 0)
{
  Write-Host "`nAll proofs type-checked!`n" -ForegroundColor Green
  exit $exitCode
}
else
{
  Write-Host "`nType-check failed!`n" -ForegroundColor Red
  exit $exitCode
}