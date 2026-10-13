param([Parameter(Mandatory=$true)][string]$Module, [int]$Attempt = 1)
$ErrorActionPreference = 'Continue'
Set-Location (Split-Path -Parent $PSScriptRoot)
$env:LEAN_PATH = '.lake\corrected-spectrum\lib\lean;.lake\build\lib\lean;.lake\packages\mathlib\.lake\build\lib\lean;.lake\packages\batteries\.lake\build\lib\lean;.lake\packages\aesop\.lake\build\lib\lean;.lake\packages\Qq\.lake\build\lib\lean;.lake\packages\proofwidgets\.lake\build\lib\lean;.lake\packages\plausible\.lake\build\lib\lean;.lake\packages\LeanSearchClient\.lake\build\lib\lean;.lake\packages\importGraph\.lake\build\lib\lean'
$percolationCompiler = 'C:\Users\lzysh\Documents\Codex\2026-09-21\new-chat\work\elan\toolchains\leanprover--lean4---v4.28.0\bin\lean.exe'
$percolationSource = "RequestProject/Outlook/$Module.lean"
$percolationOutput = ".lake/build/lib/lean/RequestProject/Outlook/$Module.olean"
$percolationLog = Join-Path $PSScriptRoot "$Module.sol-attempt-$Attempt.log"
$percolationStart = [DateTime]::UtcNow.ToString('o')
$percolationHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $percolationSource).Hash
"source=$percolationSource`nstarted=$percolationStart`nsource_sha256=$percolationHash" | Set-Content -LiteralPath $percolationLog
& $percolationCompiler -o $percolationOutput (Resolve-Path $percolationSource).Path 2>&1 | Tee-Object -FilePath $percolationLog -Append
$percolationExit = $LASTEXITCODE
$percolationEnd = [DateTime]::UtcNow.ToString('o')
"exit=$percolationExit`nfinished=$percolationEnd" | Add-Content -LiteralPath $percolationLog
$percolationRecord = [pscustomobject]@{
 source = (Resolve-Path $percolationSource).Path
 source_sha256 = $percolationHash
 current_source_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $percolationSource).Hash
 logged_start_utc = $percolationStart
 end_utc = $percolationEnd
 exit_code = $percolationExit
 compiler = $percolationCompiler
 log = $percolationLog
}
$percolationRecord | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath "$percolationLog.receipt.json"
$percolationRecordsPath = Join-Path $PSScriptRoot 'sol-percolation-verification.json'
$percolationRecords = @()
if (Test-Path -LiteralPath $percolationRecordsPath) {
 $percolationRecords = @(Get-Content -Raw -LiteralPath $percolationRecordsPath | ConvertFrom-Json)
}
$percolationRecords += $percolationRecord
ConvertTo-Json -InputObject $percolationRecords -Depth 6 | Set-Content -LiteralPath $percolationRecordsPath
Write-Output "module=$Module attempt=$Attempt exit=$percolationExit source_sha256=$percolationHash"
exit $percolationExit


