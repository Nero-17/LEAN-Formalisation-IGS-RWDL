param([int]$StartIndex = 0)
$ErrorActionPreference = 'Stop'
Set-Location (Split-Path -Parent $PSScriptRoot)
$env:LEAN_PATH = '.lake\build\lib\lean;.lake\packages\mathlib\.lake\build\lib\lean;.lake\packages\batteries\.lake\build\lib\lean;.lake\packages\aesop\.lake\build\lib\lean;.lake\packages\Qq\.lake\build\lib\lean;.lake\packages\proofwidgets\.lake\build\lib\lean;.lake\packages\plausible\.lake\build\lib\lean;.lake\packages\LeanSearchClient\.lake\build\lib\lean;.lake\packages\importGraph\.lake\build\lib\lean'
$section4Compiler = 'C:\Users\lzysh\Documents\Codex\2026-09-21\new-chat\work\elan\toolchains\leanprover--lean4---v4.28.0\bin\lean.exe'
$section4Modules = @(
  'RequestProject/Cluster/InverseLimit',
  'RequestProject/Reduced/AllParameters',
  'RequestProject/Cluster/TreeNetwork',
  'RequestProject/Cluster/InfiniteTree',
  'RequestProject/Cluster/InfiniteProcess',
  'RequestProject/Cluster/NestedReduction',
  'RequestProject/Reduced/NoLimit',
  'RequestProject/Cluster/TreeBounds',
  'RequestProject/Reduced/OriginalParameters',
  'RequestProject/Cluster/InfiniteConsequences',
  'RequestProject/Cluster/FullProcessLaw',
  'RequestProject/Outlook/RuleCompatibility',
  'RequestProject/Cluster',
  'Section4Axioms'
)
$section4Records = @()
if ($StartIndex -gt 0) {
  $section4Records = @(Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot 'verification.json') |
    ConvertFrom-Json | Select-Object -First $StartIndex)
}
foreach ($section4Module in ($section4Modules | Select-Object -Skip $StartIndex)) {
  $section4Source = "$section4Module.lean"
  $section4Log = Join-Path $PSScriptRoot ((Split-Path -Leaf $section4Module) + '.log')
  $section4Start = [DateTime]::UtcNow.ToString('o')
  "source=$section4Source`nstarted=$section4Start" | Set-Content -LiteralPath $section4Log
  if ($section4Module -eq 'Section4Axioms') {
    & $section4Compiler $section4Source 2>&1 | Tee-Object -FilePath $section4Log -Append
  } else {
    $section4Output = ".lake/build/lib/lean/$section4Module.olean"
    New-Item -ItemType Directory -Force (Split-Path -Parent $section4Output) | Out-Null
    & $section4Compiler -o $section4Output $section4Source 2>&1 |
      Tee-Object -FilePath $section4Log -Append
  }
  $section4Exit = $LASTEXITCODE
  $section4End = [DateTime]::UtcNow.ToString('o')
  "exit=$section4Exit`nfinished=$section4End" | Add-Content -LiteralPath $section4Log
  $section4Records += [pscustomobject]@{
    source = $section4Source
    sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $section4Source).Hash
    started_utc = $section4Start
    finished_utc = $section4End
    exit_code = $section4Exit
    compiler = $section4Compiler
    log = $section4Log
  }
  $section4Records | ConvertTo-Json -Depth 4 |
    Set-Content -LiteralPath (Join-Path $PSScriptRoot 'verification.json')
  Write-Output "$section4Module : exit $section4Exit"
  if ($section4Exit -ne 0) { exit $section4Exit }
}
exit 0
