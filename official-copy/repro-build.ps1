$ErrorActionPreference = 'Continue'
$out = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\.lake\build\lib\lean'
$pv = Join-Path $out 'PvnpReal'
New-Item -ItemType Directory -Force -Path $pv | Out-Null
$srcOle = 'C:\Users\tacti.TACTICALTIM\OneDrive\Desktop\Alice Project Files\TH\ABT\pvnp\.lake\build\lib\lean\PvnpReal'
robocopy $srcOle $pv *.olean *.ilean /NFL /NDL /NJH /NJS /NP | Out-Null
$env:LEAN_PATH = "$out;" + $env:LEAN_PATH
$base = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\PvnpReal'
$log = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\repro.log'
$dbg = 'C:\Users\tacti.TACTICALTIM\p-vs-np\.cursor\debug-720129.log'
Set-Content -LiteralPath $log -Value "LEAN_PATH_HEAD=$($env:LEAN_PATH.Split(';')[0])"
function Write-Dbg($hyp, $msg, $data) {
  $o = @{sessionId='720129'; hypothesisId=$hyp; location='repro-build.ps1'; message=$msg; data=$data; timestamp=[DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds(); runId='repro1'}
  Add-Content -LiteralPath $dbg -Value ($o | ConvertTo-Json -Compress)
}
$odLean = 'C:\Users\tacti.TACTICALTIM\OneDrive\Desktop\Alice Project Files\TH\ABT\pvnp\.lake\build\lib\lean'
Copy-Item -LiteralPath (Join-Path $odLean 'Benchmarks.olean') -Destination (Join-Path $out 'Benchmarks.olean') -Force
$targets = @(
  @{ name = 'PvnpReal'; hyp = 'H5'; src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\PvnpReal.lean'; olean = (Join-Path $out 'PvnpReal.olean') },
  @{ name = 'UnifiedPvnp'; hyp = 'H6'; src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\UnifiedPvnp.lean'; olean = (Join-Path $out 'UnifiedPvnp.olean') },
  @{ name = 'Axioms'; hyp = 'H7'; src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\Axioms.lean'; olean = (Join-Path $out 'Axioms.olean') }
)
Write-Dbg 'H5' 'start umbrella' @{ targets = @('PvnpReal','UnifiedPvnp','Axioms') }
foreach ($t in $targets) {
  "===== $($t.name) =====" | Tee-Object -FilePath $log -Append | Write-Host
  & lean $t.src -o $t.olean 2>&1 | Tee-Object -FilePath $log -Append | Write-Host
  $code = $LASTEXITCODE
  "EXIT $code" | Tee-Object -FilePath $log -Append | Write-Host
  $err = @(Select-String -LiteralPath $log -Pattern 'error:' | Select-Object -Last 8 | ForEach-Object { $_.Line })
  Write-Dbg $t.hyp "$($t.name) exit" @{ exit = $code; olean = (Test-Path -LiteralPath $t.olean); errors = $err }
  if ($code -ne 0) { exit $code }
}
Write-Dbg 'H7' 'umbrella built' @{ ok = $true }
exit 0
