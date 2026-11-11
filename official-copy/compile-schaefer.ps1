$out = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\.lake\build\lib\lean'
$env:LEAN_PATH = "$out;" + $env:LEAN_PATH
$dbg = 'C:\Users\tacti.TACTICALTIM\p-vs-np\.cursor\debug-720129.log'
$src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\Schaefer.lean'
$olean = Join-Path $out 'Schaefer.olean'
Write-Host '===== Schaefer ====='
& lean $src -o $olean
$code = $LASTEXITCODE
Write-Host "EXIT $code"
if ($code -ne 0) { exit $code }
Write-Host '===== SchaeferAx ====='
& lean 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\SchaeferAx.lean'
$code = $LASTEXITCODE
Write-Host "EXIT $code"
$o = @{sessionId='720129'; hypothesisId='H1'; location='Schaefer.lean'; message='schaefer compile'; data=@{exit=$code; olean=(Test-Path -LiteralPath $olean)}; timestamp=[DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds(); runId='schaefer-ax'}
Add-Content -LiteralPath $dbg -Value ($o | ConvertTo-Json -Compress)
exit $code
