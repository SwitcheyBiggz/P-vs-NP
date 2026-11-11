$out = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\.lake\build\lib\lean'
$env:LEAN_PATH = "$out;" + $env:LEAN_PATH
$src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\WitnessCert.lean'
$olean = Join-Path $out 'WitnessCert.olean'
Write-Host '===== WitnessCert ====='
& lean $src -o $olean
$code = $LASTEXITCODE
Write-Host "EXIT $code"
exit $code
