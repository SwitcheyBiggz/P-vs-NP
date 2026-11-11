$out = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\.lake\build\lib\lean'
$env:LEAN_PATH = "$out;" + $env:LEAN_PATH
$src = 'C:\Users\tacti.TACTICALTIM\p-vs-np\official-copy\CrossReduce.lean'
$olean = Join-Path $out 'CrossReduce.olean'
Write-Host '===== CrossReduce ====='
& lean $src -o $olean
$code = $LASTEXITCODE
Write-Host "EXIT $code"
exit $code
