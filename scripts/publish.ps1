param(
    [string]$Notes = "업데이트"
)

$ErrorActionPreference = "Stop"
Set-Location (Split-Path $PSScriptRoot -Parent)

$versionFile = Join-Path (Get-Location) "version.py"
$text = Get-Content $versionFile -Raw -Encoding UTF8
if ($text -notmatch 'APP_VERSION = "(\d+)\.(\d+)\.(\d+)"') {
    throw "version.py 의 APP_VERSION 을 찾지 못했습니다."
}
$next = "{0}.{1}.{2}" -f $Matches[1], $Matches[2], ([int]$Matches[3] + 1)
$text = $text -replace 'APP_VERSION = "\d+\.\d+\.\d+"', "APP_VERSION = `"$next`""
Set-Content $versionFile $text -Encoding UTF8 -NoNewline

git add version.py phone_messenger.py updater.py README.md UsbSmsBridge.apk scripts .github UsbSms.spec requirements.txt requirements-build.txt
git commit -m "Release v$next`n`n$Notes"
git tag "v$next"
git push origin HEAD
git push origin "v$next"
Write-Host "v$next 태그를 푸시했습니다. GitHub Actions가 릴리스를 만들면 다른 컴퓨터에서 자동 업데이트됩니다."
