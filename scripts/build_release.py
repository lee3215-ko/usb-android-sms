"""Build the public Windows zip from an explicit file list."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from version import APP_VERSION, ASSET_NAME, EXE_NAME, PACKAGE_NAME

PLATFORM_TOOLS = "https://dl.google.com/android/repository/platform-tools-latest-windows.zip"
ADB_FILES = ("adb.exe", "AdbWinApi.dll", "AdbWinUsbApi.dll")


def adb_binaries(cache: Path) -> Path:
    folder = cache / "platform-tools"
    if all((folder / name).is_file() for name in ADB_FILES):
        return folder
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / "platform-tools-windows.zip"
    if not archive.is_file():
        urllib.request.urlretrieve(PLATFORM_TOOLS, archive)
    with zipfile.ZipFile(archive) as bundle:
        for name in ADB_FILES:
            target = folder / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(bundle.read(f"platform-tools/{name}"))
    return folder


def main():
    tag = os.environ.get("GITHUB_REF_NAME", "")
    if tag.startswith("v") and tag != f"v{APP_VERSION}":
        raise RuntimeError("Git tag and version.py must match")
    subprocess.run([sys.executable, "-m", "PyInstaller", "--noconfirm", "UsbSms.spec"], cwd=ROOT, check=True)
    output = ROOT / "release" / f"v{APP_VERSION}"
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="usbsms-package-") as temporary:
        package = Path(temporary) / PACKAGE_NAME
        package.mkdir()
        shutil.copy2(ROOT / "dist" / EXE_NAME, package / EXE_NAME)
        shutil.copy2(ROOT / "UsbSmsBridge.apk", package / "UsbSmsBridge.apk")
        shutil.copy2(ROOT / "README.md", package / "README.md")
        adb = package / "adb"
        adb.mkdir()
        for name in ADB_FILES:
            shutil.copy2(adb_binaries(ROOT / "build" / "platform-tools-cache") / name, adb / name)
        (package / "version.json").write_text(json.dumps({"version": APP_VERSION}), encoding="utf-8")
        archive = output / ASSET_NAME
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as bundle:
            for source in sorted(package.rglob("*")):
                if source.is_file():
                    bundle.write(source, source.relative_to(package.parent).as_posix())
        with archive.open("rb") as source:
            digest = hashlib.file_digest(source, "sha256").hexdigest()
        (output / "SHA256SUMS.txt").write_text(f"{digest}  {ASSET_NAME}\n", encoding="ascii")
        print(archive)


if __name__ == "__main__":
    main()
