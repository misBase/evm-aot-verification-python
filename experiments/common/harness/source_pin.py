"""Expected source pin of the validator under test (../../../ch4-5-validator).

Every job checks that the validator's model packages (verification, state, x86_64, evm_ir, common, tools) hash to
this pin before and after it runs, so a result is always tied to one exact source tree. `make pin` (re)computes
SOURCE_PIN.json from the packaged validator. The paper's runs used the unpacked development tree of the same
revision; its pin is recorded in SOURCE_PIN.json as "paper_run_pin" for reference.
"""
import json
from pathlib import Path

_PIN = json.loads(Path(__file__).with_name("SOURCE_PIN.json").read_text())
SHA256, FILES = _PIN["sha256"], _PIN["files"]


def compute(root):
    """The pin of a validator tree: sha256 over (relative path, bytes) of its model packages' .py files."""
    from hashlib import sha256
    root, digest, count = Path(root), sha256(), 0
    for package in ("verification", "state", "x86_64", "evm_ir", "common", "tools"):
        for path in sorted((root / package).rglob("*.py")):
            digest.update(path.relative_to(root).as_posix().encode())
            digest.update(path.read_bytes())
            count += 1
    return dict(sha256=digest.hexdigest(), files=count)


if __name__ == "__main__":  # python source_pin.py VALIDATOR_DIR: write SOURCE_PIN.json for that tree
    import sys
    pin = compute(sys.argv[1])
    out = Path(__file__).with_name("SOURCE_PIN.json")
    previous = json.loads(out.read_text()) if out.exists() else {}
    pin["paper_run_pin"] = previous.get("paper_run_pin")
    out.write_text(json.dumps(pin, indent=1) + "\n")
    print(json.dumps(pin))
