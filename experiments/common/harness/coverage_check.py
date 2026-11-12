"""Audit planned jobs and selector admission without turning diagnostics into proofs.

  python coverage_check.py RESULTS_DIR FIXTURES_DIR [--only PREFIX] [--json OUT]
"""
import argparse
from collections import Counter
import json
from pathlib import Path


def _read(path):
    try:
        value = json.loads(path.read_text())
        if not isinstance(value, dict):
            raise ValueError("result JSON must be an object")
        return value
    except (OSError, ValueError) as error:
        return {"result": "ERR", "receipt_error": str(error)}


def _slice_error(job, record):
    from slices import receipt_failure
    try:
        args = job.argv
        if args[0] == "reach":
            stem, selector, size = args[1:4]
        else:
            stem = args[1]
            selector = args[args.index("--selector") + 1]
            size = args[args.index("--calldata-size") + 1]
        return receipt_failure(record, stem, int(selector, 16), None if size == "None" else int(size))
    except (ValueError, IndexError, TypeError, KeyError) as error:
        return f"slice arguments unavailable: {error}"


def audit_jobs(planned, out):
    planned = list(planned)
    out = Path(out)
    path = lambda name: out / (name.replace("/", "__") + ".json")
    counts = Counter(job.name for job in planned)
    done, skipped, missing, invalid, unvalidated = [], [], [], [], []
    for job in planned:
        dependency = None
        if job.requires:
            name, accepted = job.requires
            if not path(name).exists() and path(job.name).exists():
                invalid.append(dict(name=job.name, reason=f"required receipt missing: {name}"))
                continue
            if path(name).exists():
                dependency = _read(path(name))
                reason = None
                if dependency.get("result") not in accepted:
                    reason = f"dependency {name}: {dependency.get('result')}"
                elif job.name.startswith("fn/"):
                    reason = _slice_error(job, dependency)
                if reason:
                    item = dict(name=job.name, reason=reason)
                    (invalid if path(job.name).exists() else skipped).append(item)
                    continue
        if not path(job.name).exists():
            missing.append(job.name)
            continue
        record = _read(path(job.name))
        if record.get("receipt_error"):
            invalid.append(dict(name=job.name, reason=record["receipt_error"]))
            continue
        if job.name.startswith("fn/") and job.argv and job.argv[0] == "reach":
            reason = _slice_error(job, record)
            if reason:
                unvalidated.append(dict(name=job.name, reason=reason))
        done.append(dict(name=job.name, result=record.get("result"), host=record.get("host")))
    return dict(planned=len(planned), done=done, skipped=skipped, missing=missing,
                invalid_results=invalid, unvalidated_function_receipts=unvalidated,
                duplicate_names=sorted(name for name, count in counts.items() if count > 1),
                scope="job accounting and sample admission; no equivalence proof")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    parser.add_argument("fixtures")
    parser.add_argument("--only", default="")
    parser.add_argument("--json", type=Path)
    args = parser.parse_args(argv)
    import matrix
    planned = [job for job in matrix.jobs(args.fixtures, args.results) + matrix.load_extra(args.fixtures, args.results)
               if job.name.startswith(args.only)]
    report = audit_jobs(planned, args.results)
    print(f"planned {report['planned']} with result {len(report['done'])} skipped {len(report['skipped'])} missing {len(report['missing'])}")
    for name in report["missing"]:
        print("MISSING", name)
    for item in report["unvalidated_function_receipts"]:
        print("UNVALIDATED", item["name"], item["reason"])
    for item in report["invalid_results"]:
        print("INVALID", item["name"], item["reason"])
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return int(bool(report["missing"] or report["invalid_results"] or report["duplicate_names"]
                    or report["unvalidated_function_receipts"]))


if __name__ == "__main__":
    raise SystemExit(main())
