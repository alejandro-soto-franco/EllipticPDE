#!/usr/bin/env python3
"""
Check this repository against Palomar's mechanical requirements before submitting.

Every check here comes from PalomarPolicy `CONTRIBUTING.md` sections 2 and 3, plus the
toolchain floor and taxonomy snapshots in PalomarSubmission. A submission that fails one
of them fails verification after intake has spent a proof, so it is worth a minute here.

Three things this cannot check, because they need Palomar's own verifier: the licence
detector's SPDX verdict, whether Mathlib's manifest URL with a `.git` suffix satisfies the
URL rule, and the editorial judgement. Those are reported as notes rather than results.

Run:  uv run --with pyyaml python verify/palomar_preflight.py
Exit code 0 iff every check passes.
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / "lean"
CONFIG = PROJECT / "comparator.json"
META = PROJECT / "formalization.yaml"

AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
LICENCE_NAMES = {"license", "licence", "copying", "unlicense", "ofl"}
LICENCE_SUFFIXES = {"", ".md", ".markdown", ".txt"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background", "other"}
ARTEFACTS = (".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so",
             ".trace")
TOOLCHAIN_MINIMUM = (4, 28, 0)

results: list[tuple[bool, str, str]] = []


def check(ok: bool, name: str, detail: str = "") -> None:
    results.append((ok, name, detail))


def git(*args: str) -> str:
    return subprocess.run(["/usr/bin/git", "-C", str(ROOT), *args],
                          capture_output=True, text=True).stdout.strip()


def parse_version(toolchain: str) -> tuple[int, int, int] | None:
    m = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(-rc\d+)?", toolchain.strip())
    return (int(m[1]), int(m[2]), int(m[3])) if m else None


def check_repository() -> None:
    check(git("status", "--porcelain") == "", "working tree is clean",
          "uncommitted work is excluded from a submission")
    head = git("rev-parse", "HEAD")
    check(bool(re.fullmatch(r"[0-9a-f]{40}", head)), "HEAD is a 40-character SHA", head)
    check(git("rev-parse", "HEAD") == git("rev-parse", "@{u}"),
          "HEAD is pushed to its upstream")

    tracked = git("ls-files").splitlines()
    compiled = [f for f in tracked if f.endswith(ARTEFACTS)]
    check(not compiled, "no compiled artefacts are tracked", ", ".join(compiled[:3]))
    links = [line.split("\t")[-1] for line in git("ls-files", "-s").splitlines()
             if line.startswith("120000")]
    check(not links, "no symbolic links are tracked", ", ".join(links[:3]))
    check(not (ROOT / ".gitmodules").exists(), "no Git submodules")
    lfs = [f for f in tracked if f.endswith(".gitattributes")]
    pointers = any("filter=lfs" in (ROOT / f).read_text(encoding="utf-8", errors="ignore")
                   for f in lfs)
    check(not pointers, "no Git LFS filters")

    size = sum(f.stat().st_size for f in ROOT.rglob("*")
               if f.is_file() and not f.is_symlink() and ".git/" not in str(f)
               and "/.lake/" not in str(f))
    check(size <= 500 * 1024 ** 2, "checkout is at most 500 MiB",
          f"{size / 1024 ** 2:.1f} MiB")


def check_licence() -> None:
    found = [p for p in ROOT.iterdir()
             if p.is_file() and p.stem.lower() in LICENCE_NAMES
             and p.suffix.lower() in LICENCE_SUFFIXES]
    check(len(found) == 1, "exactly one conventional licence file at the root",
          ", ".join(p.name for p in found) or "none")
    if len(found) != 1:
        return
    text = found[0].read_text(encoding="utf-8")
    check(0 < len(text.encode()) <= 1024 ** 2, "licence file is nonempty and under 1 MiB",
          f"{len(text.encode())} bytes")
    check("Apache License" in text and "Version 2.0" in text,
          "licence text is Apache 2.0")


def check_project_files() -> None:
    lakefiles = [n for n in ("lakefile.toml", "lakefile.lean")
                 if (PROJECT / n).exists()]
    check(len(lakefiles) == 1, "exactly one lakefile in the project directory",
          ", ".join(lakefiles))
    check((PROJECT / "lake-manifest.json").exists(), "lake-manifest.json is committed")
    for name in ("Challenge.lean", "Solution.lean", "comparator.json",
                 "formalization.yaml", "lean-toolchain"):
        check((PROJECT / name).exists(), f"{name} is present")

    version = parse_version((PROJECT / "lean-toolchain").read_text(encoding="utf-8"))
    check(version is not None, "lean-toolchain names a Lean release")
    if version:
        check(version >= TOOLCHAIN_MINIMUM,
              "toolchain is at or above Palomar's floor",
              f"{'.'.join(map(str, version))} against "
              f"{'.'.join(map(str, TOOLCHAIN_MINIMUM))}")

    manifest = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package.get("type") != "git":
            continue
        url, rev = package["url"], package["rev"]
        check(url.startswith("https://github.com/") and "?" not in url and "#" not in url,
              f"{package['name']} uses a credential-free GitHub URL", url)
        check(bool(re.fullmatch(r"[0-9a-f]{40}", rev)),
              f"{package['name']} is pinned to a full lowercase SHA", rev)


def check_challenge_size() -> None:
    source = (PROJECT / "Challenge.lean").read_text(encoding="utf-8")
    lines, size = len(source.splitlines()), len(source.encode())
    check(lines <= 1000 and size <= 100 * 1024, "challenge is inside the hard limit",
          f"{lines} lines, {size} bytes")
    check(lines <= 300 and size <= 32 * 1024,
          "challenge is inside the reviewed surface, so no size warning",
          f"{lines} lines against 300, {size} bytes against {32 * 1024}")


def check_config() -> dict:
    raw = CONFIG.read_text(encoding="utf-8")
    check(len(raw.encode()) <= 1024 ** 2, "comparator.json is under 1 MiB")
    config = json.loads(raw)
    check(isinstance(config, dict), "comparator.json holds one object")
    required = {"challenge_module", "solution_module", "theorem_names",
                "permitted_axioms"}
    optional = {"definition_names", "enable_nanoda"}
    check(required <= set(config), "comparator.json has the four required keys")
    extra = set(config) - required - optional
    check(not extra, "comparator.json carries no unaccepted key", ", ".join(sorted(extra)))
    names = config.get("theorem_names", [])
    check(bool(names) and all(isinstance(n, str) and n for n in names),
          "theorem_names is a nonempty list of nonempty strings", f"{len(names)} names")
    check(set(config.get("permitted_axioms", [])) <= AXIOMS,
          "permitted_axioms names only the three classical axioms")
    for module in ("challenge_module", "solution_module"):
        name = config[module]
        check(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part)
                  for part in name.split(".")), f"{module} is a valid dotted name", name)
    check(config["challenge_module"] != config["solution_module"],
          "the two modules are distinct")
    return config


def check_solution_pins(config: dict) -> None:
    solution = (PROJECT / "Solution.lean").read_text(encoding="utf-8")
    pinned = set(re.findall(r"^#print axioms (\S+)\s*$", solution, re.MULTILINE))
    missing = [n for n in config["theorem_names"] if n not in pinned]
    check(not missing, "every compared theorem pins its axiom set in Solution.lean",
          ", ".join(missing))
    check("sorry" not in re.sub(r"/-.*?-/", "", solution, flags=re.S),
          "Solution.lean carries no sorry outside its documentation")


def check_imports() -> None:
    """The Challenge's transitive import closure must avoid this project's own source."""
    probe = PROJECT / "PalomarPreflightImports.lean"
    probe.write_text(
        "import Challenge\n"
        "open Lean in\n"
        "run_cmd do\n"
        "  for m in (← Lean.getEnv).allImportedModuleNames do\n"
        "    Lean.logInfo m.toString\n", encoding="utf-8")
    try:
        out = subprocess.run(["lake", "env", "lean", probe.name], cwd=PROJECT,
                             capture_output=True, text=True).stdout
    finally:
        probe.unlink(missing_ok=True)
    modules = {line.strip() for line in out.splitlines() if line.strip()}
    project_modules = {m for m in modules
                       if m == "EllipticPdes" or m.startswith("EllipticPdes.")
                       or m in {"Solution", "AxiomAudit"}}
    check(bool(modules), "the challenge's import closure could be read",
          f"{len(modules)} modules")
    check(not project_modules,
          "the challenge imports no source of this project",
          ", ".join(sorted(project_modules)[:3]))


def check_metadata() -> None:
    import yaml

    raw = META.read_text(encoding="utf-8")
    check(len(raw.encode()) <= 256 * 1024, "formalization.yaml is under 256 KiB")
    check("<<:" not in raw, "formalization.yaml uses no YAML merge key")

    class Strict(yaml.SafeLoader):
        pass

    def no_duplicates(loader, node, deep=False):
        seen = set()
        for key_node, _ in node.value:
            key = loader.construct_object(key_node, deep=deep)
            if key in seen:
                raise ValueError(f"duplicate key {key!r}")
            seen.add(key)
        return yaml.SafeLoader.construct_mapping(loader, node, deep)

    Strict.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, no_duplicates)
    try:
        meta = yaml.load(raw, Strict)
        check(True, "formalization.yaml has no duplicate mapping key")
    except ValueError as e:
        check(False, "formalization.yaml has no duplicate mapping key", str(e))
        return

    check(isinstance(meta, dict), "formalization.yaml holds one top-level mapping")
    project = meta.get("project", {})
    check(bool(project.get("name")), "project.name is a nonempty string")
    description = project.get("description", "")
    check(bool(description) and len(description) <= 10_000,
          "project.description is nonempty and at most 10,000 characters",
          f"{len(description)} characters")
    authors = project.get("authors", [])
    check(bool(authors) and all(isinstance(a, str) and a for a in authors),
          "project.authors is a nonempty list of names", ", ".join(authors))
    maintainers = project.get("responsible_maintainers", [])
    check(bool(maintainers) and all(isinstance(m, str) and m for m in maintainers),
          "project.responsible_maintainers is a nonempty list", ", ".join(maintainers))
    check(project.get("license") == "Apache-2.0",
          "project.license is the SPDX identifier of the root licence file",
          str(project.get("license")))
    check("repository" not in meta,
          "repository is omitted, so the submission is the substantive development")

    classification = meta.get("classification", {})
    arxiv = classification.get("arxiv", [])
    msc = classification.get("msc2020", [])
    check(1 <= len(arxiv) <= 2 and len(set(arxiv)) == len(arxiv),
          "classification.arxiv holds one or two distinct codes", ", ".join(arxiv))
    check(1 <= len(msc) <= 8 and len(set(msc)) == len(msc),
          "classification.msc2020 holds one to eight distinct codes", ", ".join(msc))
    for field, codes in (("arxiv-categories", arxiv), ("msc2020-codes", msc)):
        snapshot = taxonomy(field)
        if snapshot is None:
            print(f"  note  {field} snapshot unavailable, codes unchecked")
            continue
        check(set(codes) <= snapshot, f"every code is in Palomar's {field} snapshot",
              ", ".join(sorted(set(codes) - snapshot)))

    methods = meta.get("automation", {}).get("methods", [])
    check(bool(methods) and all(m.get("method") for m in methods),
          "automation.methods is nonempty and every entry names a method",
          ", ".join(m.get("method", "") for m in methods))
    check(bool(meta.get("review", {}).get("status")), "review.status is nonempty",
          str(meta.get("review", {}).get("status")))

    sources = meta.get("sources", [])
    check(bool(sources), "sources is nonempty")
    check(all(s.get("title") for s in sources), "every source has a nonempty title")
    check(all(s.get("relationship") in RELATIONSHIPS for s in sources),
          "every source relationship is one of the five accepted values")
    check(all(s.get("type") in SOURCE_TYPES for s in sources if "type" in s),
          "every declared source type is accepted")
    original = [s for s in sources if s.get("type") == "original-proof"]
    substantive = [s for s in sources
                   if s.get("relationship") in {"formalizes", "adapts",
                                                "independently-proves"}]
    check(not original and bool(substantive),
          "the source list is consistently source-based",
          f"{len(substantive)} substantive relationships")

    declared = {r.get("declaration") for r in meta.get("status", {})
                .get("main_results", [])}
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    check(set(config["theorem_names"]) <= declared,
          "every compared theorem appears in status.main_results")


def taxonomy(name: str) -> set[str] | None:
    """Palomar's checked-in taxonomy snapshot, fetched once and cached outside the repo.

    The snapshots belong to PalomarSubmission, so they are read rather than vendored.
    """
    cache = Path.home() / ".cache" / "palomar-taxonomies"
    path = cache / f"{name}.json"
    if not path.exists():
        cache.mkdir(parents=True, exist_ok=True)
        fetched = subprocess.run(
            ["gh", "api", f"repos/PalomarRegistry/PalomarSubmission/contents/"
             f"taxonomies/{name}.json", "--jq", ".content"],
            capture_output=True, text=True)
        if fetched.returncode != 0:
            return None
        import base64
        path.write_bytes(base64.b64decode(fetched.stdout))
    return set(_flatten(json.loads(path.read_text(encoding="utf-8"))))


def _flatten(node):
    if isinstance(node, dict):
        for key, value in node.items():
            yield key
            yield from _flatten(value)
    elif isinstance(node, list):
        for value in node:
            yield from _flatten(value)
    elif isinstance(node, str):
        yield node


def check_github() -> None:
    status = subprocess.run(["gh", "auth", "status"], capture_output=True, text=True)
    text = status.stdout + status.stderr
    check(status.returncode == 0, "gh is authenticated")
    check("gist" in text, "the gh token carries the gist scope",
          "step 3 of the submission proof creates a secret gist")


def main() -> int:
    check_repository()
    check_licence()
    check_project_files()
    check_challenge_size()
    config = check_config()
    check_solution_pins(config)
    check_imports()
    check_metadata()
    check_github()

    width = max(len(name) for _, name, _ in results)
    for ok, name, detail in results:
        mark = "pass" if ok else "FAIL"
        print(f"  {mark}  {name:<{width}}  {detail}")
    failed = [name for ok, name, _ in results if not ok]
    print(f"\n{len(results) - len(failed)}/{len(results)} checks pass")
    if failed:
        print("failing: " + ", ".join(failed))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
