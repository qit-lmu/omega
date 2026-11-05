#!/usr/bin/env python3
"""Check manuscript coverage, dependencies, completion metadata, and root imports.

The parser deliberately handles this manuscript's comments and disabled
``iffalse`` blocks rather than interpreting arbitrary TeX. Labels are the stable
identities; source line numbers are navigation hints. Lean declaration existence
and axiom dependencies are checked separately by checkdecls and Audit.lean.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

from render_blueprint import render

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENTS = {"definition", "lemma", "corollary", "theorem", "proposition", "remark"}


def active_tex(source: str) -> str:
    """Remove comments and iffalsed text, preserving line numbers."""
    lines = []
    for line in source.splitlines(keepends=True):
        for i, char in enumerate(line):
            if char != "%":
                continue
            backslashes = len(line[:i]) - len(line[:i].rstrip("\\"))
            if backslashes % 2 == 0:
                line = line[:i] + ("\n" if line.endswith("\n") else "")
                break
        lines.append(line)
    source = "".join(lines)
    result, depth, cursor = [], 0, 0
    for match in re.finditer(r"\\(iffalse|fi)\b", source):
        part = source[cursor:match.start()]
        result.append("\n" * part.count("\n") if depth else part)
        if match.group(1) == "iffalse":
            depth += 1
        elif depth:
            depth -= 1
        else:
            result.append(match.group())  # unrelated preamble conditional
        cursor = match.end()
    if depth:
        raise ValueError("Unclosed \\iffalse in manuscript")
    result.append(source[cursor:])
    return "".join(result)


def lean_code(source: str) -> str:
    """Mask Lean comments and strings so examples cannot count as imports.

    Lean block comments nest.  Preserve newlines and replace other ignored
    characters with spaces, allowing import detection on the remaining code.
    """
    result: list[str] = []
    i, depth, in_string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                result.append("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                result.append(" " + ("\n" if source[i + 1] == "\n" else " "))
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            result.append("  ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            result.append(" " * (end - i))
            i = end
        elif source[i] == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def manuscript_numbers(active: str) -> dict[int, str]:
    """Compute this manuscript's section-based result and equation numbers.

    The theorem environments share one counter, and ``equation`` has its own;
    both reset at each unstarred section. Count unlabelled environments too so
    inserting one cannot silently leave later blueprint numbers stale.
    ``active`` must have comments and disabled blocks removed by ``active_tex``.
    """
    environments = "|".join(sorted(ENVIRONMENTS | {"equation"}))
    pattern = r"\\section\s*(?:\[[^\]]*\]\s*)?\{|\\begin\{(" + environments + r")\}"
    section, result, equation = 0, 0, 0
    numbers = {}
    for match in re.finditer(pattern, active):
        environment = match.group(1)
        if environment is None:
            section += 1
            result, equation = 0, 0
        elif environment == "equation":
            equation += 1
            numbers[match.start()] = f"{section}.{equation}"
        else:
            result += 1
            numbers[match.start()] = f"{section}.{result}"
    return numbers


def validate(manifest: dict, manuscript: str, root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    nodes = manifest["nodes"]
    ids = [node["id"] for node in nodes]
    by_id = {node["id"]: node for node in nodes}
    for label, count in Counter(ids).items():
        if count != 1:
            errors.append(f"Duplicate blueprint node: {label}")
    active = active_tex(manuscript)
    labels = re.findall(r"\\label\{([^}]+)\}", active)
    for label, count in Counter(labels).items():
        if count != 1:
            errors.append(f"Duplicate active manuscript label: {label}")

    numbers = manuscript_numbers(active)
    numbered = []
    numbered_count = 0
    pattern = r"\\begin\{(" + "|".join(sorted(ENVIRONMENTS)) + r")\}(.*?)\\end\{\1\}"
    for match in re.finditer(pattern, active, re.S):
        numbered_count += 1
        # A labelled equation inside a theorem is a separate result; its label
        # cannot stand in for a missing label on the enclosing environment.
        body = re.sub(r"\\begin\{equation\}.*?\\end\{equation\}", "",
                      match.group(2), flags=re.S)
        found = re.findall(r"\\label\{([^}]+)\}", body)
        if not found:
            line = active.count("\n", 0, match.start()) + 1
            errors.append(f"Unlabelled active {match.group(1)} at line {line}")
            continue
        label = found[0]
        numbered.append(label)
        node = by_id.get(label)
        if node is None:
            errors.append(f"Missing manuscript result: {label}")
        elif node["source"]["environment"] != match.group(1):
            errors.append(f"Wrong manuscript environment for {label}")
        if node is not None and node["source"]["paper_number"] != numbers[match.start()]:
            errors.append(f"Wrong manuscript number for {label}: expected {numbers[match.start()]}")

    equations = []
    for match in re.finditer(r"\\begin\{equation\}(.*?)\\end\{equation\}", active, re.S):
        for label in re.findall(r"\\label\{([^}]+)\}", match.group(1)):
            equations.append(label)
            node = by_id.get(label)
            if node is None:
                errors.append(f"Missing labelled equation: {label}")
            else:
                if node["source"]["environment"] != "equation":
                    errors.append(f"Wrong manuscript environment for {label}")
                if node["source"]["paper_number"] != numbers[match.start()]:
                    errors.append(f"Wrong manuscript number for {label}: expected {numbers[match.start()]}")
    coverage = manifest["coverage"]
    if coverage["active_numbered_environments"] != numbered_count:
        errors.append("Active numbered-environment count is stale")
    if coverage["active_labelled_equations"] != len(equations):
        errors.append("Active labelled-equation count is stale")

    for node in nodes:
        label = node["id"]
        if type(node.get("proved_in_manuscript")) is not bool:
            errors.append(f"Missing or invalid manuscript-proof provenance for {label}")
        if node.get("proved_in_manuscript") and not node.get("manuscript_proof_note", "").strip():
            errors.append(f"Manuscript proof needs provenance evidence: {label}")
        if node["status"] not in manifest["status_definitions"]:
            errors.append(f"Unknown status for {label}: {node['status']}")
        if node["status"] == "formalized" and not node["lean_declarations"]:
            errors.append(f"Formalized node has no checked declaration: {label}")
        source = node["source"]
        if source["label"] is not None and source["label"] not in labels:
            errors.append(f"Source label is not active in manuscript: {source['label']}")
        if source["environment"] in ENVIRONMENTS and label not in numbered:
            errors.append(f"Node claims a nonexistent numbered result: {label}")
        if source["environment"] == "equation" and label not in equations:
            errors.append(f"Node claims a nonexistent labelled equation: {label}")
        if source["environment"] == "prose" and source["paper_number"] is not None:
            errors.append(f"Unnumbered manuscript prose has a paper number: {label}")
        if not (root / source["path"]).is_file():
            errors.append(f"Missing source file for {label}: {source['path']}")
        dependencies = set(node["dependencies"])
        if dependencies != set(node["statement_dependencies"]) | set(node["proof_dependencies"]):
            errors.append(f"Statement/proof dependencies disagree for {label}")
        for dependency in dependencies:
            if dependency not in by_id:
                errors.append(f"Unknown dependency of {label}: {dependency}")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(label: str, path: list[str]) -> None:
        if label in visiting:
            errors.append("Dependency cycle: " + " -> ".join(path + [label]))
            return
        if label in visited or label not in by_id:
            return
        visiting.add(label)
        for dependency in by_id[label]["dependencies"]:
            visit(dependency, path + [label])
        visiting.remove(label)
        visited.add(label)

    for label in ids:
        visit(label, [])
    target = manifest["target"]
    if target["node"] not in by_id:
        errors.append("Main theorem has no blueprint node")
    else:
        node = by_id[target["node"]]
        if target["lean_declaration"] not in node["lean_declarations"]:
            errors.append("Main theorem declaration disagrees with its node")
        if target["status"] != node["status"]:
            errors.append("Main theorem status disagrees with its node")

    # Every project module must be imported by the public root, so the axiom
    # audit cannot silently miss a module that was left outside the root.
    imported: set[str] = set()

    def imports(path: Path) -> None:
        code = lean_code(path.read_text())
        for group in re.findall(r"^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)", code, re.M):
            for name in group.split():
                if not re.fullmatch(r"Omega(?:\.\w+)*", name) or name in imported:
                    continue
                imported.add(name)
                dependency = root / (name.replace(".", "/") + ".lean")
                if dependency.is_file():
                    imports(dependency)
                else:
                    errors.append(f"Imported project module does not exist: {name}")

    if (root / "Omega.lean").is_file():
        imports(root / "Omega.lean")
    else:
        errors.append("Public root module is missing: Omega.lean")
    for path in (root / "Omega").rglob("*.lean"):
        name = ".".join(path.relative_to(root).with_suffix("").parts)
        if name not in imported:
            errors.append(f"Module is not covered by root imports and audit: {name}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ROOT / "blueprint/manifest.json")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    manuscript = (ROOT / manifest["manuscript"]).read_text()
    errors = validate(manifest, manuscript)
    if (ROOT / "blueprint/src/content.tex").read_text() != render(manifest):
        errors.append("Generated blueprint is stale: run python3 scripts/render_blueprint.py")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    checked = sum(node["status"] == "formalized" for node in manifest["nodes"])
    print(f"Blueprint checks passed: {len(manifest['nodes'])} nodes, {checked} formalized; "
          f"main theorem {manifest['target']['status']}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
