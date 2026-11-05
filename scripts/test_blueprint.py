"""Regression tests for manuscript coverage and honest blueprint/audit status.

All mutations use in-memory copies or temporary directories.  These tests do
not edit the manuscript, manifest, generated blueprint, or project modules.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from check_blueprint import ROOT, active_tex, lean_code, validate
from render_blueprint import render


MANIFEST = json.loads((ROOT / "blueprint/manifest.json").read_text())
MANUSCRIPT = (ROOT / MANIFEST["manuscript"]).read_text()


class ActiveTexTests(unittest.TestCase):
    def test_comments_respect_escaped_percent_and_preserve_lines(self):
        source = "visible \\% still visible % hidden\n" + "two \\\\% hidden too\n"
        result = active_tex(source)
        self.assertIn(r"\% still visible", result)
        self.assertNotIn("hidden", result)
        self.assertEqual(result.count("\n"), source.count("\n"))

    def test_nested_disabled_blocks_and_commented_directives(self):
        source = (
            "before\n% \\iffalse is commented\n"
            "\\iffalse\nouter\n\\iffalse\ninner\n\\fi\nstill outer\n\\fi\nafter\n"
        )
        result = active_tex(source)
        self.assertIn("before", result)
        self.assertIn("after", result)
        self.assertNotIn("outer", result)
        self.assertNotIn("inner", result)
        self.assertEqual(result.count("\n"), source.count("\n"))

    def test_unclosed_disabled_block_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unclosed"):
            active_tex("\\iffalse\nmissing end\n")


class ManifestValidationTests(unittest.TestCase):
    def setUp(self):
        self.manifest = copy.deepcopy(MANIFEST)
        self.manuscript = MANUSCRIPT
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "material").mkdir()
        (self.root / "material/main.tex").write_text(self.manuscript)
        for source in {node["source"]["path"] for node in self.manifest["nodes"]}:
            if source == self.manifest["manuscript"]:
                continue
            target = self.root / source
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / source).read_bytes())
        (self.root / "Omega").mkdir(exist_ok=True)
        # Auxiliary results can cite Lean files. Keep those source paths real,
        # but isolate these tests from their production dependency graph.
        source_modules = []
        for path in (self.root / "Omega").rglob("*.lean"):
            path.write_text("module\n")
            source_modules.append(".".join(path.relative_to(self.root).with_suffix("").parts))
        self.source_imports = "".join(f"public import {name}\n" for name in sorted(source_modules))
        (self.root / "Omega.lean").write_text("module\npublic import Omega.Core\n")
        (self.root / "Omega/Core.lean").write_text("module\n" + self.source_imports)

    def errors(self):
        return validate(self.manifest, self.manuscript, self.root)

    def node(self, label):
        return next(node for node in self.manifest["nodes"] if node["id"] == label)

    def assert_error(self, text):
        self.assertTrue(any(text in error for error in self.errors()), self.errors())

    def test_current_manifest_is_valid(self):
        self.assertEqual(self.errors(), [])

    def test_commented_and_disabled_duplicate_results_are_ignored(self):
        duplicate = r"\begin{lemma}\label{lem:flattening-lb}old\end{lemma}"
        self.manuscript += "\n% " + duplicate + "\n\\iffalse\n" + duplicate + "\n\\fi\n"
        self.assertEqual(self.errors(), [])

    def test_missing_result_label_is_reported(self):
        self.manuscript = self.manuscript.replace(r"\label{lem:flattening-lb}", "", 1)
        self.assert_error("Unlabelled active lemma")

    def test_missing_manifest_result_is_reported(self):
        self.manifest["nodes"].remove(self.node("lem:flattening-lb"))
        self.assert_error("Missing manuscript result: lem:flattening-lb")

    def test_missing_labelled_equation_is_reported(self):
        self.manifest["nodes"].remove(self.node("eq:matmul-normalization"))
        self.assert_error("Missing labelled equation: eq:matmul-normalization")

    def test_nested_equation_needs_its_own_manifest_entry(self):
        self.manifest["nodes"].remove(self.node("eq:lem4/3"))
        errors = self.errors()
        self.assertIn("Missing labelled equation: eq:lem4/3", errors)
        self.assertFalse(any("Missing manuscript result: lem:4/3" in error for error in errors))

    def test_nested_equation_label_cannot_replace_lemma_label(self):
        self.manuscript = self.manuscript.replace(r"\label{lem:4/3}", "", 1)
        errors = self.errors()
        self.assertTrue(any("Unlabelled active lemma" in error for error in errors), errors)
        self.assertIn("Node claims a nonexistent numbered result: lem:4/3", errors)
        self.assertNotIn("Wrong manuscript environment for eq:lem4/3", errors)
        self.assertNotIn("Active numbered-environment count is stale", errors)

    def test_unlabelled_quotient_remark_is_reported_without_changing_count(self):
        self.manuscript = self.manuscript.replace(r"\label{rem:quotient-degeneration}", "", 1)
        errors = self.errors()
        self.assertTrue(any("Unlabelled active remark" in error for error in errors), errors)
        self.assertNotIn("Active numbered-environment count is stale", errors)

    def test_added_unlabelled_remark_increases_coverage_count(self):
        self.manuscript += "\n" + r"\begin{remark}An additional result.\end{remark}" + "\n"
        self.assert_error("Unlabelled active remark")
        self.assert_error("Active numbered-environment count is stale")

    def test_wrong_paper_numbers_are_reported(self):
        self.node("lem:flattening-lb")["source"]["paper_number"] = "2.9"
        self.node("eq:omega-log-n")["source"]["paper_number"] = None
        self.assert_error("Wrong manuscript number for lem:flattening-lb: expected 2.3")
        self.assert_error("Wrong manuscript number for eq:omega-log-n: expected 2.6")

    def test_new_unlabelled_environments_shift_later_paper_numbers(self):
        self.manuscript = self.manuscript.replace(
            r"\label{eq:omega-log-n}",
            r"\end{equation}\begin{equation}\label{eq:omega-log-n}", 1)
        self.manuscript = self.manuscript.replace(
            r"\label{lem:flattening-lb}",
            r"\end{lemma}\begin{lemma}\label{lem:flattening-lb}", 1)
        self.assert_error("Wrong manuscript number for eq:omega-log-n: expected 2.7")
        self.assert_error("Wrong manuscript number for lem:flattening-lb: expected 2.4")

    def test_starred_sections_and_disabled_equations_do_not_shift_numbers(self):
        self.manuscript = self.manuscript.replace(
            r"\label{eq:schonhages-ineq}",
            "\\section*{Unnumbered note}\n"
            "% \\begin{equation}x=0\\end{equation}\n"
            "\\iffalse\\begin{equation}x=0\\end{equation}\\fi\n"
            r"\label{eq:schonhages-ineq}", 1)
        self.assertEqual(self.errors(), [])

    def test_active_duplicate_label_is_reported(self):
        self.manuscript += "\n\\label{lem:flattening-lb}\n"
        self.assert_error("Duplicate active manuscript label: lem:flattening-lb")

    def test_disabled_label_cannot_be_used_as_a_source(self):
        self.manuscript += "\n\\iffalse\\label{disabled:only}\\fi\n"
        self.node("aux:entropy")["source"]["label"] = "disabled:only"
        self.assert_error("Source label is not active in manuscript: disabled:only")

    def test_stale_coverage_counts_are_reported(self):
        self.manifest["coverage"]["active_numbered_environments"] += 1
        self.manifest["coverage"]["active_labelled_equations"] += 1
        self.assert_error("Active numbered-environment count is stale")
        self.assert_error("Active labelled-equation count is stale")

    def test_cycle_is_reported_with_both_nodes(self):
        first, second = "aux:entropy", "lem:optimize-sum"
        self.node(first)["dependencies"].append(second)
        self.node(first)["proof_dependencies"].append(second)
        cycles = [error for error in self.errors() if error.startswith("Dependency cycle:")]
        self.assertTrue(cycles)
        self.assertTrue(any(first in error and second in error for error in cycles))

    def test_unknown_dependency_is_reported(self):
        self.node("aux:entropy")["dependencies"].append("missing:result")
        self.node("aux:entropy")["proof_dependencies"].append("missing:result")
        self.assert_error("Unknown dependency of aux:entropy: missing:result")

    def test_statement_proof_dependency_drift_is_reported(self):
        self.node("lem:optimize-sum")["proof_dependencies"] = []
        self.assert_error("Statement/proof dependencies disagree for lem:optimize-sum")

    def test_stale_main_target_status_cannot_claim_completion(self):
        current = self.manifest["target"]["status"]
        self.manifest["target"]["status"] = "planned" if current == "formalized" else "formalized"
        self.assert_error("Main theorem status disagrees with its node")

    def test_main_target_declaration_must_match(self):
        self.manifest["target"]["lean_declaration"] = "MatrixMultiplication.different_theorem"
        self.assert_error("Main theorem declaration disagrees with its node")

    def test_formalized_node_must_have_a_checked_declaration(self):
        self.node("aux:numerical-endpoint")["lean_declarations"] = []
        self.assert_error("Formalized node has no checked declaration: aux:numerical-endpoint")

    def test_manuscript_proof_provenance_is_explicit_and_boolean(self):
        del self.node("lem:flattening-lb")["proved_in_manuscript"]
        self.node("lem:optimize-sum")["proved_in_manuscript"] = "false"
        self.assert_error("Missing or invalid manuscript-proof provenance for lem:flattening-lb")
        self.assert_error("Missing or invalid manuscript-proof provenance for lem:optimize-sum")

    def test_manuscript_proof_requires_provenance_evidence(self):
        self.node("lem:flattening-lb")["manuscript_proof_note"] = ""
        self.assert_error("Manuscript proof needs provenance evidence: lem:flattening-lb")

    def test_unimported_module_is_not_covered_by_audit(self):
        (self.root / "Omega/Hidden.lean").write_text("module\n")
        self.assert_error("Module is not covered by root imports and audit: Omega.Hidden")

    def test_nested_block_comment_import_does_not_count_for_audit(self):
        (self.root / "Omega/Hidden.lean").write_text("module\n")
        with (self.root / "Omega.lean").open("a") as file:
            file.write("/- Outer\n/- Inner -/\nimport Omega.Hidden\n-/\n")
        self.assert_error("Module is not covered by root imports and audit: Omega.Hidden")

    def test_string_import_does_not_count_for_audit(self):
        (self.root / "Omega/Hidden.lean").write_text("module\n")
        with (self.root / "Omega.lean").open("a") as file:
            file.write('def example := "example\\\"\nimport Omega.Hidden\n"\n')
        self.assert_error("Module is not covered by root imports and audit: Omega.Hidden")

    def test_public_transitive_imports_and_trailing_comments_are_covered(self):
        (self.root / "Omega/Leaf.lean").write_text("module\n")
        (self.root / "Omega/Core.lean").write_text(
            "module\n" + self.source_imports + "public import Omega.Leaf -- used\n")
        self.assertEqual(self.errors(), [])

    def test_multiple_imports_on_one_line_are_covered(self):
        (self.root / "Omega/Leaf.lean").write_text("module\n")
        (self.root / "Omega.lean").write_text("import Omega.Core Omega.Leaf -- both\n")
        self.assertEqual(self.errors(), [])

    def test_missing_root_and_imported_module_are_reported(self):
        (self.root / "Omega.lean").unlink()
        self.assert_error("Public root module is missing: Omega.lean")
        (self.root / "Omega.lean").write_text("import Omega.Absent\n")
        self.assert_error("Imported project module does not exist: Omega.Absent")


class RendererTests(unittest.TestCase):
    def test_pending_results_prevent_global_completion_claim(self):
        manifest = copy.deepcopy(MANIFEST)
        for node in manifest["nodes"]:
            if node["status"] in {"planned", "notready"}:
                node["status"] = "formalized"
        complete_claim = "All mathematical entries in the audited blueprint are formalized."
        self.assertIn(complete_claim, render(manifest))
        pending = next(node for node in manifest["nodes"]
                       if node["id"] == "rem:quotient-degeneration")
        for status in ("planned", "notready"):
            with self.subTest(status=status):
                pending["status"] = status
                content = render(manifest)
                self.assertNotIn(complete_claim, content)
                self.assertIn("1 mathematical entries still have pending proof obligations.", content)
                self.assertNotIn("@COVERAGE_STATUS@", content)

    def test_manuscript_markers_are_independent_of_lean_status(self):
        for status in MANIFEST["status_definitions"]:
            manifest = copy.deepcopy(MANIFEST)
            for node in manifest["nodes"]:
                if node["id"] == "lem:flattening-lb":
                    node["status"] = status
            content = render(manifest)
            marked = re.findall(r"\\label\{([^}]+)\}\s*\\manuscriptproof", content)
            expected = [node["id"] for node in manifest["nodes"]
                        if node["proved_in_manuscript"]]
            self.assertCountEqual(marked, expected)

    def test_only_checked_nodes_get_lean_links(self):
        content = render(MANIFEST)
        linked = {
            name for names in re.findall(r"\\lean\{([^}]+)\}", content)
            for name in names.split(",")
        }
        checked = {
            name for node in MANIFEST["nodes"] if node["status"] == "formalized"
            for name in node["lean_declarations"]
        }
        self.assertEqual(linked, checked)
        self.assertEqual(MANIFEST["target"]["lean_declaration"] in linked,
                         MANIFEST["target"]["status"] == "formalized")

    def test_all_proofs_are_explicitly_bound_to_their_statement(self):
        content = render(MANIFEST)
        owners = re.findall(r"\\begin\{proof\}\s*\\proves\{([^}]+)\}", content)
        expected = [
            node["id"] for node in MANIFEST["nodes"]
            if node["proof_plan_tex"] or node["proof_dependencies"]
        ]
        self.assertCountEqual(owners, expected)
        self.assertEqual(content.count(r"\begin{proof}"), len(owners))

    def test_expository_nodes_have_no_proof_wrapper(self):
        content = render(MANIFEST)
        notes = [node for node in MANIFEST["nodes"] if node["status"] == "expository"]
        self.assertTrue(notes)
        for node in notes:
            with self.subTest(label=node["id"]):
                start = content.index("\\label{" + node["id"] + "}")
                end = content.find(r"\renewcommand{\thetheorem}", start)
                block = content[start:end if end != -1 else len(content)]
                self.assertNotIn(r"\begin{proof}", block)
                self.assertNotIn(r"\textit{Planned proof.}", block)
                self.assertNotIn(r"\textit{Checked proof.}", block)

    def test_propositions_supported_by_checker_are_renderable(self):
        manifest = copy.deepcopy(MANIFEST)
        manifest["nodes"][0]["kind"] = "proposition"
        self.assertIn(r"\begin{proposition}", render(manifest))

    def test_external_output_path_and_staleness_check(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            manifest = path / "manifest.json"
            output = path / "content.tex"
            manifest.write_text(json.dumps(MANIFEST))
            command = [sys.executable, str(ROOT / "scripts/render_blueprint.py"),
                       "--manifest", str(manifest), "--output", str(output)]
            built = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(built.returncode, 0, built.stderr)
            checked = subprocess.run(command + ["--check"], capture_output=True, text=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            output.write_text("stale")
            stale = subprocess.run(command + ["--check"], capture_output=True, text=True)
            self.assertEqual(stale.returncode, 1)


@unittest.skipUnless((ROOT / "blueprint/web/dep_graph_document.html").exists(),
                     "Rendered web blueprint is not available")
class RenderedHtmlTests(unittest.TestCase):
    def test_graph_borders_match_manuscript_proofs(self):
        graph = (ROOT / "blueprint/web/dep_graph_document.html").read_text()
        self.assertIn("<dt>Bold border</dt>", graph)
        self.assertIn("independent of Lean status", graph)
        for node in MANIFEST["nodes"]:
            with self.subTest(label=node["id"]):
                match = re.search(r'"' + re.escape(node["id"]) + r'"\s*\[([^\]]+)', graph)
                self.assertIsNotNone(match)
                attrs = match.group(1)
                self.assertEqual('class="manuscript-proof"' in attrs,
                                 node["proved_in_manuscript"])
                self.assertEqual('penwidth=4' in attrs, node["proved_in_manuscript"])

    def test_proof_links_and_pending_vs_checked_status(self):
        html = "\n".join(path.read_text() for path in (ROOT / "blueprint/web").glob("sect*.html"))
        labels = {"aux:numerical-endpoint", "eq:PM-recurrence",
                  "aux:polynomial-value-elementary-growth", "aux:prove2me-statement",
                  "thm:omega-le-nine-fourths"}
        cases = {node["id"]: node["status"] == "formalized"
                 for node in MANIFEST["nodes"] if node["id"] in labels}
        self.assertEqual(set(cases), labels)
        for label, checked in cases.items():
            with self.subTest(label=label):
                start = html.index(f'id="{label}"')
                rest = html[start:]
                proof = re.search(r'<div class="proof_wrapper" id="([^\"]+)"', rest)
                self.assertIsNotNone(proof)
                heading = rest[:proof.start()]
                self.assertIn("#" + proof.group(1), heading)
                self.assertEqual('class="lean_decl"' in heading, checked)
                proof_content = rest[proof.start():].split('class="proof_content">', 1)[1]
                self.assertIn("Checked proof." if checked else "Planned proof.",
                              proof_content.split("</div>", 1)[0])

    def test_graph_connects_generic_proofs_to_pending_paper_instances(self):
        graph = (ROOT / "blueprint/web/dep_graph_document.html").read_text()
        for origin, target in [
            ("aux:numerical-recurrence", "eq:PM-recurrence"),
            ("aux:numerical-elementary-growth", "aux:polynomial-value-elementary-growth"),
            ("aux:numerical-endpoint", "thm:omega-le-nine-fourths"),
        ]:
            self.assertIn(f'"{origin}" -> "{target}"', graph)
        pending = re.search(r'"thm:omega-le-nine-fourths"\s*\[([^\]]+)', graph)
        self.assertIsNotNone(pending)
        if MANIFEST["target"]["status"] == "notready":
            self.assertIn('color="#FFAA33"', pending.group(1))


if __name__ == "__main__":
    unittest.main()
