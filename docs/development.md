# Development and blueprint guide

[Project overview and setup](../README.md) · [Coverage and module map](coverage.md)

## Editing results

The [manifest](../blueprint/manifest.json) is the source of truth for blueprint
statements, proof plans, status, and dependencies. Do not edit the generated
[content.tex](../blueprint/src/content.tex) directly.

1. Implement and check the Lean declaration, adding any new module to
   [Omega.lean](../Omega.lean) so the whole-library audit covers it.
2. Update the manifest with exact public declaration names and dependency edges.
   Keep manuscript labels stable. Separate helper nodes when only part of a
   manuscript claim is proved.
3. Record whether the manuscript itself supplies a proof, with a short
   provenance note. A Lean proof or blueprint proof plan does not establish this.
4. Run `python3 scripts/render_blueprint.py`, then `make check` from the repository
   root. Run `make blueprint-pdf` after changes that affect printable content.
5. Mark a node `formalized` only when its complete stated claim is checked,
   then regenerate and rerun the checks with that final status.

When formalization reveals a manuscript bug or imprecision, report the relevant
result label, the issue, and a proposed correction. When annotating
[the manuscript](../material/main.tex), use a precise `\MW{...}` comment rather
than silently changing the mathematical claim. Keep blueprint statements and
proof obligations consistent with the claim actually formalized.

## Checks and outputs

Install the [documented prerequisites](../README.md#build-and-check) first.
Commands below run from the repository root.

| Command | Checks or output |
| --- | --- |
| `lake build` | Compile the Lean library |
| `lake env lean scripts/Audit.lean` | Audit transitive axioms after compilation |
| `make coverage` | Validate manuscript coverage, dependency graph, root imports, and generated TeX |
| `make tooling-tests` | Run the blueprint tooling regression tests |
| `make check` | Compile, audit, validate, build HTML and declaration docs, then run tooling tests |
| `make blueprint-web` | Build Lean, validate coverage, and generate HTML plus declaration docs |
| `make blueprint-pdf` | Validate coverage and generate the printable blueprint |

The three rendered-HTML tests require an existing web build; they are skipped
when it is absent. `make check` builds HTML before running them. Generated
artifacts under `blueprint/web/`, `blueprint/docs/`, and `blueprint/print/` are
ignored by Git. Serve the entire `blueprint/` directory so declaration links
from `web/` to `docs/` resolve.

## Reading the blueprint

Each active numbered paper result has its own blueprint node. Additional
infrastructure is explicitly marked auxiliary. Generic theorems and their
tensor applications have separate nodes, so progress is not overstated.
`planned` and `notready` nodes are proof obligations, not assumptions available
to Lean. Formalized nodes link only to checked declarations.

Graph nodes use **boxes** for theorems, lemmas, corollaries, and propositions,
as well as equations, and **ellipses** for definitions and remarks.
Paper results retain their manuscript numbers (for example, Lemma 6.1 and
Theorem 6.3); equations retain their separate manuscript numbering. Added
foundations use **A1, A2, …**. These labels appear in headings, references,
graph nodes, and graph popups in the web blueprint, and in the PDF.
Nodes have **bold borders** when
the manuscript supplies a proof or derivation, including known results reproved
here. Cited inputs and additional
formalization helpers keep thin borders. The manifest's `proved_in_manuscript`
flag and `manuscript_proof_note` record this independently of Lean status;
colors continue to show formalization progress. A local plasTeX package applies
the borders whenever the web blueprint is rebuilt.
**Light green backgrounds** mark completed formalized definitions, which have
no separate theorem proof to supply. **Dark green backgrounds** mark results
whose proofs and dependencies are formalized, including remarks with checked proofs.
The main result has a larger **MAIN RESULT — ω ≤ 9/4 — over every field** label
and a double border. The reading guide links directly to its theorem and Lean proof.

## CI and GitHub Pages

The [GitHub Actions workflow](../.github/workflows/check.yml) runs on pushes,
pull requests, and manual dispatch. It builds Lean, audits project axioms,
checks manuscript coverage, generates HTML and the declaration index, runs
tooling tests, and builds the printable blueprint.

In **Settings → Pages**, set **Build and deployment → Source** to
**GitHub Actions**. Successful runs on the default branch publish to Pages;
pull requests only produce a downloadable build artifact. The build job has
read-only repository permissions. Pages and identity-token write permissions
are confined to the separate deployment job.

The staged site contains generated files only: `web/`, `docs/`, and
`print/print.pdf`. Its root redirects to `web/`. Keep `web/` and `docs/` as
siblings to preserve declaration links at project-site URLs.
