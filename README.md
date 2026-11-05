# Tensor value and the 9/4 bound for matrix multiplication

A Lean and mathlib formalization of the manuscript by M. Levent Doğan,
Vladimir Lysikov, Keiya Sakabe, and Michael Walter.

[Blueprint](https://qit-lmu.github.io/omega/web/) ·
[Coverage](docs/coverage.md)

The main theorem in [Omega/Main.lean](Omega/Main.lean) is:

```lean
theorem MatrixMultiplication.omega_le_nine_quarters
    (K : Type u) [Field K] :
    MatrixMultiplication.omega K ≤ (9 : ℝ) / 4
```

It holds over every field, with no characteristic, cardinality, or
algebraic-closure assumptions. The proof uses fractional symmetrized tensor
value, degenerations of polynomial multiplication, and an elementary growth
argument, without spectral points.

`omega K` is the base-two logarithm of the asymptotic rank of the 2 × 2 matrix
multiplication tensor. The library also identifies it with the infimum of
ordinary-rank logarithmic bounds. The manuscript's arithmetic-operation
interpretation is expository: this project does not formalize a computational
model or prove that its complexity exponent equals `omega`.

## Build and check

Run the commands below from the repository root. Lean and mathlib are pinned
in [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json). Blueprint Python dependencies are
pinned in [blueprint/uv.lock](blueprint/uv.lock).

### Lean library only

Install Git and [elan](https://github.com/leanprover/elan), and ensure `lake`
is on your `PATH`. Elan selects the repository's pinned Lean toolchain.

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

The cache command downloads precompiled mathlib artifacts. The final command
checks all imported project declarations, including private helpers, against
`propext`, `Classical.choice`, and `Quot.sound` only.

### Full checks and blueprint

In addition to the Lean tools, install these prerequisites **before** running
`make check`:

- [uv](https://docs.astral.sh/uv/) for the locked blueprint environment.
- Python 3.11 or newer and Make for repository scripts and build commands. The blueprint
  environment selects Python 3.13 through `blueprint/.python-version`.
- Graphviz, its development libraries/headers, `pkg-config`, and a C compiler
  for platforms where Python's Graphviz binding must be built from source.
- A TeX distribution providing `kpsewhich` for the HTML renderer. For the PDF,
  it must also provide `latexmk`, AMS packages, and Latin Modern fonts.

On Ubuntu, these are the blueprint system packages installed by CI:

```sh
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  graphviz libgraphviz-dev pkg-config \
  latexmk texlive-latex-recommended texlive-fonts-recommended lmodern
```

Also ensure Python 3.11 or newer, Make, and a C compiler are available. On macOS, use a
TeX distribution such as [MacTeX](https://www.tug.org/mactex/) and install
[Graphviz](https://graphviz.org/download/), its development files, and compiler
tools as appropriate for your package manager. Put their executables on `PATH`.

```sh
lake exe cache get
uv sync --project blueprint --locked --cache-dir .lake/uv-cache
make check
make blueprint-pdf
```

`make check` compiles Lean, audits axioms, validates manuscript coverage and the
dependency graph, builds the HTML blueprint and declaration index, verifies
linked declarations, and runs tooling regression tests. The separate PDF
command generates the printable blueprint.

### Browse a local build

```sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint
```

Open [the local blueprint](http://127.0.0.1:8000/web/). Serve the entire
`blueprint/` directory so links to the sibling `docs/` directory work.
Generated outputs are ignored by Git:

| Output | Location |
| --- | --- |
| HTML blueprint | `blueprint/web/index.html` |
| Dependency graph | `blueprint/web/dep_graph_document.html` |
| Checked declaration index | `blueprint/docs/find/index.html` |
| Printable blueprint | `blueprint/print/print.pdf` |

## Scope and repository layout

All mathematical entries in the audited blueprint are formalized, covering
34 active numbered manuscript environments, 14 labelled equations, and tracked
background assertions. The exponent convention, computational interpretation,
and historical comparisons are expository. The checked library contains no
`sorry` or project axioms. See the [coverage guide](docs/coverage.md) for the
full result inventory and documented differences between manuscript and Lean
proofs.

| Path | Purpose |
| --- | --- |
| [material/main.tex](material/main.tex) | Manuscript with stable result labels |
| [Omega.lean](Omega.lean) | Public root importing every project module |
| [Omega/](Omega/) | Tensor foundations, value calculus, and exponent proof |
| [blueprint/manifest.json](blueprint/manifest.json) | Canonical correspondence and dependency graph |
| [blueprint/src/content.tex](blueprint/src/content.tex) | Generated TeX; edit the manifest instead |
| [scripts/](scripts/) | Coverage, rendering, declaration checks, and axiom audit |

## Prove2Me corollary

The public [Prove2Me statement](https://prove2.me/theorems/f2b5622a-3bca-4b8f-92a1-381d10af16e3)
is proved as `mme_omega_le_225` in
[Omega/External/Prove2Me.lean](Omega/External/Prove2Me.lean). Its downloaded
definition bodies are preserved unchanged. A checked tensor-coordinate bridge
identifies the ranks, and `MME.matMulExp_eq_omega` identifies its ordinary-rank
infimum with this library's exponent; the corollary then applies the main theorem.

The original statement, definitions, source URLs, and hashes are archived in
[material/prove2me/](material/prove2me/). The archived statement's proof
placeholder is reference text only; no external solution is imported.

## Development and publication

See the [development guide](docs/development.md) for the result-update
workflow, manuscript corrections, blueprint graph conventions, and GitHub Pages
setup. CI checks Lean, project axioms, coverage, declarations, and blueprint
outputs. Successful default-branch runs publish the site; pull requests produce
build artifacts without deploying.
