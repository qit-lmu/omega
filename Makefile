UV_RUN = uv run --project blueprint --locked --cache-dir .lake/uv-cache
.DEFAULT_GOAL := check

.PHONY: check lean coverage tooling-tests blueprint-web blueprint-pdf

lean:
	lake build

coverage:
	python3 scripts/check_blueprint.py
	python3 scripts/render_blueprint.py --check

tooling-tests:
	python3 -m unittest discover -s scripts -p 'test_*.py'

check: lean coverage
	lake env lean scripts/Audit.lean
	$(UV_RUN) leanblueprint web
	$(UV_RUN) leanblueprint checkdecls
	lake exe checkdecls blueprint/lean_decls --docs
	$(MAKE) tooling-tests

blueprint-web: lean coverage
	$(UV_RUN) leanblueprint web
	lake exe checkdecls blueprint/lean_decls --docs

blueprint-pdf: coverage
	$(UV_RUN) leanblueprint pdf
