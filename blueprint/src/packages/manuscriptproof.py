"""Show manuscript numbers and style proofs independently of Lean colors.

The pinned depgraph plugin exposes a document-local shape map and a post-parse
graph inventory, but no per-node penwidth hook. Decorate each document's to_dot
method after graph construction; do not change the installed package or global
class. The attributes survive transitive reduction and SVG rendering.
"""

from pathlib import Path

from plasTeX import Command
from plasTeX.PackageResource import PackageTemplateDir


class manuscriptproof(Command):
    """Mark the enclosing theorem as having a proof in the manuscript."""

    def digest(self, tokens):
        super().digest(tokens)
        self.parentNode.userdata["manuscriptproof"] = True


class mainresult(Command):
    """Highlight the enclosing theorem, using its argument as the formula."""

    args = "label:str"

    def digest(self, tokens):
        super().digest(tokens)
        self.parentNode.userdata["mainresult"] = self.attributes["label"]


def with_manuscript_labels_and_borders(graph):
    original_to_dot = graph.to_dot

    def to_dot(shapes):
        dot = original_to_dot(shapes)
        for node in graph.nodes:
            attrs = dot.get_node(node.id).attr
            reference = f"{node.caption} {node.ref.textContent.strip()}"
            attrs["label"] = reference + r"\n" + attrs["label"]
            if node.userdata.get("manuscriptproof"):
                attrs["penwidth"] = "4"
                attrs["class"] = "manuscript-proof"
                attrs["tooltip"] = "Proof or derivation supplied in the manuscript"
            main_label = node.userdata.get("mainresult")
            if main_label:
                attrs["peripheries"] = "2"
                attrs["fontsize"] = "18"
                attrs["margin"] = "0.20,0.12"
                attrs["label"] = (r"MAIN RESULT\n" + reference + r"\n"
                                  + main_label + r"\nover every field")
        return dot

    return to_dot


def ProcessOptions(options, document):
    # Also correct the pinned HTML5 hyperref template: its parser records an
    # idref label, while the bundled template expects obsolete URL fields.
    document.addPackageResource(PackageTemplateDir(
        path=Path(__file__).parent / "templates"))

    def style_graphs():
        data = document.userdata["dep_graph"]
        data.setdefault("shapes", {}).update({
            "definition": "ellipse",
            "theorem": "box",
            "lemma": "box",
            "corollary": "box",
            "proposition": "box",
            "equationresult": "box",
            "remark": "ellipse",
        })
        shape_legend = {
            "Boxes": "theorems, lemmas, corollaries, propositions, and equations",
            "Ellipses": "definitions and remarks",
        }
        legend = []
        for label, description in data["legend"]:
            if label == f"{data['colors']['proved'][1]} background":
                legend.append((
                    f"{data['colors']['defined'][1]} background",
                    "the <em>definition</em> is formalized and complete; "
                    "there is no separate theorem proof to supply"))
            legend.append((label, shape_legend.get(label, description)))
        data["legend"] = legend
        for graph in data["graphs"].values():
            graph.to_dot = with_manuscript_labels_and_borders(graph)
        data["legend"].extend([
            ("Numbering", "paper results and equations use their manuscript numbers; "
             "A1, A2, and so on label added foundations"),
            ("Double border", "the main result: omega is at most 9/4 over every field"),
            ("Bold border", "a proof or derivation is supplied in the manuscript, "
             "including prior results reproved here; independent of Lean status"),
            ("Thin border", "other nodes, including cited inputs, definitions, "
             "and added formalization helpers"),
        ])

    # depgraph constructs graphs at 110; leanblueprint adds its colors and
    # legend at 150. Rendering (and transitive reduction) happens later.
    document.addPostParseCallbacks(160, style_graphs)
