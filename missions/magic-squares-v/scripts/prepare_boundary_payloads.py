"""Prepare reviewable public payloads; this script performs no network writes."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "missions/magic-squares-v/submissions"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
SOURCE = (
    "Original matching-board specialization of the Eulerian face-lattice property "
    "and the order-dual of Weisner's theorem; derived in MATCHING-BOUNDARY-SOURCE.md. "
    "Richard P. Stanley, Enumerative Combinatorics, Volume 1, author manuscript, "
    "Proposition 3.8.9, p. 309, and Corollary 3.9.3, p. 313: "
    "https://math.mit.edu/~rstan/ec/ec1.pdf. "
    "This matching-board statement is our specialization, not a verbatim theorem in that source."
)
STATEMENT = r"""Let $n\ge 1$ and let a board be a subset of $[n]\times[n]$. For a permutation $\sigma$, write $\phi_\sigma=\{(i,\sigma(i)):i\in[n]\}$. A board is matching-covered if it is nonempty and each of its cells belongs to some permutation support contained in the board. Define
$$a(C)=\sum_{S\subseteq C}(-1)^{|S|}\mathbf 1\{C\setminus S\text{ contains a permutation support}\}.$$

For any matching-covered boards $D\subseteq B$ and any permutation support $\phi_\sigma\subseteq B$, the following finite boundary identity holds:
$$\sum_{\substack{D\subseteq C\subseteq B\\B\setminus\phi_\sigma\subseteq C}}a(C)=\begin{cases}a(B),&\phi_\sigma\subseteq D,\\0,&\phi_\sigma\nsubseteq D.\end{cases}$$

The summation includes all such boards $C$, without requiring them to be matching-covered. This identity provides a finite combinatorial sufficient condition for reciprocity of semi-magic counting polynomials. Its formal proof is the remaining obligation in the associated conditional reduction."""

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    definition = (ROOT / "Definitions/Def_MagicSquaresMatchingBoundary.lean").read_text(encoding="utf-8")
    mirror = (ROOT / "Theorems/Thm_MagicSquares_matching_boundary_euler.lean").read_text(encoding="utf-8")
    formal = "\n".join(line for line in mirror.splitlines() if not line.startswith("import ")).strip()
    payloads = {
        "boundary-definition-payload.json": {
            "definition_name": "MagicSquaresMatchingBoundary",
            "definition_title": "Finite matching-board boundary coefficients",
            "definition": definition,
            "natural_language_statement": STATEMENT.split("For any matching-covered")[0] + "These finite definitions specify the boundary identity used in a reduction of semi-magic reciprocity.",
            "source": SOURCE, "tags": ["combinatorics", "magic-squares", "mobius-inversion"], "env": ENV,
        },
        "boundary-problem-payload.json": {
            "problems": [{
                "theorem_name": "MagicSquares.matching_boundary_euler",
                "theorem_title": "Matching-covered board boundary cancellation",
                "formal_statement": formal,
                "natural_language_statement": STATEMENT,
                "preamble": "import Mathlib\nimport Definitions.Def_MagicSquaresMatchingBoundary",
                "source": SOURCE, "tags": ["combinatorics", "magic-squares", "mobius-inversion"],
            }], "env": ENV,
        },
    }
    for name, payload in payloads.items():
        (OUT / name).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(name)

if __name__ == "__main__":
    main()
