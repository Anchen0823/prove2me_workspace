"""Append the 2026-09-25 DAG-wiring section to the private mission description.

Guards: the live description must equal the current local file before the edit
(otherwise someone changed it remotely and we would clobber their text), and the
edit is read back verbatim afterwards.  The hash recorded in
new-results-receipt.json is refreshed so that publish_new_dag_results.py keeps
working.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PLATFORM = HERE.parent
sys.path.insert(0, str(PLATFORM))
from sync_private_proposal import RECEIPT, get_token, request  # noqa: E402

DESCRIPTION = PLATFORM / "mission-description.md"
RESULTS_RECEIPT = PLATFORM / "new-results-receipt.json"
MARKER = "## Platform DAG wiring update, 25 September 2026"

SECTION = """
## Platform DAG wiring update, 25 September 2026

The goal theorem now carries machine-checked decompositions instead of standing as a
bare open leaf. Two independent reductions of the goal were accepted as
proof-sketches, and five new private theorem items were published.

The goal's **one-form** decomposition imports
`ZetaNine.irrational_of_small_nonzero_integer_forms` (Proved) and
`ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` (Open). The criterion states
that a real number admitting nonzero integer forms of arbitrarily small absolute
value is irrational; the open child asks for a fixed $c>0$ with nonzero forms
$b+a\\,\\zeta(9)$ of absolute value below $e^{-cn}$ for all sufficiently large $n$.
The goal's **two-form** decomposition imports
`ZetaNine.irrational_of_two_small_integer_forms` (Proved, the mission's existing
criterion) and `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` (Open),
which additionally requires the two coefficient vectors to be non-proportional.

Both open children are strictly stronger than the goal and are **not** equivalent to
it: they demand approximations of a fixed exponential quality, which a general
irrational number need not admit. They are the definition-free packaging of the
local notes' combination of the open exponential margin J, the coefficient map F,
the analytic decay A and the Gauss lattice bound G, and proving either one settles
the goal. The Lean content of these two reductions is a short final assembly; the
mathematical work lives entirely in the open child, and neither child is claimed
proved. The one-form child carries an explicit nonvanishing clause; the two-form
child does not need one, because with two non-proportional coefficient vectors at
most one form can vanish.

Three further items are proved and fully general, and form the formalisable core of
local nodes TP and FQ. `ZetaNine.irrational_of_small_nonzero_integer_forms` is the
criterion half of TP. `ZetaNine.taylor_sign_implies_kernel_sum_pos` is the
positive-kernel half of TP: for a strictly positive kernel $R$, sampling map $u$,
polynomial $p$ and expansion point $u_0$, if every sample satisfies $u(k)\\ge u_0$,
every Taylor coefficient of $p$ at $u_0$ is nonnegative, the weighted series is
summable, and $p$ is positive at one sample, then the complete weighted sum is
strictly positive. `ZetaNine.quadrature_exact_of_moments` is the exact algebraic core
of FQ: agreement of a linear functional with a five-node rule on the moments of
degrees zero through four forces agreement on every polynomial of degree at most
four. None of the three mentions the concrete construction, and none of them
asserts positivity of the actual cubature weights or any infinite sign condition.

**What is deliberately not wired.** The concrete construction still has no Lean
definitions: there is no formal coefficient matrix $F_n$, saturated kernel, Smith
data, weighted area or congruence-lattice minimum. Consequently the local reductions
$V\\leftarrow VA,Q,X$, $VA\\leftarrow VB,Y$, $VA\\leftarrow VD,YD,H,Z,Y$,
$VB\\leftarrow VC,H,Z$, $T5\\leftarrow FD,FC$ and $J\\leftarrow V,S$ are **not** posted
as platform decompositions, and the milestones for X, VB, VC, VD, S, J, T, TG, TS,
T5, FD, FM and CP remain unlinked to theorem items. Two reasons, recorded so that
nobody re-derives them: a child of the goal stated only as "small integer forms
exist" is *equivalent* to the goal once a criterion is available, so it would be a
disguised restatement rather than a decomposition; and a reduction whose parent has
free parameters cannot import closed child theorems, so a genuine multi-level graph
over the concrete nodes needs the definition layer first. The arrow arguments
themselves are elementary once the objects exist. Until then the platform dependency
graph should be read as one open analytic obligation per route plus three proved
general lemmas, with the remaining milestones still at research-notebook status.

All five new statements were read back blind by an independent auditor before
publication. The goal theorem remains **Open**.
"""


def main() -> None:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if receipt.get("status") != "Private" or not receipt.get("mission_id"):
        raise RuntimeError("Expected the live private mission")
    token = get_token()
    listing = request("GET", "/missions?limit=100&offset=0", token)
    row = next((r for r in listing.get("missions", []) if r.get("id") == receipt["mission_id"]), None)
    if row is None:
        raise RuntimeError("Private mission not found in the live list")

    current = DESCRIPTION.read_text(encoding="utf-8")
    if MARKER in current:
        raise RuntimeError("Local description already carries the wiring section")
    if row.get("description") != current:
        raise RuntimeError("Live description differs from the local file; refusing to clobber")
    if "2609.22316" not in current.rstrip().splitlines()[-1]:
        raise RuntimeError("Unexpected tail of the local description; refusing to append")

    updated = current.rstrip("\n") + "\n" + SECTION
    DESCRIPTION.write_text(updated, encoding="utf-8")

    result = request("PATCH", f"/missions/{receipt['mission_id']}", token,
                     {"description": updated})
    if result.get("visibility") != "private":
        raise RuntimeError("Description update lost private visibility")
    check = request("GET", "/missions?limit=100&offset=0", token)
    live = next(r for r in check.get("missions", []) if r.get("id") == receipt["mission_id"])
    if live.get("description") != updated:
        raise RuntimeError("Live description read-back failed")
    print(f"Appended wiring section; live description now {len(updated)} chars")

    data = json.loads(RESULTS_RECEIPT.read_text(encoding="utf-8"))
    data["mission_description_sha256"] = hashlib.sha256(updated.encode("utf-8")).hexdigest()
    RESULTS_RECEIPT.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                               encoding="utf-8")
    print("Refreshed mission_description_sha256 in new-results-receipt.json")


if __name__ == "__main__":
    main()
