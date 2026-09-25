"""Publish and prove faithful abstract cores of new private zeta(9) DAG results.

Concrete zeta-specific Q, X, and Y are not implied by these abstract Lean
statements. The full research DAG and exact scope are in mission-description.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from submit_solved_milestones import post_multipart
from sync_private_proposal import HERE, RECEIPT, get_token, request


OUT = HERE / "new-results-receipt.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TARGETS = {
    "Z9.Q.ABSTRACT": {
        "name": "ZetaNine.volume_baseline_cancellation",
        "title": "Logarithmic Smith-volume cancellation",
        "draft": "VolumeCancellation.lean",
        "statement": "VolumeCancellation-statement.md",
        "solution": "Sol_ZetaNine_volume_baseline_cancellation.lean",
        "explanation": "VolumeCancellation-explanation.md",
        "source": "Local zeta9 research note, roadmap/research/volume-cancellation.md, equations (1)-(2), 2026-09-24",
    },
    "Z9.Y.ABSTRACT": {
        "name": "ZetaNine.finite_prime_budget",
        "title": "Finite weighted prime-budget inequality",
        "draft": "PrimeBudgetInequality.lean",
        "statement": "PrimeBudget-statement.md",
        "solution": "Sol_ZetaNine_finite_prime_budget.lean",
        "explanation": "PrimeBudget-explanation.md",
        "source": "Local zeta9 research note, roadmap/research/arithmetic-prime-budget.md, equations (1)-(2), 2026-09-24",
    },
    "Z9.YD.ABSTRACT": {
        "name": "ZetaNine.finite_prime_discount",
        "title": "Exact finite weighted prime-discount identity",
        "draft": "PrimeDiscountIdentity.lean",
        "statement": "PrimeDiscount-statement.md",
        "solution": "Sol_ZetaNine_finite_prime_discount.lean",
        "explanation": "PrimeDiscount-explanation.md",
        "source": "Local zeta9 research note, roadmap/research/prime-discount-identity.md, equations (2)-(3), 2026-09-24",
    },
}


def saved() -> dict[str, Any]:
    if OUT.exists():
        result = json.loads(OUT.read_text(encoding="utf-8"))
        if result.get("schema") != "zeta9-private-new-results-v1":
            raise ValueError("Unexpected result receipt schema")
        return result
    return {"schema": "zeta9-private-new-results-v1", "results": {},
            "mission_milestones": {}}


def save(data: dict[str, Any]) -> None:
    OUT.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def mission() -> dict[str, Any]:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if (receipt.get("status") != "Private" or receipt.get("visibility") != "private" or
            not receipt.get("mission_id")):
        raise RuntimeError("Expected the existing live private mission")
    return receipt


def body(item: dict[str, str]) -> dict[str, Any]:
    code = (HERE / item["draft"]).read_text(encoding="utf-8")
    prefix, tail = code.split("namespace ZetaNine", 1)
    formal = "namespace ZetaNine" + tail
    short_name = item["name"].split(".")[-1]
    if (formal.count(f"theorem {short_name}") != 1 or
            formal.count(":= by sorry") != 1 or
            not formal.rstrip().endswith("end ZetaNine")):
        raise ValueError(f"Malformed theorem draft: {item['draft']}")
    return {
        "theorem_name": item["name"],
        "theorem_title": item["title"],
        "formal_statement": formal.strip(),
        "natural_language_statement": (HERE / item["statement"]).read_text(encoding="utf-8").strip(),
        "preamble": prefix.strip(),
        "source": item["source"],
        "private": True,
        "env": ENV,
    }


def publish() -> None:
    mission()
    token = get_token()
    data = saved()
    for local_id, item in TARGETS.items():
        if data["results"].get(local_id, {}).get("job_id"):
            print(f"Already queued {local_id}")
            continue
        result = request("POST", "/submit-problem", token, body(item))
        jobs = result.get("jobs", [])
        if len(jobs) != 1 or jobs[0].get("name") != item["name"] or result.get("errors"):
            raise RuntimeError(f"Unexpected publish response for {local_id}: {result}")
        data["results"][local_id] = {"job_id": jobs[0]["job_id"],
                                     "name": item["name"], "job_status": "PENDING"}
        save(data)
        print(f"Queued private theorem {local_id}: {jobs[0]['job_id']}")


def poll_jobs() -> None:
    token = get_token()
    data = saved()
    for local_id, entry in data["results"].items():
        result = request("GET", f"/publish-jobs/{entry['job_id']}", token)
        if result.get("theorem_name") != entry["name"]:
            raise RuntimeError(f"Publish job mismatch: {local_id}")
        entry["job_status"] = result.get("status")
        entry["publish_error"] = result.get("error_message")
        if entry["job_status"] == "PUBLISHED":
            if result.get("visibility") != "private" or not result.get("theorem_id"):
                raise RuntimeError(f"Theorem was not published privately: {local_id}")
            entry["theorem_id"] = result["theorem_id"]
        print(f"{local_id} publish: {entry['job_status']}")
    save(data)


def assert_solution_matches(item: dict[str, str], theorem: dict[str, Any], source: str) -> None:
    if (theorem.get("theorem_name") != item["name"] or
            theorem.get("mathlib_rev") != ENV or theorem.get("visibility") != "private"):
        raise RuntimeError(f"Private theorem metadata mismatch: {item['name']}")
    short_name = item["name"].split(".")[-1]
    formal = theorem["formal_statement"]
    target_sig = formal.split(f"theorem {short_name}", 1)[1].split(":= by sorry", 1)[0]
    solution_sig = source.split("theorem solution", 1)[1].split(":= by", 1)[0]
    if source.count("theorem solution") != 1 or "sorry" in source or target_sig != solution_sig:
        raise RuntimeError(f"Solution signature or placeholder mismatch: {item['name']}")


def prove() -> None:
    mission()
    token = get_token()
    data = saved()
    for local_id, item in TARGETS.items():
        entry = data["results"].get(local_id, {})
        if entry.get("submission_id"):
            print(f"Already submitted proof for {local_id}")
            continue
        if entry.get("job_status") != "PUBLISHED" or not entry.get("theorem_id"):
            raise RuntimeError(f"Theorem not yet published: {local_id}")
        theorem = request("GET", f"/theorems/{entry['theorem_id']}", token)
        if theorem.get("status") != "Open":
            raise RuntimeError(f"Theorem not Open: {local_id}")
        solution_path = HERE / "solutions" / item["solution"]
        source = solution_path.read_text(encoding="utf-8")
        assert_solution_matches(item, theorem, source)
        explanation = (HERE / "solutions" / item["explanation"]).read_text(encoding="utf-8")
        result = post_multipart(token, entry["theorem_id"], solution_path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission ID for {local_id}: {result}")
        entry["submission_id"] = result["submission_id"]
        entry["proof_status"] = result.get("status")
        entry["solution_sha256"] = hashlib.sha256(solution_path.read_bytes()).hexdigest()
        save(data)
        print(f"Submitted proof {local_id}: {entry['submission_id']}")


def poll_proofs() -> None:
    token = get_token()
    data = saved()
    for local_id, entry in data["results"].items():
        if not entry.get("submission_id"):
            continue
        result = request("GET", f"/verify?submission_id={entry['submission_id']}", token)
        if result.get("theorem_id") != entry["theorem_id"]:
            raise RuntimeError(f"Proof target mismatch: {local_id}")
        entry["proof_status"] = result.get("status")
        entry["proof_error"] = result.get("error_message")
        print(f"{local_id} proof: {entry['proof_status']}")
    save(data)


MILESTONES = (
    ("Q1. Concrete Smith area identity",
     "For each even n>=2 in the p=9, m=n construction, prove the exact weighted area identity Delta_n=(s1_n^2 N_n/D_n^2) Xi_n, where Xi_n is the weighted area of E_n=S F_n^(-1). This concrete identity remains a formalization target; it is proved in the local mathematical note.", None),
    ("Q2. Logarithmic volume cancellation",
     "Assuming positive real D,s,N,g,Xi and Delta=(s^2 N/D^2)Xi, prove log(D/s)+(1/2)log Delta-(1/2)log g=(log Xi+log(N/g))/2. This is only the abstract algebraic core of local node Q.", "Z9.Q.ABSTRACT"),
    ("X. Inverse-image area exponent",
     "For the concrete weighted inverse-image rows E_n W_n and the proved n-to-n+2 connection, establish limsup_{even n} log Xi_n/(2n) < (1/4)log(3711015000). A local mathematical proof uses exterior-square block growth and sharper exact rational root isolation; faithful Lean definitions and proof remain to be supplied.", None),
    ("Y1. Finite weighted prime budget",
     "For finite indices i, nonnegative integer valuations v_i,a_i, and nonnegative weights w_i, prove sum (v_i-2a_i)_+ w_i <= 9 sum a_i w_i + sum (v_i-11a_i)_+ w_i. This is the formalizable finite core of local node Y.", "Z9.Y.ABSTRACT"),
    ("VB. Uniform excess-prime budget",
     "With E_n=sum_{p<=n}(v_p(N_n)-11 floor(log_p n))_+ log p and H_n=sum_{p>n}v_p(N_n)log p, prove limsup_{even n}(E_n+H_n)/n < 2(10.564)-(1/2)log(3711015000)-9. This strictly open arithmetic bound would imply VA, then V using Q and X.", None),
    ("H. Translation-trace large-prime window",
     "For every even n>=8 and prime p>n in the concrete construction, prove v_p(N_n)<=floor(3n/(2p)). This implies H_n<=theta(3n/2)-theta(n) and limsup H_n/n<=1/2. The local mathematical proof uses finite-field translation trace and minor-gcd cancellation; a faithful Lean theorem is still needed.", None),
    ("Z. Sublinear small-prime excess",
     "For even n>=4, prove the contribution of primes p<=sqrt(7n/2) to E_n is at most 42 floor(sqrt(7n/2)) log(7n/2), hence o(n). The local mathematical proof uses the existing uniform valuation bound; a faithful Lean theorem is still needed.", None),
    ("VC. Intermediate-prime excess budget",
     "For E_mid(n)=sum_{sqrt(7n/2)<p<=n}(v_p(N_n)-11)_+ log p, prove limsup_{even n} E_mid(n)/n < 2(10.564)-(1/2)log(3711015000)-9-1/2. This remains open; H and Z would then imply VB.", None),
    ("I. Merged-pole intermediate-prime bound",
     "For each even n>=2 and prime sqrt(7n/2)<p<=n in the concrete construction, prove the merged-pole CRT and normalized trace lemmas in their stated range and the uniform bound v_p(N_n)<=30+D_np-5h_np<=38, where h_np=1 if 3(n mod p)>=2p-1 and 0 otherwise. These are proved in a local mathematical note, but faithful Lean definitions and proofs are still needed; the result alone does not prove VC.", None),
    ("LC. Intrinsic local congruence slope",
     "For each even n>=2 and g|N_n, prove with M_n=J_n/s1_n that Lambda_g={zK_n:zM_n=0 mod g}, that a primitive z has multiplier g/gcd(g,content(zM_n)), and that each p-power condition is one dot product against a p-unit column of M_n. The local mathematical proof is Smith-choice independent; faithful Lean formalization remains open.", None),
    ("S. Uniform congruence shape",
     "Prove sigma_n->0 along all even n for g_n=gcd(N_n,d_n^2) by excluding every primitive direction that is exponentially shorter than sqrt(g_n Delta_n) after its exact congruence multiplier. This remains open.", None),
    ("J. Infinite exponential margin",
     "Prove that some epsilon>0 and infinitely many even n satisfy B_n+sigma_n<=10.564-epsilon. The stronger V and S together suffice, but failure of either does not refute this node. This remains open.", None),
    ("YD. Exact finite prime discount",
     "For arbitrary finite natural valuations v_i,a_i and real weights w_i, prove the exact identity sum_i (v_i-2a_i)_+ w_i + sum_i min((11a_i-v_i)_+,9a_i) w_i = 9 sum_i a_i w_i + sum_i (v_i-11a_i)_+ w_i. The linked Lean proof covers this abstract finite identity only; the concrete zeta(9) substitution is local mathematical work.", "Z9.YD.ABSTRACT"),
    ("VD. Discounted intermediate-prime budget",
     "With U_n=sum_{p<=n} min((11 floor(log_p n)-v_p(N_n))_+,9 floor(log_p n)) log p, prove limsup_{even n}(E_mid(n)-U_n)/n < 2(10.564)-(1/2)log(3711015000)-9-1/2. This weaker-than-VC weighted target remains open.", None),
    ("TP. Positive one-form bridge",
     "Formalize the concrete positive-kernel criterion: an integer-output polynomial with one weak sign in all five Taylor coefficients at u0=(n+1)(2n+1) has a strictly nonzero sum, and an infinite exponentially short sequence of such forms implies zeta(9) irrational. The local mathematical proof and exact partial-lattice lift are available; faithful Lean definitions remain open.", None),
    ("T. Full-lattice first-direction positivity",
     "Prove that infinitely many even n have a first-minimum vector of the full integer-output lattice whose five Taylor coefficients at u0 have one weak sign. Together with the local inverse-image area theorem and TP this would prove the root. This infinite sign assertion is open.", None),
    ("TG. Partial-lattice first-direction positivity",
     "Prove that infinitely many even n have a first-minimum vector of Lambda_{g_n} whose five Taylor coefficients at u0 have one weak sign. Its integer-output lift has exact norm exponent B_n-sigma_n, so together with V and TP this would prove the root without S. This infinite sign assertion is open.", None),
    ("TA. Eventual two-step Taylor positivity",
     "For the concrete normalized Taylor connection H_n, prove H_n H_(n+2) is strictly entrywise positive for every sufficiently large even n. Deduce that every fixed real output (b,a) with b+a zeta(9) nonzero has all five Taylor coefficients eventually of that sign. The two coordinate ratio windows strictly nest modulo four, and their width has limsup logarithmic rate below -10.1109 per n. Local mathematical proofs and exact rational matrix audits exist; no faithful Lean theorem is linked.", None),
    ("SP. Signed-saddle nonvanishing lemma",
     "For every predetermined positive window h_n tending to zero with n h_n^2/log n tending to infinity, all sufficiently large even n, and every nonzero real quartic q, prove that one weak sign at every positive-kernel sample with |k/n-x_*|<=h_n forces the entire infinite weighted sum to be strictly nonzero with that sign. In particular h_n=A log n/sqrt(n) works for every fixed A>0. The local proof controls five central samples and the complete infinite tail; faithful Lean formalization remains open.", None),
    ("TS. Infinite saddle-signed short direction",
     "Prove that for some fixed A>0 and infinitely many sufficiently large even n, a shortest vector of the full integer-output lattice has one weak sign at all samples in |k/n-x_*|<=A log n/sqrt(n). Together with SP, the inverse-image area bound X, and analytic decay, this would prove zeta(9) irrational. This moving-vector infinite sign assertion remains open.", None),
    ("GC. Gaussian saddle moments and sharp constant window",
     "For the actual infinite positive kernel, prove that the normalized moments of the affine-in-y saddle coordinate through degree four converge to (1,0,1,0,3). Deduce that for every fixed A>sqrt(3/a), all sufficiently large even n and every nonzero moving real quartic with one weak sign at all samples |k/n-x_*|<=A/sqrt(n) have a strictly same-sign complete sum; for each smaller A, exhibit moving rational quartic counterexamples on the same kernel. Here a=-f''(x_*) and 0.095251<sqrt(3/a)<0.095252. This is proved in local mathematical notes, not in Lean; equality is not asserted.", None),
    ("FQ. Exact positive five-sample cubature",
     "For all sufficiently large even n, choose actual integers k_(n,j)=floor(n x_*+j sqrt(n/a)+1/2), j=-2,...,2. Prove the actual infinite positive-kernel sum of every real quartic in y=k(k+n)/n^2 equals Z_n times a strictly positive exact weighted sum at these five samples, with weights independent of the quartic and tending to (1/12,1/6,1/2,1/6,1/12). Weak agreement of the five signs then forces strict nonvanishing. The local mathematical proof uses true Gaussian moments and a finite Vandermonde inverse; no faithful Lean theorem is yet linked.", None),
    ("T5. Infinite five-sample-signed short direction",
     "Prove that for infinitely many sufficiently large even n, a shortest vector of the full integer-output lattice has one weak sign at the five predetermined actual sample integers k_(n,j), j=-2,...,2. The note-proved exact positive cubature FQ, inverse-image area bound X, and analytic decay would then prove zeta(9) irrational. This moving-lattice infinite sign assertion remains open; an abstract two-dimensional lattice counterexample shows area and shortness alone do not imply it.", None),
    ("GO. Geometry-only five-sample obstruction",
     "For every sufficiently large even n, construct an abstract rank-two integer polynomial lattice for which every nonzero vector has both signs among the three prescribed samples j=-2,0,2, while its weighted first-minimum logarithmic rate and weighted-area logarithmic half-rate can both equal 5. The local note proves this and shows that rank, area and shortness bounds alone do not imply T5. This is not a counterexample for the actual E_n output lattice; no faithful Lean theorem is linked.", None),
    ("FI. Strict five-sample ratio interval",
     "For every sufficiently large even n, prove that the rational ratios of the two concrete coordinate polynomials at the five prescribed samples form a nondegenerate interval ell_n<zeta(9)<h_n, strictly inside the Taylor coefficient ratio interval, with limsup logarithmic width rate below -10.1109. Prove that a nonzero integer output (b,a) has weak agreement of the five signs exactly when a=0 or -b/a lies outside the open interval (ell_n,h_n); endpoints are allowed. The local mathematical proof uses TA and FQ; it does not prove the open infinite shortest-vector condition T5, and no faithful Lean theorem is linked.", None),
    ("FO. Uniform approximation by every first output",
     "For the actual full integer-output lattice and delta=(1/4)log(lambda1/|lambda2|)>5.05545, prove that for every epsilon in (0,delta), all sufficiently large even n and every first output (b,a), a!=0 and |b+a zeta(9)|<=exp(-(delta-epsilon)n). Under rationality zeta(9)=c/d, all late first outputs must equal +/−(-c,d). A local mathematical proof uses positive moments and Hermite; T5 remains open and no faithful Lean theorem is linked.", None),
    ("FC. Exact five-endpoint denominator and gap",
     "For the actual five sample integers and Ctilde=S adj(d_n^9 F_n)/delta4star_n, prove each reduced sample-ratio denominator equals |Ctilde_B v(t)|/gcd(|Ctilde_B v(t)|,|Ctilde_A v(t)|). If an integer slope lies inside the strict five-point interval, prove |a|(h_n-ell_n)>1/min(Q_-,Q_+); bound first-output |a| by lambda1||E_B W_n||/Xi_n. This local mathematical proof yields FD+FC=>T5 but no uniform FD estimate; no faithful Lean theorem is linked.", None),
    ("FD. Infinite endpoint-denominator height criterion",
     "Prove for infinitely many sufficiently large even n that [lambda1||E_B W_n||/Xi_n](h_n-ell_n)min(Q_-,Q_+)<=1 for the actual five-sample reduced endpoint denominators. Together with FC, this forces every first output outside the open ratio interval and implies T5. The infinite arithmetic estimate remains open; finite samples do not establish it.", None),
    ("FM. Same-limit rational connection obstruction",
     "Construct a rational full-rank alternative connection retaining the actual five prescribed nodes, positive exact cubature, positive two-step limiting transfer, the same limiting spectrum, and the inverse-area upper exponent, but whose eventual first integer outputs are a rational zero relation and mixed-sign at the five samples. The local mathematical proof bounds what structural arguments alone can show. It does not preserve the actual finite-parameter connection C(n) and is not a counterexample to T5; no faithful Lean theorem is linked.", None),
    ("XL. Actual inverse-area lower and height upper rates",
     "For the actual changing connection, prove the B-coordinate weighted row norm exponent (1/2)log A, the area lower rate liminf log Xi_n/(2n)>=(1/4)log(A|lambda5|)>(1/4)log(1499/10), and the upper first-output height rate (1/4)log(A/|lambda5|). The sharper second-mode lower growth is still open. A local mathematical proof uses positive moment angle and inverse-block growth; no faithful Lean theorem is linked.", None),
    ("CM. Critical second-minimum equivalence",
     "For the actual positive kernel, prove Z_n~C_Z n^-5 exp(f_*n), both fixed output rows have norm Theta(n^5 exp(-f_*n)), and zeta(9) irrational iff lambda2_n=o(n^5 exp(-f_*n)) iff liminf lambda2_n Z_n=0. Under rationality the late first direction is the zero relation and lambda1_n lambda2_n/Xi_n tends to one. This equivalence is proved in a local mathematical note; it does not prove the still-open CP estimate or the root, and no faithful Lean theorem is linked.", None),
    ("CP. Critical second-minimum polynomial margin",
     "Prove liminf along even n of lambda2_n Z_n=0, equivalently liminf lambda2_n/(n^5 exp(-f_*n))=0, for the actual full integer-output lattice. The note-proved CM equivalence would then imply zeta(9) irrational. This critical lattice estimate remains open and cannot be inferred from the current area spectral upper bound alone.", None),
)

PRIOR_MILESTONE_DESCRIPTIONS = {
    "X. Inverse-image area exponent":
        "For the concrete weighted inverse-image rows E_n W_n and the proved n-to-n+2 connection, establish limsup_{even n} log Xi_n/(2n) < (1/4)log(3750000000). A local mathematical proof uses exterior-square block growth and exact rational root isolation; faithful Lean definitions and proof remain to be supplied.",
    "VB. Uniform excess-prime budget":
        "With E_n=sum_{p<=n}(v_p(N_n)-11 floor(log_p n))_+ log p and H_n=sum_{p>n}v_p(N_n)log p, prove limsup_{even n}(E_n+H_n)/n < 2(10.564)-(1/2)log(3750000000)-9. This strictly open arithmetic bound would imply VA, then V using Q and X.",
    "TA. Eventual two-step Taylor positivity":
        "For the concrete normalized Taylor connection H_n, prove H_n H_(n+2) is strictly entrywise positive for every sufficiently large even n. Deduce that every fixed real output (b,a) with b+a zeta(9) nonzero has all five Taylor coefficients eventually of that sign, and that the two coordinate ratio windows strictly nest modulo four and contract exponentially to zeta(9). A local mathematical proof and exact rational matrix audit exist; no faithful Lean theorem is linked.",
    "SP. Signed-saddle nonvanishing lemma":
        "For every fixed A>0, all sufficiently large even n, and every nonzero real quartic q, prove that one weak sign at every positive-kernel sample with |k/n-x_*|<=A n^(-1/3) forces the entire infinite weighted sum to be strictly nonzero with that sign. The local proof controls the central five samples and the complete infinite tail; faithful Lean formalization remains open.",
    "TS. Infinite saddle-signed short direction":
        "Prove that for some fixed A>0 and infinitely many sufficiently large even n, a shortest vector of the full integer-output lattice has one weak sign at all samples in |k/n-x_*|<=A n^(-1/3). Together with SP, the inverse-image area bound X, and analytic decay, this would prove zeta(9) irrational. This moving-vector infinite sign assertion remains open.",
}

MILESTONE_UPDATE_REASONS = {
    "TA. Eventual two-step Taylor positivity": "Added a proved exterior-square/Perron bound for the concrete Taylor ratio-window exponent.",
    "SP. Signed-saddle nonvanishing lemma": "The same proved saddle argument applies to every window with n h_n^2/log n tending to infinity.",
    "TS. Infinite saddle-signed short direction": "The proved narrower-window lemma weakens the still-open infinite sign target.",
}


def sync_mission() -> None:
    receipt = mission()
    token = get_token()
    data = saved()
    for local_id in TARGETS:
        entry = data["results"].get(local_id, {})
        if entry.get("proof_status") != "ACCEPTED":
            raise RuntimeError(f"New abstract theorem is not accepted: {local_id}")
        theorem = request("GET", f"/theorems/{entry['theorem_id']}", token)
        if theorem.get("status") != "Proved" or theorem.get("visibility") != "private":
            raise RuntimeError(f"New theorem not private and Proved: {local_id}")

    def live_mission() -> dict[str, Any]:
        offset = 0
        while True:
            listing = request("GET", f"/missions?limit=100&offset={offset}", token)
            for row in listing.get("missions", []):
                if row.get("id") == receipt["mission_id"]:
                    if row.get("visibility") != "private":
                        raise RuntimeError("The mission is no longer private")
                    return row
            offset += len(listing.get("missions", []))
            if offset >= listing.get("total", 0):
                raise RuntimeError("Private mission not found in the live list")

    wanted_description = (HERE / "mission-description.md").read_text(encoding="utf-8")
    current_description = live_mission().get("description", "")
    current_hash = hashlib.sha256(current_description.encode("utf-8")).hexdigest()
    if current_description != wanted_description:
        if current_hash != data.get("mission_description_sha256"):
            raise RuntimeError("Mission description changed remotely since the local read-back")
        result = request("PATCH", f"/missions/{receipt['mission_id']}", token,
                         {"description": wanted_description})
        if result.get("visibility") != "private":
            raise RuntimeError("Mission description update lost private visibility")
        if live_mission().get("description") != wanted_description:
            raise RuntimeError("Live mission description read-back failed")
        print("Updated private mission research DAG description")

    current = request("GET", f"/missions/{receipt['mission_id']}/milestones?limit=100&offset=0", token)
    existing = {row["title"]: row for row in current.get("milestones", [])}
    for title, description, linked_id in MILESTONES:
        theorem_id = data["results"][linked_id]["theorem_id"] if linked_id else None
        if title in existing:
            row = existing[title]
            actual_id = (row.get("theorem") or {}).get("id")
            if actual_id != theorem_id:
                raise RuntimeError(f"Existing milestone theorem differs from reviewed target: {title}")
            if row.get("milestone_description") != description:
                if row.get("milestone_description") != PRIOR_MILESTONE_DESCRIPTIONS.get(title):
                    raise RuntimeError(f"Existing milestone differs from reviewed target: {title}")
                row = request("PATCH", f"/milestones/{row['id']}", token, {
                    "milestone_description": description,
                    "reason": MILESTONE_UPDATE_REASONS.get(title, "Sharpened the local spectral root interval; the theorem remains an open formalization target."),
                })
                if row.get("milestone_description") != description:
                    raise RuntimeError(f"Milestone update read-back failed: {title}")
                print(f"Updated private mission milestone {title}")
            data["mission_milestones"][title] = row["id"]
            continue
        payload = {"title": title, "milestone_description": description}
        if theorem_id:
            payload["theorem_id"] = theorem_id
        row = request("POST", f"/missions/{receipt['mission_id']}/milestones", token, payload)
        if row.get("title") != title:
            raise RuntimeError(f"Milestone read-back mismatch: {title}")
        data["mission_milestones"][title] = row["id"]
        save(data)
        print(f"Added private mission milestone {title}")

    check = request("GET", f"/missions/{receipt['mission_id']}/milestones?limit=100&offset=0", token)
    got = {row["title"]: row for row in check.get("milestones", [])}
    for title, description, linked_id in MILESTONES:
        row = got[title]
        theorem_id = data["results"][linked_id]["theorem_id"] if linked_id else None
        if (row.get("milestone_description") != description or
                (row.get("theorem") or {}).get("id") != theorem_id):
            raise RuntimeError(f"Post-write milestone read-back failed: {title}")
    root_id = receipt["local_theorem_ids"]["Z9.R"]
    root = request("GET", f"/theorems/{root_id}", token)
    if (root.get("theorem_id") != root_id or root.get("status") != "Open" or
            root.get("visibility") != "private"):
        raise RuntimeError("Root theorem read-back mismatch: " +
                           repr({key: root.get(key) for key in
                                 ("id", "theorem_id", "theorem_name", "status", "visibility")}))
    data["mission_description_sha256"] = hashlib.sha256(wanted_description.encode("utf-8")).hexdigest()
    save(data)
    print(f"Verified {len(MILESTONES)} new private mission milestones; root Open/private")


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    for name in ("publish", "poll-jobs", "prove", "poll-proofs", "sync-mission"):
        modes.add_argument("--" + name, action="store_true")
    args = parser.parse_args()
    if args.publish:
        publish()
    elif args.poll_jobs:
        poll_jobs()
    elif args.prove:
        prove()
    elif args.poll_proofs:
        poll_proofs()
    else:
        sync_mission()


if __name__ == "__main__":
    main()
