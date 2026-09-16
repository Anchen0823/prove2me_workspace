#!/usr/bin/env python
"""Assemble the /submit-problem payload for the WeakGoldbach sieve-coverage child."""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MDIR = os.path.join(ROOT, "missions", "weak-goldbach")


def read(name):
    with open(os.path.join(MDIR, name), "r", encoding="utf-8") as fh:
        return fh.read().strip()


def main():
    formal = read("child_formal_statement.lean")
    nl = read("child_nl.md")
    payload = {
        "problems": [
            {
                "theorem_name": "WeakGoldbach.verified_range_sieve_coverage",
                "theorem_title": "Finite sieve coverage of the binary Goldbach range "
                                 "$(4\\cdot 10^{14},\\,4\\cdot 10^{18}]$ in blocks of one million",
                "formal_statement": formal,
                "natural_language_statement": nl,
                "preamble": "import Definitions.Def_GoldbachSieve\n"
                            "import Mathlib.Algebra.Ring.Parity\n\n"
                            "set_option autoImplicit false",
                "source": (
                    "T. Oliveira e Silva, S. Herzog, S. Pardi, Empirical verification of the "
                    "even Goldbach conjecture and computation of prime gaps up to 4\u00b710^18, "
                    "Math. Comp. 83 (2014), no. 288, 2033-2060, "
                    "https://doi.org/10.1090/S0025-5718-2013-02787-1, \u00a71.1-\u00a71.4 "
                    "(cache-efficient segmented sieve of Eratosthenes; minimal-partition marking) "
                    "and \u00a72 (records of the smallest prime of a minimal Goldbach partition); the "
                    "largest such smaller prime below 4\u00b710^18, namely 9781 at "
                    "n = 3,325,581,707,333,960,528, is recorded in OEIS A025019 / A025018 and "
                    "tabulated at https://sweet.ua.pt/tos/goldbach.html . The certificate interface "
                    "`GoldbachSieve.pairSums` reuses J. Richstein, Verifying the Goldbach conjecture "
                    "up to 4\u00b710^14, Math. Comp. 70 (2001), 1745-1749, "
                    "https://doi.org/10.1090/S0025-5718-00-01290-4 , whose block width and "
                    "small-prime bound are likewise formalization choices."
                ),
                "tags": ["goldbach", "number-theory", "primes", "computational-number-theory"],
            }
        ]
    }
    out = os.path.join(MDIR, "child_payload.json")
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, ensure_ascii=False)
    print("wrote", out)


if __name__ == "__main__":
    main()
