#!/usr/bin/env python3
"""Finite semantic checks for arXiv:2609.00240v1.

These checks are executable evidence, NOT proofs in Lean. By default all local
increasing activation families on cubes of dimension at most three are tested.
Empty-set activations are omitted because they never change the active union.
Closure is tested symbolically for every possible Boolean decoder at once:
OR/AND expressions are equal for all decoders iff their literal sets agree.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from time import perf_counter


def submasks(s: int):
    x = s
    while True:
        yield x
        if not x:
            break
        x = (x - 1) & s


def local_increasing_tables(n: int, s: int):
    domain = tuple(sorted(submasks(s)))
    for v in itertools.product((0, 1), repeat=len(domain)):
        lookup = dict(zip(domain, v))
        if all(lookup[x] <= lookup[x | (1 << i)]
               for x in domain for i in range(n) if s >> i & 1):
            yield tuple(lookup[x & s] for x in range(1 << n))


def atoms(active):
    return tuple((a, x & a) for x, a in enumerate(active))


def assert_constant_on_atoms(partition, expressions, context):
    values = {}
    for x, (a, e) in enumerate(zip(partition, expressions)):
        if a in values:
            assert values[a] == e, (context, x, a, values[a], e)
        else:
            values[a] = e


def check_activation_families(n: int):
    sets = tuple(range(1, 1 << n))
    choices = [tuple(local_increasing_tables(n, s)) for s in sets]
    families = 0
    recovery_cases = 0
    symbolic_shift_cases = 0
    for tables in itertools.product(*choices):
        family = dict(zip(sets, tables))
        active = tuple(
            sum(1 << i for i in range(n)
                if any(s >> i & 1 and table[x]
                       for s, table in family.items()))
            for x in range(1 << n))
        old = atoms(active)
        # Lemma 4.1's exact atom-preserving zeroing operation.
        for x in range(1 << n):
            assert old[x & active[x]] == old[x], (n, family, x, "zeroing")
        for i in range(n):
            bit = 1 << i
            forced = tuple((active[x | bit], x & active[x | bit])
                           for x in range(1 << n))
            upper_expr = []
            lower_expr = []
            for x in range(1 << n):
                lo, hi = x & ~bit, x | bit
                # A frozenset is a symbolic OR or symbolic AND of old-atom
                # labels. Repetitions disappear by Boolean idempotence.
                upper_expr.append(frozenset((old[x], old[lo]))
                                  if x & bit else frozenset((old[x],)))
                lower_expr.append(frozenset((old[x],))
                                  if x & bit else frozenset((old[lo], old[hi])))
                if x & bit:
                    # Appendix B R_i: reconstruct active lower sets using only
                    # the upper active union and the recorded true labels.
                    b, a = old[x]
                    lowered_labels = a & ~bit
                    recovered = 0
                    for s, table in family.items():
                        if s & ~b == 0 and table[lowered_labels]:
                            recovered |= s
                    assert (recovered, lowered_labels & recovered) == old[lo]
                    if not b & bit:
                        assert old[lo] == old[x]
                    recovery_cases += 1
                b, a = forced[x]
                assert (b, (a | bit) & b) == old[hi]  # Appendix B Q_i.
            assert_constant_on_atoms(old, upper_expr, (n, family, i, "upper"))
            assert_constant_on_atoms(forced, lower_expr, (n, family, i, "lower"))
            symbolic_shift_cases += 2
        families += 1
    return {"dimension": n, "activation_families": families,
            "atom_recovery_cases": recovery_cases,
            "universal_decoder_shift_checks": symbolic_shift_cases}


def increasing_in(v, i):
    bit = 1 << i
    return all(v[x] <= v[x | bit] for x in range(len(v)))


def shift(v, i, lower):
    bit = 1 << i
    return tuple((v[x & ~bit] & v[x | bit]) if lower and not x & bit
                 else (v[x & ~bit] | v[x | bit]) if not lower and x & bit
                 else v[x] for x in range(len(v)))


def check_shift_inequalities(n: int):
    cube = range(1 << n)
    functions = tuple(itertools.product((0, 1), repeat=1 << n))
    targets = tuple(v for v in functions if all(increasing_in(v, i) for i in range(n)))
    biases = (Fraction(1, 10), Fraction(1, 2), Fraction(9, 10))
    tests = 0
    for p in biases:
        weights = tuple(p ** x.bit_count() * (1 - p) ** (n - x.bit_count()) for x in cube)
        def error(f, v):
            return sum(weights[x] for x in cube if f[x] != v[x])
        for v in functions:
            for i in range(n):
                u, l = shift(v, i, False), shift(v, i, True)
                assert increasing_in(u, i) and increasing_in(l, i)
                for j in range(n):
                    if increasing_in(v, j):
                        assert increasing_in(u, j) and increasing_in(l, j)
                for f in targets:
                    assert (1 - p) * error(f, u) + p * error(f, l) <= error(f, v)
                    tests += 1
    return {"dimension": n, "functions": len(functions),
            "increasing_targets": len(targets), "exact_error_inequalities": tests}


def check_forcing_distribution(n: int):
    cases = 0
    for p in (Fraction(1, 10), Fraction(1, 2), Fraction(9, 10)):
        q = 2 * p - p * p
        w = tuple(p ** x.bit_count() * (1 - p) ** (n - x.bit_count())
                  for x in range(1 << n))
        for z in range(1 << n):
            probability = sum(w[x] * w[d] for x in range(1 << n)
                              for d in range(1 << n) if x | d == z)
            target = q ** z.bit_count() * (1 - q) ** (n - z.bit_count())
            assert probability == target
            assert target <= (2 - p) ** n * w[z]
            cases += 1
    return {"dimension": n, "exact_mass_and_ratio_checks": cases}


def obstruction_b1():
    # Coordinates are bits (b, a1, a2).
    target = tuple(int(bool(x & 6)) for x in range(8))
    h = tuple(target[x] if x & 1 else 1 for x in range(8))
    assert shift(h, 0, True) == target
    assert sum(a != b for a, b in zip(target, h)) == 1
    best_increasing_decoder_errors = 8
    old = tuple((7, x) if x & 1 else (0, 0) for x in range(8))
    for v in itertools.product((0, 1), repeat=8):
        if not all(increasing_in(v, i) for i in range(3)):
            continue
        if len({v[x] for x in range(8) if not x & 1}) != 1:
            continue
        best_increasing_decoder_errors = min(best_increasing_decoder_errors,
                                             sum(a != b for a, b in zip(target, v)))
    assert best_increasing_decoder_errors == 2
    assert old[0] == old[2] and target[0] != target[2]
    return {"old_decoder_error": "1/8", "best_increasing_old_decoder_error": "1/4",
            "lower_shift_equals_target": True}


def hatami_coefficient_warning():
    """Exact counterexample to an auxiliary bound in the cited Hatami proof.

    This does NOT refute Hatami's theorem or the target paper's Lemma 2.1.
    For XOR_2 the coefficient is -2p(1-p); the claimed bound is p.
    """
    p = Fraction(1, 10)
    coefficient_abs = 2 * p * (1 - p)
    assert coefficient_abs == Fraction(9, 50)
    assert coefficient_abs > p
    return {"source": "Hatami 2012, Annals p.517 (external dependency)",
            "function": "XOR of two bits", "bias": str(p),
            "coefficient_abs": str(coefficient_abs), "claimed_upper_bound": str(p),
            "conclusion": "auxiliary coefficient bound false; theorem not refuted"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-dimension", type=int, choices=(1, 2, 3), default=3)
    args = parser.parse_args()
    start = perf_counter()
    results = {"status": "PASS", "scope": "finite semantic checks, not a proof",
               "activation_checks": [], "shift_checks": [], "forcing_checks": []}
    for n in range(1, args.max_dimension + 1):
        results["activation_checks"].append(check_activation_families(n))
        results["shift_checks"].append(check_shift_inequalities(n))
        results["forcing_checks"].append(check_forcing_distribution(n))
    results["appendix_b1"] = obstruction_b1()
    results["external_dependency_warning"] = hatami_coefficient_warning()
    results["elapsed_seconds"] = round(perf_counter() - start, 3)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
