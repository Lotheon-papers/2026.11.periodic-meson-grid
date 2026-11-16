"""Independent audit checks; standard library only, deterministic seed.

Run alongside Calculs.py. Monte Carlo and sampled sensitivity checks are
diagnostics, not proofs of calibration or of a global minimum.
"""

from contextlib import redirect_stdout
from csv import DictReader
from fractions import Fraction
from io import StringIO
from itertools import product
from math import sqrt
from pathlib import Path
from random import Random

import Calculs as exact


DIRECTORY = Path(__file__).resolve().parent
TRIALS = 200_000
SEED = 20261115


def direct_distance(value):
    """Nearest integer grid point; independent of the modulo implementation."""
    return abs(value - 70 * round(value / 70))


def check_estimate(name, hits, expected):
    expected = float(expected)
    estimate = hits / TRIALS
    standard_error = sqrt(expected * (1 - expected) / TRIALS)
    assert abs(estimate - expected) < 6 * standard_error, name
    print(f"{name}: MC={estimate:.6f}, exact={expected:.12f}, "
          f"SE={standard_error:.6f}")


def check_density(a, e):
    jumps = exact.density_jumps(a, e)
    # Integrate the step function exactly over its entire support.
    assert sum(weight for _, weight in jumps) == 0
    assert -sum(knot * weight for knot, weight in jumps) == e - a
    # Count preimages directly, without splitting the mass interval into branches.
    for j in range(1, 70):
        z = Fraction(j, 2)
        if any(z == knot for knot, _ in jumps):
            continue
        count = sum(a < 70 * k + sign * z < e
                    for k in range(-1, 29) for sign in (-1, 1))
        assert count == sum(weight for knot, weight in jumps if knot < z)


def quantile(count, level, a, e):
    low, high = Fraction(0), Fraction(35 * count)
    for _ in range(45):
        middle = (low + high) / 2
        if exact.probability(count, middle, a, e) < level:
            low = middle
        else:
            high = middle
    return (low + high) / 2


def main():
    with (DIRECTORY / "Masses.csv").open(encoding="utf-8") as stream:
        data = list(DictReader(stream))
    bands = [(Fraction(row["borne_inferieure_MeV_c2"]),
              Fraction(row["borne_superieure_MeV_c2"])) for row in data]
    nominal = tuple(Fraction(row["nominale_MeV_c2"]) for row in data)
    assert all(low <= value <= high
               for value, (low, high) in zip(nominal, bands))
    assert all(left[1] < right[0] for left, right in zip(bands, bands[1:]))

    captured = StringIO()
    with redirect_stdout(captured):
        exact.main()
    assert captured.getvalue() == (DIRECTORY / "resultats.txt").read_text(encoding="utf-8")
    print("Exact output agrees with resultats.txt.")

    rng = Random(SEED)
    witness = (bands[0][1], bands[1][1], bands[2][1], Fraction(1260), bands[4][1])
    root = (exact.ROOT_LO + exact.ROOT_HI) / 2
    m2_witness = (*witness[:4], 1820 - root)
    lower = (exact.probability(5, exact.phase_score(witness, 0), witness[0], witness[-1]),
             Fraction("0.15504888347310"), Fraction(60227, 350000))

    points = list(product(*bands)) + [witness, m2_witness]
    points.extend(tuple(low + (high - low) * Fraction(rng.randrange(1_000_001), 1_000_000)
                        for low, high in bands) for _ in range(300))
    for masses in points:
        a, e = masses[0], masses[-1]
        total = exact.phase_score(masses, 0)
        actual = (exact.probability(5, total, a, e),
                  exact.probability(3, total - exact.distance(a) - exact.distance(e), a, e),
                  exact.phase_probability(masses))
        assert all(value >= bound for value, bound in zip(actual, lower))
        check_density(a, e)
    print(f"Sensitivity diagnostics: {len(points)} configurations "
          "(all corners, witnesses, 300 sampled points); density preimages agree.")

    print(f"Monte Carlo: seed={SEED}, N={TRIALS} per configuration.")
    for label, masses in (("nominal", nominal), ("M1/M3 witness", witness),
                          ("M2 root midpoint", m2_witness)):
        a, e = float(masses[0]), float(masses[-1])
        observed = float(exact.phase_score(masses, 0))
        interior = observed - direct_distance(a) - direct_distance(e)
        values = tuple(map(float, masses))
        hits = [0, 0, 0]
        for _ in range(TRIALS):
            distances = [direct_distance(rng.uniform(a, e)) for _ in range(5)]
            hits[0] += sum(distances) <= observed
            hits[1] += sum(distances[:3]) <= interior
            phase = rng.uniform(0, 70)
            hits[2] += sum(direct_distance(m - phase) for m in values) <= observed
        total = exact.phase_score(masses, 0)
        expected = (exact.probability(5, total, masses[0], masses[-1]),
                    exact.probability(3, total - exact.distance(masses[0])
                                      - exact.distance(masses[-1]), masses[0], masses[-1]),
                    exact.phase_probability(masses))
        for index in range(3):
            check_estimate(f"{label} M{index + 1}", hits[index], expected[index])

    a, e = witness[0], witness[-1]
    q1 = quantile(5, Fraction(1, 20), a, e)
    q2 = quantile(3, Fraction(1, 20), a, e)
    delta = exact.distance(a) + exact.distance(e)
    cut1, cut2 = float(q1 - delta), float(q2)
    hits1 = hits2 = 0
    for _ in range(TRIALS):
        total = sum(direct_distance(rng.uniform(float(a), float(e))) for _ in range(3))
        hits1 += total <= cut1
        hits2 += total <= cut2
    check_estimate("Conditional rejection at 5%: M1", hits1,
                   exact.probability(3, q1 - delta, a, e))
    check_estimate("Conditional rejection at 5%: M2", hits2, Fraction(1, 20))
    print("All audit checks passed. Sampled checks do not prove global minima.")


if __name__ == "__main__":
    main()
