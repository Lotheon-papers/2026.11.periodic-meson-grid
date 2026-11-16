"""Exact rational computations for the manuscript (Python standard library)."""

from collections import Counter
from csv import DictReader
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, factorial, prod
from pathlib import Path

PERIOD = 70
HALF_PERIOD = 35
ROOT_LO = Fraction("14.7028877559324")
ROOT_HI = Fraction("14.7028877559326")


def distance(value):
    phase = value % PERIOD
    return min(phase, PERIOD - phase)


def simplex_volume(count, threshold, jumps):
    volume = Fraction(0)
    for terms in combinations_with_replacement(jumps, count):
        residual = threshold - sum(knot for knot, _ in terms)
        if residual > 0:
            multiplicity = prod(factorial(n) for n in Counter(terms).values())
            weight = prod(coefficient for _, coefficient in terms)
            volume += Fraction(weight, multiplicity) * residual**count
    return volume


def density_jumps(a, e):
    """Unnormalised density of a uniform mass mapped to its distance."""
    split_points = [a, *range((a // HALF_PERIOD + 1) * HALF_PERIOD,
                              e.__ceil__(), HALF_PERIOD), e]
    jumps = Counter()
    for left, right in zip(split_points, split_points[1:]):
        low, high = sorted((distance(left), distance(right)))
        jumps[low] += 1
        jumps[high] -= 1
    return tuple((knot, weight) for knot, weight in sorted(jumps.items()) if weight)


def explicit_jumps(A, E):
    jumps = Counter({Fraction(0): 48, Fraction(HALF_PERIOD): -48})
    jumps[A] -= 1
    jumps[E] += 1
    return tuple((knot, weight) for knot, weight in sorted(jumps.items()) if weight)


def probability(count, threshold, a, e):
    return simplex_volume(count, threshold, density_jumps(a, e)) / (e - a)**count


def phase_score(masses, phase):
    return sum(distance(mass - phase) for mass in masses)


def phase_probability(masses):
    observed = phase_score(masses, Fraction(0))
    breaks = {Fraction(0), Fraction(PERIOD)}
    for mass in masses:
        breaks.update((mass % PERIOD, (mass + HALF_PERIOD) % PERIOD))
    scores = [(phase, phase_score(masses, phase)) for phase in sorted(breaks)]
    length = Fraction(0)
    for (left, f), (right, g) in zip(scores, scores[1:]):
        low, high = sorted((f, g))
        if high <= observed:
            length += right - left
        elif low < observed:
            length += (right - left) * (observed - low) / (high - low)
    return length / PERIOD


def irwin_hall(count, threshold):
    total = sum((-1)**i * comb(count, i) * max(threshold-i, 0)**count
                for i in range(count + 1))
    return Fraction(total, factorial(count))


def main():
    with Path(__file__).with_name("Masses.csv").open(encoding="utf-8") as stream:
        data = list(DictReader(stream))
    nominal = tuple(Fraction(row["nominale_MeV_c2"]) for row in data)
    a, e = nominal[0], nominal[-1]
    total = phase_score(nominal, Fraction(0))
    p1 = probability(5, total, a, e)
    p2 = probability(3, total - distance(a) - distance(e), a, e)
    p3 = phase_probability(nominal)
    assert tuple(f"{float(p):.12f}" for p in (p1, p2, p3)) == (
        "0.361078916387", "0.739463414792", "0.453606857143")
    print("Nominal S/5, M1, M2, M3:", *(f"{float(value):.12f}"
                                      for value in (total / 5, p1, p2, p3)))

    a, b, c, _, e = (Fraction(row["borne_superieure_MeV_c2"]) for row in data)
    witness = (a, b, c, Fraction(1260), e)
    A, E = 140 - a, 1820 - e
    s = distance(b) + distance(c)
    minimum_m1 = probability(5, s + A + E, a, e)
    assert minimum_m1 == Fraction(117271815670703024016458494058250829,
                                 6771887131105517591313698384755949535)
    print("M1 minimum exact:", minimum_m1)

    for trial_E in map(Fraction, ("1", "5.0227", "10", "14.7028877559325", "21")):
        assert density_jumps(a, 1820 - trial_E) == explicit_jumps(A, trial_E)

    def derivative_sign(E_value):
        jumps = explicit_jumps(A, E_value)
        width = 1680 + A - E_value
        return (simplex_volume(3, s, jumps)
                - width * simplex_volume(2, s - E_value, jumps))

    assert derivative_sign(ROOT_LO) < 0 < derivative_sign(ROOT_HI)
    midpoint = (ROOT_LO + ROOT_HI) / 2
    bound = Fraction(3, 1600) * (ROOT_HI - ROOT_LO) / 2
    p_mid = probability(3, s, a, 1820 - midpoint)
    assert Fraction("0.15504888347310") < p_mid - bound
    assert p_mid + bound < Fraction("0.15504888347311")
    print("M2 minimum enclosure: (0.15504888347310, 0.15504888347311)")

    minimum_m3 = phase_probability(witness)
    assert minimum_m3 == Fraction(60227, 350000)
    print("M3 minimum exact:", minimum_m3)
    shifts = sorted({*(distance(mass) for mass in witness),
                     *(distance(mass) + HALF_PERIOD for mass in witness),
                     Fraction(PERIOD)})
    print("M3 witness knots and scores:")
    for shift in shifts:
        print(f"  {float(shift):8.4f} {float(phase_score(witness, -shift)):8.4f}")

    lo, hi = Fraction("50.001088928"), Fraction("50.001088930")
    alpha = Fraction(1, 20)
    assert probability(5, lo, a, e) < alpha < probability(5, hi, a, e)
    assert Fraction("0.3245930589") < probability(3, lo - A - E, a, e)
    assert probability(3, hi - A - E, a, e) < Fraction("0.3245930591")
    print("M1 conditional size at witness: (0.3245930589, 0.3245930591)")

    assert irwin_hall(5, Fraction(1)) == Fraction(1, 120)
    assert irwin_hall(3, Fraction(1)) == Fraction(1, 6)
    lo, hi = Fraction("1.4346498845027"), Fraction("1.4346498845028")
    assert irwin_hall(5, lo) < alpha < irwin_hall(5, hi)
    for shift, lower, upper in (
        (0, "0.4510804422637", "0.4510804422639"),
        (1, "0.0136857138516", "0.0136857138518"),
    ):
        assert Fraction(lower) < irwin_hall(3, lo - shift)
        assert irwin_hall(3, hi - shift) < Fraction(upper)
        print(f"Five draws, full periods, endpoint score {shift} h: ({lower}, {upper})")
    assert irwin_hall(3, hi - 2) == 0
    print("Five draws, full periods, endpoint score 2 h: 0")


if __name__ == "__main__":
    main()
