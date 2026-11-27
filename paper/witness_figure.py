"""Render the stated witness and its full overlap profile (requires Matplotlib)."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("pdf")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def vertices(heights, den):
    # Each of the n products at a single lag is at most den**2.
    n = len(heights)
    limb_bytes = ((n * den**2).bit_length() + 7) // 8

    def pack(digits):
        return int.from_bytes(b"".join(x.to_bytes(limb_bytes, "little") for x in digits), "little")

    product = pack(heights) * pack(den - x for x in reversed(heights))
    digits = product.to_bytes(limb_bytes * (2*n-1), "little")
    return [0, *(int.from_bytes(digits[i:i+limb_bytes], "little")
                 for i in range(0, len(digits), limb_bytes)), 0]


def main():
    construction = json.loads((ROOT / "construction.json").read_text())
    cert = json.loads((ROOT / "certificate.json").read_text())
    a, den = construction["numerators"], construction["denominator"]
    n = len(a)
    events = vertices(a, den)
    digest = hashlib.sha256("".join(f"{x}\n" for x in events).encode()).hexdigest()
    if digest != cert["event_sha256"]:
        raise ValueError("Grid vertices differ from the certificate")
    maximum = max(events)
    lags = [j-n for j, v in enumerate(events) if v == maximum]
    cap = Fraction(2*maximum, n*den**2)
    if lags != cert["peak_lags"] or len(lags) != 1 or cap != Fraction(cert["cap"]):
        raise ValueError("Maximum or maximizing lag differs from the certificate")

    # Float conversion is confined to the graphical representation.
    plt.rcParams.update({"font.size": 8.5, "pdf.fonttype": 42, "path.simplify": False,
                         "axes.spines.top": False, "axes.spines.right": False})
    fig, (density, overlap) = plt.subplots(2, 1, figsize=(3.34, 2.62))
    fig.subplots_adjust(left=.17, right=.98, top=.96, bottom=.17, hspace=.85)
    density.stairs([x/den for x in a], [2*i/n for i in range(n+1)], baseline=None,
                   linewidth=.65, color="#273e53")
    density.set(xlim=(0, 2), ylim=(-.025, 1.025), xticks=[0, 1, 2],
                yticks=[0, .5, 1], ylabel="$h(x)$", xlabel="position $x$")
    overlap.plot([2*k/n for k in range(-n, n+1)],
                 [2*v/(n*den**2) for v in events], lw=.85, color="#273e53")
    s = Fraction(2*lags[0], n)
    overlap.plot(float(s), float(cap), "o", markeredgecolor="black", markeredgewidth=.5,
                 markerfacecolor="white", ms=4.5, zorder=3)
    overlap.annotate("$-571/1176$", (float(s), float(cap)), xytext=(14, 4),
                     textcoords="offset points", fontsize=7)
    overlap.set(xlim=(-2, 2), ylim=(-.01, .465), xticks=[-2, -1, 0, 1, 2],
                yticks=[0, .2, .4], ylabel="$H(s)$", xlabel="signed shift $s$")
    for axis in (density, overlap):
        axis.tick_params(length=2.5, width=.65, pad=2)
        axis.grid(axis="y", color=".88", linewidth=.4)
        axis.set_axisbelow(True)
    target = ROOT / "paper/generated/witness-profile.pdf"
    fig.savefig(target, metadata={"Title": "Witness density and signed overlap",
                                  "CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
