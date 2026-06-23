"""Manuscript figures for the elliptic-dirichlet numerical cross-validation.

Renders, in the ermak-planning report figure style (usetex serif, gridless, the
same blue/orange/pink/gray palette, error bars over the mesh ensemble), two
figures into ``latex/manuscript/figures/``:

  * ``poincare_validation.pdf`` -- the discrete first Dirichlet eigenvalue
    converging to the exact ``2 pi^2``, and the sharp Poincare constant
    ``1/sqrt(lambda_1)`` sitting below the proved Lean bounds;
  * ``h1_convergence.pdf`` -- the P1 ``H^1`` seminorm error against the mesh
    size on log-log axes, with the fitted first-order rate.

Each finite-element quantity is averaged over an ensemble of randomly jittered
meshes; the error bars are the ensemble standard deviation. The data is produced
by the Rust crate (``cargo run --bin data``); this script runs it, caches the
CSV under ``data/``, and plots it.
"""

import math
import os
import subprocess
import sys

import numpy as np

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update(
    {"text.usetex": True, "font.family": "serif", "axes.grid": False, "font.size": 11}
)

# ermak report palette.
BLUE = "#2c6fbb"
ORANGE = "#c9722f"
PINK = "#e0467c"
GRAY = "#9aa0a6"

HERE = os.path.dirname(os.path.abspath(__file__))
RUST_DIR = os.path.normpath(os.path.join(HERE, "..", "rust"))
FIG_DIR = os.path.normpath(os.path.join(HERE, "..", "..", "latex", "manuscript", "figures"))
DATA_DIR = os.path.join(HERE, "data")

# Shared error-bar style (ermak): hollow caps, gray bars, markers on top.
EBAR = dict(fmt="o-", ms=6, color=BLUE, ecolor=GRAY, capsize=3, elinewidth=1.2,
            lw=1.2, zorder=3)


def fetch_data(regen=False):
    """Parse the ensemble CSV blocks and the rate.

    Reads the cached ``data/validation.csv`` if present (the ensemble is slow);
    pass ``regen=True`` (CLI ``--regen``) to re-run ``cargo run --bin data``.
    """
    cache = os.path.join(DATA_DIR, "validation.csv")
    if not regen and os.path.exists(cache) and os.path.getsize(cache) > 0:
        with open(cache) as f:
            out = f.read()
    else:
        out = subprocess.run(
            ["cargo", "run", "-q", "-p", "elliptic-fem", "--bin", "data"],
            cwd=RUST_DIR,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(cache, "w") as f:
            f.write(out)

    eig, conv, rate = [], [], (None, None)
    block = None
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("# rate"):
            parts = line.split()
            rate = (float(parts[2]), float(parts[3]))
        elif line.startswith("# eig"):
            block = "eig"
        elif line.startswith("# conv"):
            block = "conv"
        elif not line or line.startswith("n,"):
            continue
        else:
            row = [float(x) for x in line.split(",")]
            (eig if block == "eig" else conv).append(row)
    return np.array(eig), np.array(conv), rate


def fig_poincare(eig):
    """Eigenvalue convergence and the sharp vs proved Poincare constant."""
    h = eig[:, 1]
    lam_mean, lam_std = eig[:, 2], eig[:, 3]
    cp_mean, cp_std = eig[:, 4], eig[:, 5]
    lam_exact = 2.0 * math.pi**2
    cp_sharp_exact = 1.0 / math.sqrt(lam_exact)
    cp_lean = 0.5  # averaged box constant max_side / sqrt(2 dim)
    cp_diam = 1.0 / math.sqrt(2.0)  # single-slice diameter bound

    fig, (axa, axb) = plt.subplots(1, 2, figsize=(7.4, 3.3))

    # Panel (a): eigenvalue -> 2 pi^2.
    axa.axhline(lam_exact, ls="--", lw=1.3, color=ORANGE, zorder=1,
                label=r"exact $2\pi^2$")
    axa.errorbar(h, lam_mean, yerr=lam_std, label=r"P1 discrete $\lambda_1$", **EBAR)
    axa.set_xlabel(r"mesh size $h$")
    axa.set_ylabel(r"first Dirichlet eigenvalue $\lambda_1$")
    axa.set_xlim(left=0.0)
    axa.legend(frameon=False, loc="upper left")
    axa.set_title(r"(a) eigenvalue $\to 2\pi^2$", fontsize=11)

    # Panel (b): sharp constant stays below the proved bounds. The legend lives
    # in the empty band above the highest reference line, so nothing collides.
    axb.axhline(cp_diam, ls="-", lw=1.2, color=GRAY, zorder=1,
                label=r"proved (diameter) $1/\sqrt2$")
    axb.axhline(cp_lean, ls="-", lw=1.4, color=PINK, zorder=2,
                label=r"proved (averaged) $C_P=1/2$")
    axb.axhline(cp_sharp_exact, ls="--", lw=1.3, color=ORANGE, zorder=1,
                label=r"sharp $1/(\pi\sqrt2)$")
    axb.errorbar(h, cp_mean, yerr=cp_std, label=r"numeric $1/\sqrt{\lambda_1}$", **EBAR)
    axb.set_xlabel(r"mesh size $h$")
    axb.set_ylabel(r"Poincar\'e constant $C_P$")
    axb.set_xlim(left=0.0)
    axb.set_ylim(0.0, 1.42)
    axb.legend(frameon=False, loc="upper left", fontsize=8, ncol=1,
               handlelength=1.6, labelspacing=0.35, borderaxespad=0.4)
    axb.set_title(r"(b) proved $C_P \geq$ sharp", fontsize=11)

    fig.tight_layout()
    out = os.path.join(FIG_DIR, "poincare_validation.pdf")
    fig.savefig(out)
    plt.close(fig)
    return out


def fig_convergence(conv, rate):
    """First-order H^1 convergence on log-log axes, with ensemble error bars."""
    h = conv[:, 1]
    err_mean, err_std = conv[:, 2], conv[:, 3]
    rate_mean, rate_std = rate

    fig, ax = plt.subplots(figsize=(5.2, 4.0))
    ax.errorbar(h, err_mean, yerr=err_std, fmt="o", ms=8, color=BLUE,
                ecolor=GRAY, capsize=3, elinewidth=1.2, zorder=3,
                label=r"$\|u-u_h\|_{H_0^1}$")
    # Least-squares fit through the ensemble means.
    coef = np.polyfit(np.log(h), np.log(err_mean), 1)
    hl = np.array([h.min(), h.max()])
    ax.plot(hl, np.exp(coef[1]) * hl**coef[0], "-", lw=1.3, color=PINK,
            zorder=2, label=rf"fit, rate $= {rate_mean:.3f} \pm {rate_std:.3f}$")
    # Reference slope-1 guide anchored at the coarsest point.
    c1 = err_mean[0] / h[0]
    ax.plot(hl, c1 * hl, "--", lw=1.1, color=GRAY, zorder=1, label=r"slope $1$")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"mesh size $h$")
    ax.set_ylabel(r"$H^1$ seminorm error")
    ax.legend(frameon=False, loc="lower right")
    ax.set_title(r"P1 first-order convergence", fontsize=11)

    fig.tight_layout()
    out = os.path.join(FIG_DIR, "h1_convergence.pdf")
    fig.savefig(out)
    plt.close(fig)
    return out


def main():
    os.makedirs(FIG_DIR, exist_ok=True)
    eig, conv, rate = fetch_data(regen="--regen" in sys.argv)
    p1 = fig_poincare(eig)
    p2 = fig_convergence(conv, rate)
    print(f"wrote {p1}")
    print(f"wrote {p2}")
    print(f"H1 fitted rate = {rate[0]:.4f} +- {rate[1]:.4f}")


if __name__ == "__main__":
    sys.exit(main())
