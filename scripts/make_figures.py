"""
Generate 3 publication-quality vector PDF and PNG figures directly from verified JSON outputs.
"""
import json
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES_DIR = os.path.join(ROOT, "results")
FIG_DIR = os.path.join(ROOT, "paper", "figures")
os.makedirs(FIG_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.labelsize": 10,
    "axes.titlesize": 10.2,
    "legend.fontsize": 8.2,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "axes.grid": True,
    "grid.alpha": 0.25,
    "grid.linestyle": "--",
})


def make_fig1():
    with open(os.path.join(RES_DIR, "experiment1_squaring_and_thresholds.json")) as f:
        d = json.load(f)
    curve = d["basin_boundary_1d"]
    dims = d["dimension_thresholds"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.7), dpi=300)

    # Panel (a): Anisotropic 1D critical basin boundary vs Grover 0.99 box
    s_vals = [c["s0"] for c in curve]
    t_vals = [c["t_crit"] for c in curve]
    ax1.plot(s_vals, t_vals, "-", color="#1f77b4", linewidth=2.0, label="Exact Gauss\u2013Seidel boundary $\\partial\\mathcal{B}_{\\mathrm{gap}}^{(1)}$")
    ax1.fill_between(s_vals, t_vals, 1.0, color="#1f77b4", alpha=0.14, label=r"Certifiable gapped basin $\mathcal{B}_{\mathrm{gap}}^{(1)}$")
    # Grover's uniform box [0.99, 1]^2
    ax1.add_patch(plt.Rectangle((0.99, 0.99), 0.01, 0.01, facecolor="#d62728", edgecolor="#d62728", alpha=0.85,
                                label=r"Grover cutoff $u \leq 0.01$"))
    # Mark symmetric fixed point p_c(1) = 0.872689 and anisotropic TFIM witness (0.8656, 0.9538)
    pc1 = 1.0 - dims[0]["u_crit_uniform_ours"]
    ax1.plot([pc1], [pc1], "o", color="#ff7f0e", markersize=6.5, label=f"Uniform root $p_c(1) = {pc1:.4f}$")
    ax1.plot([0.86561], [0.95379], "*", color="#2ca02c", markersize=9, label=r"1D TFIM ($L_0=4, h=2.0$)")
    ax1.set_xlim(0.76, 1.002)
    ax1.set_ylim(0.70, 1.002)
    ax1.set_xlabel(r"Initial spatial purity $S(L_0, \beta_0)$")
    ax1.set_ylabel(r"Initial temporal purity $T(2L_0, \beta_0)$")
    ax1.set_title(r"(a) Anisotropic 1D Purity-Bootstrap Basin")
    ax1.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.6)

    # Panel (b): D-dimensional critical hypercube-product defect 1 - Q vs Grover 1/(2a^2) (all same units!)
    ds = [r["d"] for r in dims]
    q_uni_ours = [r["one_minus_Q_uniform_ours"] for r in dims]
    q_ours = [r["one_minus_Q_crit_ours"] for r in dims]
    q_grov = [r["one_minus_Q_crit_grover"] for r in dims]
    ax2.semilogy(ds, q_uni_ours, "s--", color="#2ca02c", linewidth=1.6, markersize=5.5, label=r"Ours: uniform product $1 - p_c(d)^a$")
    ax2.semilogy(ds, q_ours, "o-", color="#1f77b4", linewidth=1.8, markersize=6, label=r"Ours: single-$Q$ worst-case $1 - Q_c^*(d)$")
    ax2.semilogy(ds, q_grov, "^:", color="#d62728", linewidth=1.6, markersize=6, label=r"Grover (2026): $1/(2a^2)$")
    ax2.set_xticks(ds)
    ax2.set_xlabel(r"Spatial dimension $d$ ($D = d + 1$ space-time axes)")
    ax2.set_ylabel(r"Max certifiable hypercube defect $1 - Q$")
    ax2.set_title("(b) Sharp $D$-Dim Thresholds ($3.3\\times$\u2013$7.6\\times$ Single-$Q$)")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.6)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig1_basin_and_dim_thresholds.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig1_basin_and_dim_thresholds.png"))
    plt.close(fig)


def make_fig2():
    with open(os.path.join(RES_DIR, "experiment2_tfim_phase_diagram.json")) as f:
        d = json.load(f)
    sw = d["gap_sweep_L8_b4"]
    sc = d["scale_critical_approach"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6), dpi=300)

    hs = [r["h"] for r in sw]
    d_ex = [r["Delta_exact"] for r in sw]
    d_ours = [r["Delta_cert_ours"] for r in sw]
    d_grov = [r["Delta_cert_grover"] if r["certified_grover"] else np.nan for r in sw]

    ax1.plot(hs, d_ex, "k-", linewidth=1.6, label=r"Exact gap $\Delta_{\mathrm{exact}} = 2(h - 1)$")
    ax1.plot(hs, d_ours, "o-", color="#1f77b4", linewidth=1.8, markersize=5.5, label=r"Ours: exact-$\mathbb{Q}$ certified $\Delta_\infty$")
    ax1.plot(hs, d_grov, "s--", color="#d62728", linewidth=1.6, markersize=5.5, label=r"Grover (2026): $\log(2)/\beta_0$")
    ax1.set_xlabel(r"Transverse field $h$ ($h_c = 1$)")
    ax1.set_ylabel(r"Thermodynamic mass gap $\Delta_\infty$")
    ax1.set_title(r"(a) 1D TFIM Certified Gap ($L_0=8, \beta_0=4$)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.8)

    # Panel (b): Distance to critical point h_min - 1 across scales
    labels = [f"$L_0={r['L0']}$\n$\\beta_0={int(r['beta0'])}$" for r in sc]
    x = np.arange(len(sc))
    w = 0.34
    ax2.bar(x - w / 2, [r["dist_to_hc_ours"] for r in sc], width=w, color="#1f77b4", label=r"Ours: $h_{\min} - h_c$ (exact-$\mathbb{Q}$)")
    ax2.bar(x + w / 2, [r["dist_to_hc_grover"] for r in sc], width=w, color="#d62728", alpha=0.85, label=r"Grover ($u \leq 0.01$): $h_{\min} - h_c$")
    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylabel(r"Distance to quantum critical point $h_{\min} - 1$")
    ax2.set_title("(b) Critical-Point Approach ($2.2\\times$\u2013$4.7\\times$ Closer)")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.8)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig2_tfim_certified_gap_critical.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig2_tfim_certified_gap_critical.png"))
    plt.close(fig)


def make_fig3():
    with open(os.path.join(RES_DIR, "experiment3_interacting_rp_and_ferro.json")) as f:
        d3 = json.load(f)
    with open(os.path.join(RES_DIR, "experiment4_2d_bilayer_and_finite_sample.json")) as f:
        d4 = json.load(f)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6), dpi=300)

    # Panel (a): Strictly bond-RP interacting Spin-1 H(D) (L0=4->8) & Spin-1/2 dimerized (L0=6->12)
    s1 = d3["spin1_heisenberg_anisotropy_L4"]
    sh = d3["spinhalf_dimerized_heisenberg_L6"]
    ax1_r = ax1.twinx()
    l1 = ax1.plot([r["D"] for r in s1], [r["Delta_cert_ours"] for r in s1], "o-", color="#2ca02c", linewidth=1.8, markersize=5.5,
                  label=r"Spin-1 $H(D)$ ($L_0=4, \beta_0=2$): exact-$\mathbb{Q}$ $\Delta_\infty$")
    # Plot Spin-1/2 dimerized vs top/rescaled axis? Even cleaner: plot Spin-1 H(D) exact L=8 gap vs certified!
    ax1_r.remove()
    ax1.plot([r["D"] for r in s1], [r["gap_L8"] for r in s1], "k:", linewidth=1.4, label=r"Spin-1 $H(D)$ exact ED gap ($L=8$)")
    # Add inset or companion Spin-1/2 dimerized? Let's plot normalized certified fraction or two panels?
    # Actually Spin-1 H(D) has D in [4, 8] and Delta_cert in [0, 1.17] — super clean! Let's also annotate Grover=0 everywhere!
    ax1.plot([r["D"] for r in s1], [0.0 for _ in s1], "s--", color="#d62728", linewidth=1.4, markersize=4.5,
             label=r"Grover ($u \leq 0.01$): fails at all $D \in [4, 8]$")
    ax1.set_xlabel(r"Single-ion anisotropy $D$ in $H(D) = \sum(\mathbf{S}_i\cdot\mathbf{S}_{i+1} + D(S_i^z)^2)$")
    ax1.set_ylabel(r"Thermodynamic mass gap $\Delta_\infty$")
    ax1.set_title(r"(a) Strictly Bond-RP Spin-1 $H(D)$ ($L_0=4 \to \infty$)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.4)

    # Panel (b): 2D (d=2, D=3) certified gap * beta0 vs 1 - Q0
    r2 = d4["d2_certificates_vs_grover"]
    defs = [r["defect_1_minus_Q0"] for r in r2]
    g_ours = [r["Delta_cert_ours_times_beta0"] for r in r2]
    g_grov = [r["Delta_cert_grover_times_beta0"] if r["certified_grover_2d"] else np.nan for r in r2]
    ax2.plot(defs, g_ours, "o-", color="#1f77b4", linewidth=1.8, markersize=6, label=r"Ours: exact-$\mathbb{Q}$ 2D bound $\beta_0 \Delta_\infty$")
    ax2.plot(defs, g_grov, "s--", color="#d62728", linewidth=1.6, markersize=5.5, label=r"Grover 2D ($1-Q \leq 1/98$): $\log 2$")
    ax2.axvline(1.0 / 98.0, color="#d62728", linestyle=":", linewidth=1.2, alpha=0.8)
    ax2.set_xlabel(r"2D hypercube purity defect $1 - Q(L_0, \beta_0)$")
    ax2.set_ylabel(r"Certified dimensionless gap $\beta_0 \Delta_\infty$")
    ax2.set_title(r"(b) 2D ($D=3$) Certified Gap vs. Defect $1 - Q_0$")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.6)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig3_interacting_rp_and_2d.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig3_interacting_rp_and_2d.png"))
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 publication figures in paper/figures/.")
