# Sharp Thresholds, Piecewise-Algebraic Squaring Laws, and Machine-Checked Thermodynamic Mass-Gap Certificates for the Reflection-Positive Purity Bootstrap

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.35.0%20(0%20deps%2C%200%20sorry)-brightgreen)](lean/PurityBootstrap.lean)
[![Verifier](https://img.shields.io/badge/Certificate%20Verifier-Exact%20%E2%84%9A%20(zero%20float%20trust)-blue)](src/purity_bootstrap.py)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Companion code, zero-dependency Lean 4 formalization, exact rational ($\mathbb{Q}$) certificates, reproducible experiments, and LaTeX manuscript for:

> **Exact Sharp Thresholds, Piecewise-Algebraic Squaring Laws, and Machine-Checked Thermodynamic Mass-Gap Certificates for the Reflection-Positive Purity Bootstrap**
> *Antigravity Frontier Research Agent* (autonomous scientific research conducted in the workspace of Lluis Eriksson)

## Core Contributions

1. **Exact Piecewise-Algebraic Squaring Law (`Theorems 2.1 & 2.2`):** Solves the exact simplex minimization problem $\inf\{\sum w_i^4 / (\sum w_i^2)^2 : w_i \ge 0,\, \sum w_i = 1,\, \sum w_i^2 = p\}$ on all of $(0,1]$ in closed form; on $(1/2, 1]$ it collapses to $h_1^*(p) = 1 - \frac{(1-p)^2}{2p^2}$ with a 3-line pure ring-algebra proof (zero calculus, zero floating-point trust).
2. **Exact Sharp Gap-from-Purity Enclosures (`Theorem 2.3`):** Proves $(2w_0 - 1)^2 \ge 2p - 1$ and $e^{\beta \Delta} = w_0/w_1 \ge \frac{(1+\sqrt{2p-1})^2}{2(1-p)}$, uniquely attained on two-level Gibbs spectra.
3. **Exact $D$-Dimensional Cyclic Gauss–Seidel Thresholds (`Theorems 3.1 & 3.2`):** Replaces conservative cutoffs ($u \le 0.01$ in 1D and $1-Q \le 1/(2a^2)$ in $d$D from Grover `arXiv:2611.07400`) with the exact algebraic uniform fixed-point equation $2 p_c^{2a} = (1-p_c)(\sum_{j=0}^{a-1} p_c^j)^2$ ($a = 2^{d+1}-1$), widening the 1D uniform basin by **$12.73\times$** ($u_c^*(1) = 0.127311$) and enlarging the single-$Q$ threshold by **$3.26\times$ to $7.63\times$** across $d = 1,\dots,5$ (asymptotically **$8\times$**, scaling as $4/(a(a+1))$).
4. **Unbounded Asymptotic Gap Bounds & Intervening-Length Transfer (`Theorem 4.1`, `Theorem 4.2`, `Proposition 4.3`):** Breaks the flat $\Delta_\infty > \frac{\log 2}{\beta_0}$ ceiling via exact doubly-exponential contraction $\Delta_\infty \ge \frac{1}{2^N \beta_0}\log\!\left(\frac{1}{K_d(u_N) u_N}\right)$ for *all* even hypercube lengths $\ell \ge L_0$, delivering up to **$9.03\times$** tighter certified gaps on 1D TFIM.
5. **$\mathfrak{su}(3)$ Bond-RP No-Go Obstruction for AKLT & Strictly Bond-RP Interacting Chains (`Proposition 6.1`):** Proves via the Gell-Mann interaction determinant ($\det(J) > 0 \implies \det(M(U)) < 0\ \forall U \in U(3)$, corroborated by exact continuous-time Gram matrix $G_{\mathrm{bond}}$) that the Spin-1 AKLT chain violates bond-reflection positivity, and certifies exact-$\mathbb{Q}$ thermodynamic gaps on TWO provably bond-RP ($G_{\mathrm{bond}} \succ 0$) interacting non-integrable spin chains where Grover's $u \le 0.01$ fails completely: Spin-1 Heisenberg + single-ion anisotropy $H(D)$ ($L_0=4 \to 8$) and Spin-1/2 dimerized Heisenberg $H(\delta)$ ($L_0=6 \to 12$).
6. **Machine-Checked Lean 4 + Zero-Float-Trust Exact-$\mathbb{Q}$ Verification (`Theorem 5.1`):** 16 zero-dependency Lean 4 theorems (`leanprover/lean4:v4.35.0`, 0 `sorry`, 0 `Classical.choice`) + 7 independently replayable `.cert.json` files verifying the entire trace, contraction ratio, and rational logarithm mass-gap lower bound (`gamma_lb_q`, `delta_inf_lb_q`) strictly over $\mathbb{Q}$.

## Single-Command Gate-2 Verification

```bash
python scripts/verify_all.py
```

## Reproducing All Experiments & Figures from Scratch

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python -m pytest -v tests/test_suite.py
```
