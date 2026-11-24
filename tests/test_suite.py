"""
Comprehensive Gate-2 verification & adversarial falsification test suite (pytest) for Paper 2.
"""
import glob
import json
import math
import os
import sys
from fractions import Fraction
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from src.purity_bootstrap import (
    h_star_exact,
    h_star_general,
    log_rational_lower_bound,
    verify_bootstrap_certificate_exact,
    exact_uniform_threshold,
)
from src.lattice_models import (
    tfim_logZ,
    tfim_ed_logZ,
    verify_spin1_bond_rp_L4,
    verify_spinhalf_dimerized_bond_rp_L4,
)


def test_h_star_sharpness_across_branches():
    """Verify h_star_general is attained identically by (k copies of a, 1 copy of b) for k=1..5."""
    for p in [0.9, 0.6, 0.42, 0.30, 0.22]:
        k = int(math.floor(1.0 / p))
        disc = k * ((k + 1) * p - 1.0)
        a = (k + math.sqrt(disc)) / (k * (k + 1))
        b = (1.0 - math.sqrt(disc)) / (k + 1)
        assert abs(k * a + b - 1.0) < 1e-13
        assert abs(k * a * a + b * b - p) < 1e-13
        val = (k * a ** 4 + b ** 4) / (p * p)
        assert abs(val - h_star_general(p)) < 1e-14


def test_exact_uniform_fixed_point_equation():
    """Verify p_c(d) = 1 - u_c*(d) satisfies 2 p^{2a} = (1 - p) ((1 - p^a)/(1 - p))^2 to 1e-11."""
    for d in [1, 2, 3, 4]:
        a = (1 << (d + 1)) - 1
        p = 1.0 - exact_uniform_threshold(d)
        lhs = 2.0 * (p ** (2 * a))
        rhs = ((1.0 - p ** a) ** 2) / (1.0 - p)
        assert abs(lhs - rhs) < 1e-11


def test_tfim_jw_matches_exact_diagonalization():
    for L in [4, 6]:
        for h in [2.2, 1.0, 0.4]:
            assert abs(tfim_logZ(L, 1.7, h) - tfim_ed_logZ(L, 1.7, h)) < 1e-12


def test_plaquette_naive_squaring_counterexample():
    """Verify S(L, 2*beta) < S(L, beta)^2 occurs on a genuine RP model (1D TFIM), showing T(2L,beta) is essential."""
    L, beta, h = 4, 0.5, 0.5
    S_b = math.exp(tfim_logZ(2 * L, beta, h) - 2.0 * tfim_logZ(L, beta, h))
    S_2b = math.exp(tfim_logZ(2 * L, 2.0 * beta, h) - 2.0 * tfim_logZ(L, 2.0 * beta, h))
    T_2L_b = math.exp(tfim_logZ(2 * L, 2.0 * beta, h) - 2.0 * tfim_logZ(2 * L, beta, h))
    assert S_2b < S_b * S_b, "Expected strict violation of naive S(L,2b) >= S(L,b)^2"
    assert S_2b >= S_b * S_b * T_2L_b - 1e-14, "True plaquette bound S(L,2b) >= S(L,b)^2 T(2L,b) must hold"


def test_bond_rp_gram_positivity_and_aklt_obstruction():
    """Verify exact continuous-time FILS bond-RP G_bond > 0 for certified models and AKLT su(3) obstruction."""
    rp_aklt = verify_spin1_bond_rp_L4(c_biq=1.0 / 3.0, D_aniso=0.0, beta=1.0)
    assert not rp_aklt["is_bond_rp"]
    assert rp_aklt["det_J"] > 0.0
    assert rp_aklt["G_bond_min_eig"] < -0.1

    rp_heis = verify_spin1_bond_rp_L4(c_biq=0.0, D_aniso=0.0, beta=1.0)
    rp_D6 = verify_spin1_bond_rp_L4(c_biq=0.0, D_aniso=6.0, beta=1.0)
    rp_sh = verify_spinhalf_dimerized_bond_rp_L4(delta=0.5, beta=1.0)
    assert rp_heis["is_bond_rp"] and rp_D6["is_bond_rp"] and rp_sh["is_bond_rp"]


def test_exact_rational_log_lower_bound():
    for num, den in [(3, 2), (10, 1), (10**6, 1), (10**10, 3)]:
        x = Fraction(num, den)
        lb = log_rational_lower_bound(x)
        exact = math.log(num / den)
        assert float(lb) <= exact + 1e-15
        assert exact - float(lb) < 1e-10


def test_rational_verifier_falsifiers():
    """Adversarial falsification: verifier MUST reject forged traces, negative N, degenerate u_N, and tampered gaps."""
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    valid_path = os.path.join(cert_dir, "tfim1d_L8_b4_h2p5.cert.json")
    with open(valid_path) as f:
        good_cert = json.load(f)
    ok_good, _ = verify_bootstrap_certificate_exact(good_cert)
    assert ok_good

    # 1. Forged jump in trace
    bad_trace = dict(good_cert, N_steps=1, trace=[["80/100", "80/100"], ["99/100", "99/100"]])
    assert not verify_bootstrap_certificate_exact(bad_trace)[0]

    # 2. Tampered display float delta_inf_lb_float = 999.0
    bad_float = dict(good_cert, delta_inf_lb_float=999.0)
    assert not verify_bootstrap_certificate_exact(bad_float)[0]

    # 3. Tampered exact rational gap delta_inf_lb_q = "999/1"
    bad_q = dict(good_cert, delta_inf_lb_q="999/1", delta_inf_lb_float=999.0)
    assert not verify_bootstrap_certificate_exact(bad_q)[0]

    # 4. Negative N_steps
    bad_neg = dict(good_cert, N_steps=-1)
    assert not verify_bootstrap_certificate_exact(bad_neg)[0]

    # 5. Degenerate boundary p = 1/2
    deg_cert = dict(good_cert, N_steps=0, trace=[["1/2", "1/2"]])
    assert not verify_bootstrap_certificate_exact(deg_cert)[0]


def test_exported_rational_certificates_exact_replay():
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    files = sorted(glob.glob(os.path.join(cert_dir, "*.cert.json")))
    assert len(files) >= 7, f"Expected >= 7 exact rational certificates, found {len(files)}"
    for fp in files:
        with open(fp) as f:
            cert = json.load(f)
        ok, info = verify_bootstrap_certificate_exact(cert)
        assert ok, f"Exact rational replay failed for {fp}: {info}"
        assert info["rho"] < Fraction(1)
        assert info["delta_inf_lb_q"] > Fraction(0)
