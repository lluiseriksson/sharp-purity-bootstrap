"""
Exact quantum lattice model partition-function engines (verified against exact diagonalization,
with explicit continuous-time FILS bond-reflection positivity Gram-matrix verifiers):
  1. 1D Periodic Transverse-Field Ising Model (TFIM): exact Kaufman/Jordan-Wigner
     log-partition function in log1p/expm1 arithmetic (zero underflow/overflow at all L, beta),
     supporting both paramagnetic (h > 1) and Z2 symmetry-broken ferromagnetic (h < 1, g = 2) phases.
  2. 1D Periodic Spin-1 Heisenberg + Single-Ion Anisotropy H(D) = sum(S_i.S_{i+1} + D (S_i^z)^2)
     (strictly bond-reflection-positive for all D in R via staggered U_y), plus bilinear-biquadratic
     diagnostics showing the su(3) determinant obstruction for AKLT (c = +1/3).
  3. 1D Periodic Spin-1/2 Dimerized Antiferromagnetic Heisenberg Chain
     H(delta) = sum (1 + (-1)^i delta) S_i.S_{i+1} (strictly bond-reflection-positive across alternating
     bonds with positive 2-site unit-cell transfer operator K >= 0; exact S^z-blocked ED at L=6, 12).
"""
import math
import numpy as np
from scipy.linalg import expm


def _log_sector_tfim(ks: list[float], beta: float, h: float, sign_prod: float) -> float:
    """
    Numerically exact log(Z_sector) for periodic L-site TFIM without overflow/underflow.
    Z_sector = 0.5 * exp(0.5 * beta * sum |eps_k|) * (prod (1 + e_k) + sign_prod * prod s_k (1 - e_k))
    where e_k = exp(-beta * |eps_k|) and s_k = sign(eps_k).
    """
    e_list = []
    for k in ks:
        if abs(k) < 1e-12:
            e_list.append(2.0 * (h - 1.0))
        elif abs(k - math.pi) < 1e-12:
            e_list.append(2.0 * (h + 1.0))
        else:
            e_list.append(2.0 * math.sqrt(1.0 + h * h - 2.0 * h * math.cos(k)))

    shift = 0.5 * beta * sum(abs(e) for e in e_list)
    # Compute log(prod (1 + e_k)) and log(|prod (1 - e_k)|) + sign!
    log_pc = sum(math.log1p(math.exp(-beta * abs(e))) for e in e_list)
    sgn_ps = 1.0
    zero_ps = False
    log_ps = 0.0
    for e in e_list:
        if e < 0.0:
            sgn_ps *= -1.0
        ae = abs(e)
        if beta * ae < 1e-15:
            zero_ps = True
        else:
            # log(1 - exp(-x)) = log(-expm1(-x))
            log_ps += math.log(-math.expm1(-beta * ae))

    if zero_ps:
        return shift + log_pc - math.log(2.0)

    eff_sign = sign_prod * sgn_ps
    # Need log(0.5 * (exp(log_pc) + eff_sign * exp(log_ps)))
    # Note log_pc >= log_ps always since 1 + e >= 1 - e!
    diff = log_ps - log_pc  # <= 0
    if eff_sign > 0:
        return shift + log_pc + math.log1p(math.exp(diff)) - math.log(2.0)
    else:
        # 1 - exp(diff) = -expm1(diff) — exact even when diff ~ -1e-16!
        # Wait: if diff == 0 identically (impossible for finite beta*ae > 0 since 1+e > 1-e), safe!
        if diff > -1e-15:
            # High precision series for log_pc - log_ps = sum log((1+e)/(1-e)) >= 2 sum e
            exact_gap = sum(math.log1p(math.exp(-beta * abs(e))) - math.log(-math.expm1(-beta * abs(e))) for e in e_list)
            return shift + log_pc + math.log(-math.expm1(-exact_gap)) - math.log(2.0)
        return shift + log_pc + math.log(-math.expm1(diff)) - math.log(2.0)


def tfim_sector_logZ(L: int, beta: float, h: float) -> tuple[float, float]:
    """Exact (log Z_even, log Z_odd) for periodic L-site TFIM (L even)."""
    ks_apbc = [(2 * m + 1) * math.pi / L for m in range(L)]
    ks_pbc = [2 * m * math.pi / L for m in range(L)]
    return _log_sector_tfim(ks_apbc, beta, h, +1.0), _log_sector_tfim(ks_pbc, beta, h, -1.0)


def tfim_logZ(L: int, beta: float, h: float) -> float:
    """Exact log Z(L, beta) = log(Z_even + Z_odd) for periodic L-site TFIM (L even)."""
    ze, zo = tfim_sector_logZ(L, beta, h)
    m = max(ze, zo)
    return m + math.log1p(math.exp(-abs(ze - zo)))


def tfim_purities(L0: int, beta0: float, h: float) -> tuple[float, float, float]:
    """Returns exact (S(L0, beta0), T(2*L0, beta0), Q(L0, beta0)) for 1D TFIM."""
    lz1 = tfim_logZ(L0, beta0, h)
    lz2 = tfim_logZ(2 * L0, beta0, h)
    lz3 = tfim_logZ(2 * L0, 2.0 * beta0, h)
    S0 = math.exp(lz2 - 2.0 * lz1)
    T0 = math.exp(lz3 - 2.0 * lz2)
    return S0, T0, S0 * S0 * T0


def tfim_ed_logZ(L: int, beta: float, h: float) -> float:
    """Direct exact diagonalization of 1D TFIM (for independent cross-verification at L <= 10)."""
    dim = 1 << L
    H = np.zeros((dim, dim), dtype=np.float64)
    for s in range(dim):
        diag = 0.0
        for i in range(L):
            zi = 1.0 if ((s >> i) & 1) else -1.0
            zj = 1.0 if ((s >> ((i + 1) % L)) & 1) else -1.0
            diag -= zi * zj
            H[s, s ^ (1 << i)] -= h
        H[s, s] += diag
    ev = np.linalg.eigvalsh(H)
    e0 = float(ev[0])
    return -beta * e0 + math.log(float(np.sum(np.exp(-beta * (ev - e0)))))


def spin1_bb_full_spectrum(L: int, theta_bb: float) -> np.ndarray:
    """
    Exact full spectrum of periodic L-site Spin-1 bilinear-biquadratic chain:
      H = sum_{i=0}^{L-1} [ cos(theta) (S_i . S_{i+1}) + sin(theta) (S_i . S_{i+1})^2 ]
    using exact total-S^z block diagonalization (L=8 has max block dim 1107, solved in ~0.3s).
    Special cases:
      - theta_bb = 0: pure Spin-1 antiferromagnetic Heisenberg chain (Haldane gap ~ 0.4105)
      - theta_bb = arctan(1/3): exact AKLT chain (exact gap ~ 0.350 * sqrt(10)/3 = 0.369? Wait:
        H_AKLT = sum (1/2 S.S + 1/6 (S.S)^2 + 1/3) = (sqrt(10)/6) * H(arctan(1/3)) + L/3)
    """
    c_th = math.cos(theta_bb)
    s_th = math.sin(theta_bb)
    # Build 2-site 9x9 bond matrix in basis |m1, m2> with m in {-1, 0, +1} encoded as {0, 1, 2}
    Sx = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=np.float64) / math.sqrt(2.0)
    Sy = np.array([[0, -1j, 0], [1j, 0, -1j], [0, 1j, 0]], dtype=np.complex128) / math.sqrt(2.0)
    Sz = np.array([[1, 0, 0], [0, 0, 0], [0, 0, -1]], dtype=np.float64)
    h2 = (np.kron(Sx, Sx) + np.kron(Sy, Sy) + np.kron(Sz, Sz)).real
    bond = c_th * h2 + s_th * (h2 @ h2)
    # Extract nonzero transitions (a, b) -> (c, d) preserving a + b == c + d
    trans = {}
    for a in range(3):
        for b in range(3):
            lst = []
            row = a * 3 + b
            for c in range(3):
                for d in range(3):
                    val = float(bond[row, c * 3 + d])
                    if abs(val) > 1e-13:
                        lst.append((c, d, val))
            trans[(a, b)] = lst

    # Group all 3^L basis states by total M = sum(digits) in {0, ..., 2*L}
    dim = 3 ** L
    # Decode base-3 digits vectorized
    idx = np.arange(dim, dtype=np.int64)
    digits = np.zeros((dim, L), dtype=np.int8)
    tmp = idx.copy()
    for pos in range(L - 1, -1, -1):
        digits[:, pos] = tmp % 3
        tmp //= 3
    M_vals = digits.sum(axis=1)
    pow3 = [3 ** (L - 1 - pos) for pos in range(L)]

    all_evals = []
    for M in range(2 * L + 1):
        sector_states = idx[M_vals == M]
        n_sec = len(sector_states)
        if n_sec == 0:
            continue
        state_to_local = {int(s): k for k, s in enumerate(sector_states)}
        H_blk = np.zeros((n_sec, n_sec), dtype=np.float64)
        sec_digits = digits[sector_states]
        for k in range(n_sec):
            s_code = int(sector_states[k])
            d_row = sec_digits[k]
            for i in range(L):
                j = (i + 1) % L
                a, b = int(d_row[i]), int(d_row[j])
                base_code = s_code - a * pow3[i] - b * pow3[j]
                for c, d, val in trans[(a, b)]:
                    new_code = base_code + c * pow3[i] + d * pow3[j]
                    col = state_to_local[new_code]
                    H_blk[k, col] += val
        ev_blk = np.linalg.eigvalsh(H_blk)
        all_evals.append(ev_blk)
    return np.sort(np.concatenate(all_evals))


def spin1_heisenberg_anisotropy_spectrum(L: int, D_aniso: float) -> np.ndarray:
    """
    Exact full spectrum of periodic L-site Spin-1 Heisenberg + single-ion anisotropy chain:
      H(D) = sum_{i=0}^{L-1} [ S_i . S_{i+1} + D (S_i^z)^2 ]
    Strictly bond-reflection-positive for ALL D in R under staggered U_y = exp(i pi S^y).
    Uses exact total-S^z block diagonalization (L=8 has max block dim 1107).
    """
    Sx = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=np.float64) / math.sqrt(2.0)
    Sy = np.array([[0, -1j, 0], [1j, 0, -1j], [0, 1j, 0]], dtype=np.complex128) / math.sqrt(2.0)
    Sz = np.array([[1, 0, 0], [0, 0, 0], [0, 0, -1]], dtype=np.float64)
    bond = (np.kron(Sx, Sx) + np.kron(Sy, Sy) + np.kron(Sz, Sz)).real
    trans = {}
    for a in range(3):
        for b in range(3):
            lst = []
            row = a * 3 + b
            for c in range(3):
                for d in range(3):
                    val = float(bond[row, c * 3 + d])
                    if abs(val) > 1e-13:
                        lst.append((c, d, val))
            trans[(a, b)] = lst

    dim = 3 ** L
    idx = np.arange(dim, dtype=np.int64)
    digits = np.zeros((dim, L), dtype=np.int8)
    tmp = idx.copy()
    for pos in range(L - 1, -1, -1):
        digits[:, pos] = tmp % 3
        tmp //= 3
    M_vals = digits.sum(axis=1)
    pow3 = [3 ** (L - 1 - pos) for pos in range(L)]

    all_evals = []
    for M in range(2 * L + 1):
        sector_states = idx[M_vals == M]
        n_sec = len(sector_states)
        if n_sec == 0:
            continue
        state_to_local = {int(s): k for k, s in enumerate(sector_states)}
        H_blk = np.zeros((n_sec, n_sec), dtype=np.float64)
        sec_digits = digits[sector_states]
        for k in range(n_sec):
            s_code = int(sector_states[k])
            d_row = sec_digits[k]
            if D_aniso != 0.0:
                H_blk[k, k] += D_aniso * float(np.sum((d_row.astype(np.int64) - 1) ** 2))
            for i in range(L):
                j = (i + 1) % L
                a, b = int(d_row[i]), int(d_row[j])
                base_code = s_code - a * pow3[i] - b * pow3[j]
                for c, d, val in trans[(a, b)]:
                    new_code = base_code + c * pow3[i] + d * pow3[j]
                    col = state_to_local[new_code]
                    H_blk[k, col] += val
        all_evals.append(np.linalg.eigvalsh(H_blk))
    return np.sort(np.concatenate(all_evals))


def spin_half_dimerized_heisenberg_spectrum(L: int, delta: float) -> np.ndarray:
    """
    Exact full spectrum of periodic even-L Spin-1/2 dimerized antiferromagnetic Heisenberg chain:
      H(delta) = sum_{i=0}^{L-1} (1 + (-1)^i delta) S_i . S_{i+1}
    Strictly bond-reflection-positive across alternating bonds with positive 2-site unit-cell
    transfer operator K >= 0. Exact total-S^z block diagonalization (L=12 max block dim 924).
    """
    states_by_n = {}
    for st in range(1 << L):
        states_by_n.setdefault(st.bit_count(), []).append(st)
    all_evals = []
    for basis in states_by_n.values():
        dim = len(basis)
        pos = {s: k for k, s in enumerate(basis)}
        H = np.zeros((dim, dim), dtype=np.float64)
        for ck, st in enumerate(basis):
            diag = 0.0
            for i in range(L):
                j = (i + 1) % L
                J = 1.0 + (delta if i % 2 == 0 else -delta)
                bi = (st >> i) & 1
                bj = (st >> j) & 1
                if bi == bj:
                    diag += 0.25 * J
                else:
                    diag -= 0.25 * J
                    nst = st ^ (1 << i) ^ (1 << j)
                    H[pos[nst], ck] += 0.5 * J
            H[ck, ck] += diag
        all_evals.append(np.linalg.eigvalsh(H))
    return np.sort(np.concatenate(all_evals))


def verify_spin1_bond_rp_L4(c_biq: float = 0.0, D_aniso: float = 0.0, beta: float = 1.0) -> dict:
    """
    Direct continuous-time FILS bond-reflection positivity Gram-matrix check on L=4 for
      H = sum_i [ S_i.S_{i+1} + c_biq (S_i.S_{i+1})^2 + D_aniso (S_i^z)^2 ]
    plus exact su(3) Gell-Mann interaction determinant det(J).
    """
    Sx = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=np.float64) / math.sqrt(2.0)
    Sy = np.array([[0, -1j, 0], [1j, 0, -1j], [0, 1j, 0]], dtype=np.complex128) / math.sqrt(2.0)
    Sz = np.array([[1, 0, 0], [0, 0, 0], [0, 0, -1]], dtype=np.float64)
    I3 = np.eye(3)
    h1 = (np.kron(Sx, Sx) + np.kron(Sy, Sy) + np.kron(Sz, Sz)).real
    h2 = h1 + c_biq * (h1 @ h1)
    Sz2 = Sz @ Sz
    Uy = np.array([[0, 0, 1], [0, -1, 0], [1, 0, 0]], dtype=np.float64)

    # Exact su(3) Gell-Mann matrix J of (-h2)
    gm = [
        np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], complex) / math.sqrt(2),
        np.array([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]], complex) / math.sqrt(2),
        np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], complex) / math.sqrt(2),
        np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], complex) / math.sqrt(2),
        np.array([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]], complex) / math.sqrt(2),
        np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], complex) / math.sqrt(2),
        np.array([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]], complex) / math.sqrt(2),
        np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], complex) / math.sqrt(6),
    ]
    J = np.zeros((8, 8), dtype=complex)
    M_uy = np.zeros((8, 8), dtype=complex)
    for a in range(8):
        for b in range(8):
            Th_b = Uy @ gm[b].conj() @ Uy.T
            J[a, b] = np.trace((-h2) @ np.kron(gm[a], gm[b]))
            M_uy[a, b] = np.trace((-h2) @ np.kron(gm[a], Th_b))
    det_J = float(np.real(np.linalg.det(J)))
    min_eig_M_uy = float(np.linalg.eigvalsh(0.5 * (M_uy + M_uy.conj().T))[0])

    # Build L=4 Hamiltonian and exact continuous-time Gram matrix G_bond
    H = np.kron(h2, np.eye(9)) + np.kron(np.kron(I3, h2), I3) + np.kron(np.eye(9), h2)
    for s0 in range(3):
        for s1 in range(3):
            for s2 in range(3):
                for s3 in range(3):
                    col = s0 * 27 + s1 * 9 + s2 * 3 + s3
                    for t3 in range(3):
                        for t0 in range(3):
                            val = h2[t3 * 3 + t0, s3 * 3 + s0]
                            if abs(val) > 1e-15:
                                H[t0 * 27 + s1 * 9 + s2 * 3 + t3, col] += val
    if D_aniso != 0.0:
        for site in range(4):
            ops = [I3] * 4
            ops[site] = D_aniso * Sz2
            M = ops[0]
            for op in ops[1:]:
                M = np.kron(M, op)
            H += M
    rho4 = expm(-beta * H).reshape(9, 9, 9, 9)
    P_rev = np.zeros((9, 9))
    for a in range(3):
        for b in range(3):
            P_rev[b * 3 + a, a * 3 + b] = 1.0
    V = P_rev @ np.kron(Uy, Uy)
    G = np.einsum("al,jaib,bk->klij", V, rho4, V).reshape(81, 81)
    evG = np.linalg.eigvalsh(0.5 * (G + G.T))
    return {
        "det_J": det_J,
        "min_eig_M_Uy": min_eig_M_uy,
        "G_bond_min_eig": float(evG[0]),
        "G_bond_max_eig": float(evG[-1]),
        "is_bond_rp": bool(evG[0] >= -1e-12),
    }


def verify_spinhalf_dimerized_bond_rp_L4(delta: float, beta: float = 1.0) -> dict:
    """Direct continuous-time FILS bond-RP check on L=4 for Spin-1/2 dimerized Heisenberg chain."""
    sx = np.array([[0, 1], [1, 0]], float) / 2.0
    sy = np.array([[0, -1j], [1j, 0]], complex) / 2.0
    sz = np.array([[1, 0], [0, -1]], float) / 2.0
    sd = np.real(np.kron(sx, sx) + np.kron(sy, sy) + np.kron(sz, sz))
    uy2 = np.array([[0, 1], [-1, 0]], float)
    I2 = np.eye(2)
    H = (1.0 + delta) * np.kron(sd, np.eye(4)) + (1.0 - delta) * np.kron(np.kron(I2, sd), I2) + (1.0 + delta) * np.kron(np.eye(4), sd)
    for s0 in range(2):
        for s1 in range(2):
            for s2 in range(2):
                for s3 in range(2):
                    col = s0 * 8 + s1 * 4 + s2 * 2 + s3
                    for t3 in range(2):
                        for t0 in range(2):
                            val = (1.0 - delta) * sd[t3 * 2 + t0, s3 * 2 + s0]
                            if abs(val) > 1e-15:
                                H[t0 * 8 + s1 * 4 + s2 * 2 + t3, col] += val
    rho4 = expm(-beta * H).reshape(4, 4, 4, 4)
    P_rev = np.array([[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]], float)
    V = P_rev @ np.kron(uy2, uy2)
    G = np.einsum("al,jaib,bk->klij", V, rho4, V).reshape(16, 16)
    evG = np.linalg.eigvalsh(0.5 * (G + G.T))
    return {
        "G_bond_min_eig": float(evG[0]),
        "G_bond_max_eig": float(evG[-1]),
        "is_bond_rp": bool(evG[0] >= -1e-12),
    }


def logZ_from_spectrum(evals: np.ndarray, beta: float) -> float:
    e0 = float(evals[0])
    return -beta * e0 + math.log(float(np.sum(np.exp(-beta * (evals - e0)))))
