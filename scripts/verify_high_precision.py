#!/usr/bin/env python3
"""Independent high-precision & exact verifier for open conjectures in arXiv:2611.03879v1
(Tristan Cazenave, Nov 2026: 'Lemmas and Conjectures in Spectral Graph Theory').

All graphs are simple, undirected, connected, n >= 2 vertices, m edges.
Invariants:
  A: adjacency matrix, eigenvalues lambda_1 >= lambda_2 >= ... >= lambda_n, rank rk(A)
  L = D - A: Laplacian matrix, eigenvalues mu_1 >= mu_2 >= ... >= mu_n = 0
  R = sum_{uv in E} 1 / sqrt(d_u * d_v): Randic index
  rad: graph radius = min_v max_u dist(v, u)

Conjectures tested (Section 7):
  C1    (#643):    R >= lambda_2 + 1
  C1_s1:           m >= lambda_1 * (lambda_2 + 1)
  C1_s2:           2m >= lambda_1^2 + (lambda_2 + 1)^2
  C2    (#20829):  lambda_2 <= mu_1 - 2
  C3    (#501193): 2*R <= rk(A) * lambda_1
  C4    (#112951): lambda_1 <= R + mu_2
  C5    (#239534): mu_2 + rk(A) <= 2*m
  C6_1:            R^2 >= (m + 1) / 2
  C6_2:            mu_2^2 >= 4*lambda_2 + 1
  C6_3:            mu_1^2 >= 4*lambda_2 + 8
  C6_4a:           R >= (2/3)*sqrt(m) + 1/3
  C6_4b:           R >= (3/2)*sqrt(rk(A)) + 1 - 3*sqrt(2)/2
  C7:              R >= rad + sqrt(2) - 3/2

Verification rigor:
  - Connectivity, simplicity, symmetry checked explicitly.
  - Exact integer rank rk(A) via SymPy exact rational matrix RREF (ZERO floating point!).
  - Exact radius via BFS.
  - High-precision (50 decimal digits) eigenvalues and Randic index via mpmath,
    checking every eigenpair residual ||M v - lam v||_inf < 1e-(dps-10) and cross-checking against numpy.
"""

from __future__ import annotations

import json
import sys
from collections import deque
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp


def check_connected_simple(n: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    if n < 2:
        raise ValueError(f"Need n >= 2, got {n}")
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError(f"Invalid edge ({u}, {v})")
        if v in adj[u]:
            raise ValueError(f"Duplicate edge ({u}, {v})")
        adj[u].add(v)
        adj[v].add(u)
    seen = [False] * n
    q = deque([0])
    seen[0] = True
    while q:
        u = q.popleft()
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                q.append(w)
    if not all(seen):
        raise ValueError("Graph is disconnected")
    return [sorted(s) for s in adj]


def exact_radius(adj: list[list[int]]) -> int:
    n = len(adj)
    rad = n
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = deque([s])
        ecc = 0
        while q:
            u = q.popleft()
            if dist[u] > ecc:
                ecc = dist[u]
            for w in adj[u]:
                if dist[w] == -1:
                    dist[w] = dist[u] + 1
                    q.append(w)
        if ecc < rad:
            rad = ecc
    return rad


def compute_invariants_exact_hp(n: int, edges: list[tuple[int, int]], dps: int = 50) -> dict:
    adj = check_connected_simple(n, edges)
    m = len(edges)
    deg = [len(adj[i]) for i in range(n)]
    rad = exact_radius(adj)

    # Exact rank over Q using SymPy
    A_sp = sp.zeros(n, n)
    for u, v in edges:
        A_sp[u, v] = 1
        A_sp[v, u] = 1
    rk = int(A_sp.rank())

    # 50-digit precision eigenvalues & Randic index via mpmath
    mp.mp.dps = dps
    R = mp.mpf(0)
    for u, v in edges:
        R += mp.mpf(1) / mp.sqrt(mp.mpf(deg[u] * deg[v]))

    A_mp = mp.matrix(n, n)
    L_mp = mp.matrix(n, n)
    for i in range(n):
        L_mp[i, i] = mp.mpf(deg[i])
    for u, v in edges:
        A_mp[u, v] = mp.mpf(1)
        A_mp[v, u] = mp.mpf(1)
        L_mp[u, v] = mp.mpf(-1)
        L_mp[v, u] = mp.mpf(-1)

    evals_A_raw, vecs_A = mp.eigh(A_mp)
    evals_L_raw, vecs_L = mp.eigh(L_mp)
    # Verify eigenvector residuals ||M v - lam v||_inf < 1e-(dps-10) for every eigenpair
    res_tol = mp.mpf(10) ** (-(dps - 10))
    for M_mp, evs, vecs in ((A_mp, evals_A_raw, vecs_A), (L_mp, evals_L_raw, vecs_L)):
        for col in range(n):
            v = vecs[:, col]
            r_vec = M_mp * v - evs[col] * v
            err = max(abs(r_vec[i]) for i in range(n))
            assert err < res_tol, f"Eigenpair residual too large: {err}"
    evals_A = sorted(list(evals_A_raw))
    evals_L = sorted(list(evals_L_raw))
    l1 = evals_A[-1]
    l2 = evals_A[-2]
    mu1 = evals_L[-1]
    mu2 = evals_L[-2]

    # Cross-check with numpy float64 to confirm ordering/consistency
    A_np = np.zeros((n, n), dtype=np.float64)
    for u, v in edges:
        A_np[u, v] = 1.0
        A_np[v, u] = 1.0
    L_np = np.diag(deg) - A_np
    eA_np = np.linalg.eigvalsh(A_np)
    eL_np = np.linalg.eigvalsh(L_np)
    assert abs(float(l1) - eA_np[-1]) < 1e-9
    assert abs(float(l2) - eA_np[-2]) < 1e-9
    assert abs(float(mu1) - eL_np[-1]) < 1e-9
    assert abs(float(mu2) - eL_np[-2]) < 1e-9

    return {
        "n": n,
        "m": m,
        "rk": rk,
        "rad": rad,
        "R": R,
        "l1": l1,
        "l2": l2,
        "mu1": mu1,
        "mu2": mu2,
    }


def evaluate_conjectures(inv: dict) -> dict[str, mp.mpf]:
    """Return margin LHS - RHS (negative means VIOLATION of conjecture)."""
    m = mp.mpf(inv["m"])
    rk = mp.mpf(inv["rk"])
    rad = mp.mpf(inv["rad"])
    R = inv["R"]
    l1, l2, mu1, mu2 = inv["l1"], inv["l2"], inv["mu1"], inv["mu2"]
    return {
        "C1": R - (l2 + 1),
        "C1_s1": m - l1 * (l2 + 1),
        "C1_s2": 2 * m - (l1 * l1 + (l2 + 1) ** 2),
        "C2": (mu1 - 2) - l2,
        "C3": rk * l1 - 2 * R,
        "C4": (R + mu2) - l1,
        "C5": 2 * m - (mu2 + rk),
        "C6_1": R * R - (m + 1) / 2,
        "C6_2": mu2 * mu2 - (4 * l2 + 1),
        "C6_3": mu1 * mu1 - (4 * l2 + 8),
        "C6_4a": R - (mp.mpf(2) / 3 * mp.sqrt(m) + mp.mpf(1) / 3),
        "C6_4b": R - (mp.mpf(3) / 2 * mp.sqrt(rk) + 1 - 3 * mp.sqrt(2) / 2),
        "C7": R - (rad + mp.sqrt(2) - mp.mpf(3) / 2),
    }


def self_test() -> None:
    # 1. K_2: equality for C4, C5, C6_4a, C6_4b, C7? Check known equalities from paper!
    inv_k2 = compute_invariants_exact_hp(2, [(0, 1)])
    m_k2 = evaluate_conjectures(inv_k2)
    assert abs(m_k2["C4"]) < mp.mpf("1e-40"), f"K2 C4 not 0: {m_k2['C4']}"
    assert abs(m_k2["C5"]) < mp.mpf("1e-40"), f"K2 C5 not 0: {m_k2['C5']}"
    assert abs(m_k2["C6_4a"]) < mp.mpf("1e-40"), f"K2 C6_4a not 0: {m_k2['C6_4a']}"
    assert abs(m_k2["C6_4b"]) < mp.mpf("1e-40"), f"K2 C6_4b not 0: {m_k2['C6_4b']}"
    assert inv_k2["rk"] == 2

    # 2. Star S_5 (K_{1,4}): equality for C3 and C6_2
    inv_s5 = compute_invariants_exact_hp(5, [(0, 1), (0, 2), (0, 3), (0, 4)])
    m_s5 = evaluate_conjectures(inv_s5)
    assert abs(m_s5["C3"]) < mp.mpf("1e-40"), f"S5 C3 not 0: {m_s5['C3']}"
    assert abs(m_s5["C6_2"]) < mp.mpf("1e-40"), f"S5 C6_2 not 0: {m_s5['C6_2']}"

    # 3. Planted bug: disconnected graph rejected
    try:
        compute_invariants_exact_hp(4, [(0, 1), (2, 3)])
        assert False, "Failed to reject disconnected graph"
    except ValueError:
        pass

    # 4. Planted bug: duplicate edge rejected
    try:
        compute_invariants_exact_hp(3, [(0, 1), (1, 2), (0, 1)])
        assert False, "Failed to reject multigraph"
    except ValueError:
        pass

    print("verify_conj_2611_03879 self-test PASSED (K2, S5 equalities to 1e-40 + 2 negative controls)")


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
    elif len(sys.argv) >= 2:
        data = json.loads(Path(sys.argv[1]).read_text())
        inv = compute_invariants_exact_hp(data["n"], [tuple(e) for e in data["edges"]])
        margins = evaluate_conjectures(inv)
        target = data.get("conjecture")
        print(f"n={inv['n']}, m={inv['m']}, rk={inv['rk']}, rad={inv['rad']}")
        print(f"R={mp.nstr(inv['R'], 15)}, l1={mp.nstr(inv['l1'], 15)}, l2={mp.nstr(inv['l2'], 15)}, mu1={mp.nstr(inv['mu1'], 15)}, mu2={mp.nstr(inv['mu2'], 15)}")
        violated = []
        for k, v in margins.items():
            if target is None or k == target or v < mp.mpf("-1e-12"):
                print(f"  {k:8s}: margin = {mp.nstr(v, 15)}")
            if v < mp.mpf("-1e-12"):
                violated.append(k)
        if violated:
            print(f"VERIFIED COUNTEREXAMPLE(S): {violated}")
            sys.exit(0)
        print("NO COUNTEREXAMPLE (all margins >= -1e-12)")
        sys.exit(1)
    else:
        print("Usage: verify_conj_2611_03879.py --self-test | <witness.json>")
        sys.exit(2)
