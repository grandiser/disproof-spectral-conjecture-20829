#!/usr/bin/env python3
"""Exact zero-floating-point symbolic proof disproving Conjecture 2 (#20829) of
arXiv:2611.03879v1 (Tristan Cazenave, Nov 2, 2026: 'Lemmas and Conjectures in Spectral Graph Theory').

Conjecture 2 (#20829) asks whether every simple, undirected, connected graph G (n >= 2) satisfies
    lambda_2(A(G)) <= mu_1(L(G)) - 2
where lambda_1 >= lambda_2 >= ... >= lambda_n are adjacency eigenvalues and
mu_1 >= mu_2 >= ... >= mu_n = 0 are Laplacian eigenvalues (L = D - A).

This script proves with zero floating-point arithmetic (SymPy exact integer and rational algebra):
  1. Explicit 11-vertex, 14-edge counterexample G_11 (two diamonds K_4 - e joined at degree-2
     vertices by a 5-vertex path P_5): lambda_2(G_11) >= 131/50 > (3 + sqrt(5))/2 = mu_1(G_11) - 2.
  2. Explicit infinite family G(s^2 + 1, s) on 2s^2 + 2 vertices proving inf_G (mu_1(G) - lambda_2(G)) = 1,
     so 1 is the best possible constant c in lambda_2 <= mu_1 - c (and since mu_1 >= Delta + 1 > lambda_1 > lambda_2,
     the infimum 1 is never attained by any connected graph).
"""

from __future__ import annotations

import json
from collections import deque
from pathlib import Path
import networkx as nx
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent


def verify_connected_simple(n: int, edges: list[tuple[int, int]]) -> None:
    assert n >= 2
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v
        assert v not in adj[u]
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
    assert all(seen), "Graph is not connected"


def prove_G11() -> None:
    witness = json.loads((ROOT / "data/G11.json").read_text())
    n = witness["n"]
    edges = [tuple(e) for e in witness["edges"]]
    verify_connected_simple(n, edges)
    assert n == 11 and len(edges) == 14

    # Cross-check data/G11.g6 matches data/G11.json exactly
    g6_str = (ROOT / "data/G11.g6").read_text().strip()
    assert g6_str == witness["graph6"]
    G_g6 = nx.from_graph6_bytes(g6_str.encode("ascii"))
    G_json = nx.Graph()
    G_json.add_nodes_from(range(n))
    G_json.add_edges_from(edges)
    assert nx.is_isomorphic(G_g6, G_json) and sorted(G_g6.edges()) == sorted(G_json.edges())

    A = sp.zeros(n, n)
    for u, v in edges:
        A[u, v] = A[v, u] = 1
    deg = [sum(A.row(i)) for i in range(n)]
    L = sp.diag(*deg) - A

    x = sp.Symbol("x")
    pA_expr = A.charpoly(x).as_expr()
    pL_expr = L.charpoly(x).as_expr()
    pA_poly = sp.Poly(pA_expr, x)
    pL_poly = sp.Poly(pL_expr, x)

    # Exact rational separator c = 131/50 = 2.62 (so c + 2 = 231/50 = 4.62)
    c = sp.Rational(131, 50)
    roots_A_ge_c = pA_poly.count_roots(c, None)
    roots_L_ge_c2 = pL_poly.count_roots(c + 2, None)
    assert roots_A_ge_c == 2, f"Expected 2 distinct roots of A >= {c}, got {roots_A_ge_c}"
    assert roots_L_ge_c2 == 0, f"Expected 0 roots of L >= {c+2}, got {roots_L_ge_c2}"

    # Verify which irreducible factor holds lambda_1 vs lambda_2
    f_l1 = sp.Poly(x**3 - 3 * x**2 - x + 5, x)
    f_l2 = sp.Poly(x**4 - x**3 - 5 * x**2 + x + 2, x)
    assert sp.rem(pA_poly, f_l1) == 0 and sp.rem(pA_poly, f_l2) == 0
    sep = sp.Rational(53, 20)
    assert f_l1.count_roots(sep, None) == 1
    assert f_l2.count_roots(c, sep) == 1

    # Direct algebraic proof at alpha = (3 + sqrt(5))/2 = mu_1 - 2
    alpha = (3 + sp.sqrt(5)) / 2
    assert sp.simplify(f_l1.as_expr().subs(x, alpha) - (2 - sp.sqrt(5))) == 0
    assert sp.simplify(f_l2.as_expr().subs(x, alpha) - (1 - sp.sqrt(5)) / 2) == 0

    # Exact closed form mu_1 = (7 + sqrt(5)) / 2
    mu1_exact = (7 + sp.sqrt(5)) / 2
    assert sp.simplify(pL_expr.subs(x, mu1_exact)) == 0
    assert pL_poly.count_roots(sp.Rational(4618, 1000), sp.Rational(4619, 1000)) == 1
    assert pL_poly.count_roots(sp.Rational(4619, 1000), None) == 0

    print("=== THEOREM 1: EXACT SYMBOLIC PROOF FOR G_11 (n=11, m=14, graph6=" + g6_str + ") ===")
    print(f"charpoly(A) = {sp.factor(pA_expr)}")
    print(f"charpoly(L) = {sp.factor(pL_expr)}")
    print(f"Exact mu_1  = (7 + sqrt(5))/2 < {c + 2}  (Sturm count in [{c+2}, inf) = {roots_L_ge_c2})")
    print(f"Exact l_1   > {sep} (root of x^3 - 3x^2 - x + 5)")
    print(f"Exact l_2  in [{c}, {sep}] (root of x^4 - x^3 - 5x^2 + x + 2)")
    print("At alpha = (3 + sqrt(5))/2: f_l1(alpha) = 2 - sqrt(5) < 0, f_l2(alpha) = (1 - sqrt(5))/2 < 0.")
    print("Therefore lambda_2(G_11) > (3 + sqrt(5))/2 = mu_1(G_11) - 2. Q.E.D.\n")


def prove_asymptotic_family() -> None:
    """Prove that for G(k, r) with k = s^2 + 1 and r = s (integer s >= 4):
       lambda_2(G) > k - 1 - 3/s and mu_1(G) < k + 3/s, so mu_1(G) - lambda_2(G) < 1 + 6/s.
    """
    s = sp.Symbol("s", integer=True, positive=True)
    k = s**2 + 1
    a = s**2 - s
    b = s

    A_sym = sp.Matrix([[1, a, 0], [1, a - 1, b], [0, a, b - 1]])
    A_anti = sp.Matrix([[-1, a, 0], [1, a - 1, b], [0, a, b - 1]])
    D = sp.diag(a + 1, a + b, a + b - 1)
    L_sym = D - A_sym
    L_anti = D - A_anti

    W = sp.diag(1, sp.sqrt(a), sp.sqrt(b))
    for name, M in [("A_sym", A_sym), ("A_anti", A_anti), ("L_sym", L_sym), ("L_anti", L_anti)]:
        S = sp.simplify(W * M * W.inv())
        assert S == S.T, f"{name} not symmetrizable"

    x = sp.Symbol("x")
    p_A_sym = sp.Poly(A_sym.charpoly(x).as_expr(), x)
    p_A_anti = sp.Poly(A_anti.charpoly(x).as_expr(), x)
    p_L_sym = sp.Poly(L_sym.charpoly(x).as_expr(), x)
    p_L_anti = sp.Poly(L_anti.charpoly(x).as_expr(), x)

    x_low = k - 1 - sp.Rational(3, 1) / s
    val_A_anti = sp.together(p_A_anti.as_expr().subs(x, x_low))
    val_A_sym = sp.together(p_A_sym.as_expr().subs(x, x_low))

    t = sp.Symbol("t", nonnegative=True)

    def assert_strictly_pos_for_s_ge_4(expr: sp.Expr, label: str) -> None:
        num_e, den_e = sp.fraction(sp.together(expr))
        num_t = sp.Poly(sp.expand(num_e.subs(s, t + 4)), t)
        den_t = sp.Poly(sp.expand(den_e.subs(s, t + 4)), t)
        assert all(c > 0 for c in num_t.all_coeffs()), f"{label} numerator not >0 for s>=4: {num_t}"
        assert all(c > 0 for c in den_t.all_coeffs()), f"{label} denominator not >0 for s>=4: {den_t}"

    assert_strictly_pos_for_s_ge_4(-val_A_anti, "-p_A_anti(x_low)")
    assert_strictly_pos_for_s_ge_4(-val_A_sym, "-p_A_sym(x_low)")

    x_hi = k + sp.Rational(3, 1) / s
    assert_strictly_pos_for_s_ge_4(x_hi - k, "x_hi - k (internal N_i eigenvalue)")
    assert_strictly_pos_for_s_ge_4(x_hi - (k - 1), "x_hi - (k-1) (internal M_i eigenvalue)")
    for name, P in [("L_sym", p_L_sym), ("L_anti", p_L_anti)]:
        expr = P.as_expr()
        for label, deriv in [("p", expr), ("p'", sp.diff(expr, x)), ("p''", sp.diff(expr, x, 2))]:
            assert_strictly_pos_for_s_ge_4(deriv.subs(x, x_hi), f"{name} {label}(x_hi)")

    # Cross-check exact full-matrix characteristic polynomial factorization for s = 3, 4, 5
    for sv in (3, 4, 5):
        kv = sv * sv + 1
        rv = sv
        nv = 2 * kv
        edges = []
        for off in (0, kv):
            for i in range(kv):
                for j in range(i + 1, kv):
                    if i == 0 and j <= rv:
                        continue
                    edges.append((off + i, off + j))
        edges.append((0, kv))
        verify_connected_simple(nv, edges)
        A_full = sp.zeros(nv, nv)
        for u, v in edges:
            A_full[u, v] = A_full[v, u] = 1
        L_full = sp.diag(*[sum(A_full.row(i)) for i in range(nv)]) - A_full
        av, bv = kv - 1 - rv, rv
        pA_expected = sp.expand(
            A_sym.subs(s, sv).charpoly(x).as_expr()
            * A_anti.subs(s, sv).charpoly(x).as_expr()
            * (x + 1) ** (2 * (av - 1) + 2 * (bv - 1))
        )
        pL_expected = sp.expand(
            L_sym.subs(s, sv).charpoly(x).as_expr()
            * L_anti.subs(s, sv).charpoly(x).as_expr()
            * (x - kv) ** (2 * (av - 1))
            * (x - (kv - 1)) ** (2 * (bv - 1))
        )
        assert sp.expand(A_full.charpoly(x).as_expr() - pA_expected) == 0
        assert sp.expand(L_full.charpoly(x).as_expr() - pL_expected) == 0

    print("=== THEOREM 2: EXACT ASYMPTOTIC PROOF FOR G(k=s^2+1, r=s) ===")
    print("Verified exact full-matrix charpoly factorization for s = 3, 4, 5 (n = 20, 34, 52).")
    print("All shifted numerators and denominators in t = s - 4 have strictly positive coefficients.")
    print("Therefore for every integer s >= 4:")
    print("  lambda_2(G(s^2+1, s)) > s^2 - 3/s   and   mu_1(G(s^2+1, s)) < s^2 + 1 + 3/s")
    print("  mu_1(G(s^2+1, s)) - lambda_2(G(s^2+1, s)) < 1 + 6/s  (strictly < 2 for every s >= 7).")
    print("Combined with mu_1 >= Delta + 1 > lambda_1 > lambda_2, inf_G (mu_1 - lambda_2) = 1. Q.E.D.")


if __name__ == "__main__":
    prove_G11()
    prove_asymptotic_family()
