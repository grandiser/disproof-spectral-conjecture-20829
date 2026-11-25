import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Formal Lean 4 disproof of Conjecture 2 (#20829) of arXiv:2611.03879v1

Tristan Cazenave, *Lemmas and Conjectures in Spectral Graph Theory* (`arXiv:2611.03879v1`,
November 2, 2026), Section 7, Conjecture 2 (#20829) asks whether every simple, undirected,
connected graph `G` on `n ≥ 2` vertices satisfies `λ₂(A(G)) ≤ μ₁(L(G)) - 2`, where
`λ₁ ≥ λ₂ ≥ …` are the eigenvalues of `G.adjMatrix ℝ` and `μ₁ ≥ μ₂ ≥ …` are the eigenvalues
of `G.lapMatrix ℝ` (using the exact definitions of `SpectralLean/Invariants.lean`).

We exhibit the 11-vertex, 14-edge simple connected graph `G₁₁` (two diamonds `K₄ - e` joined
at degree-2 vertices by a 5-vertex path `P₅`) and prove:
1. `G₁₁.Connected`
2. `(21 : ℝ) / 8 < λ₂(G₁₁)` (via Courant-Fischer on two orthogonal, `A`-orthogonal integer vectors)
3. `μ₁(G₁₁) < (37 : ℝ) / 8` (via an exact 11-term block-diagonal sum-of-squares identity)
4. `¬ (λ₂(G₁₁) ≤ μ₁(G₁₁) - 2)`

All proofs use only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Disproof20829

open Matrix SimpleGraph

/-- Adjacency predicate for `G₁₁` on `Fin 11`:
    Left diamond `{0,1,2,3}` (missing `0-3`), bridge `3-4-5-6-7`,
    right diamond `{7,8,9,10}` (missing `7-10`). -/
def g11Adj (u v : Fin 11) : Bool :=
  let a := min u.val v.val
  let b := max u.val v.val
  (a == 0 && b == 1) || (a == 0 && b == 2) || (a == 1 && b == 2) ||
  (a == 1 && b == 3) || (a == 2 && b == 3) ||
  (a == 3 && b == 4) || (a == 4 && b == 5) || (a == 5 && b == 6) || (a == 6 && b == 7) ||
  (a == 7 && b == 8) || (a == 7 && b == 9) || (a == 8 && b == 9) ||
  (a == 8 && b == 10) || (a == 9 && b == 10)

/-- The 11-vertex, 14-edge counterexample graph `G₁₁`. -/
def G11 : SimpleGraph (Fin 11) where
  Adj u v := g11Adj u v = true
  symm := ⟨fun u v h => by
    fin_cases u <;> fin_cases v <;> simp_all [g11Adj]⟩
  loopless := ⟨fun u h => by
    fin_cases u <;> simp [g11Adj] at h⟩

instance : DecidableRel G11.Adj := fun u v => inferInstanceAs (Decidable (g11Adj u v = true))

/-- Helper: every vertex of `G₁₁` is reachable from `0`. -/
private lemma g11_reachable_zero (v : Fin 11) : G11.Reachable 0 v := by
  have e01 : G11.Adj 0 1 := by decide
  have e12 : G11.Adj 1 2 := by decide
  have e13 : G11.Adj 1 3 := by decide
  have e34 : G11.Adj 3 4 := by decide
  have e45 : G11.Adj 4 5 := by decide
  have e56 : G11.Adj 5 6 := by decide
  have e67 : G11.Adj 6 7 := by decide
  have e78 : G11.Adj 7 8 := by decide
  have e89 : G11.Adj 8 9 := by decide
  have e810 : G11.Adj 8 10 := by decide
  fin_cases v
  · exact Reachable.refl 0
  · exact e01.reachable
  · exact e01.reachable.trans e12.reachable
  · exact e01.reachable.trans e13.reachable
  · exact (e01.reachable.trans e13.reachable).trans e34.reachable
  · exact ((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable
  · exact (((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable
  · exact ((((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable).trans e67.reachable
  · exact (((((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable).trans e67.reachable).trans e78.reachable
  · exact ((((((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable).trans e67.reachable).trans e78.reachable).trans e89.reachable
  · exact ((((((e01.reachable.trans e13.reachable).trans e34.reachable).trans e45.reachable).trans e56.reachable).trans e67.reachable).trans e78.reachable).trans e810.reachable

theorem g11_connected : G11.Connected := by
  refine ⟨fun u v => (g11_reachable_zero u).symm.trans (g11_reachable_zero v)⟩

/-- Exact definitions matching Cazenave's `SpectralLean/Invariants.lean`. -/
theorem adj_isHermitian : (G11.adjMatrix ℝ).IsHermitian :=
  G11.isHermitian_adjMatrix ℝ

theorem lap_isHermitian : (G11.lapMatrix ℝ).IsHermitian :=
  (G11.posSemidef_lapMatrix ℝ).isHermitian

noncomputable def adjEig (i : Fin (Fintype.card (Fin 11))) : ℝ :=
  adj_isHermitian.eigenvalues₀ i

noncomputable def lapEig (i : Fin (Fintype.card (Fin 11))) : ℝ :=
  lap_isHermitian.eigenvalues₀ i

/-- Exact quadratic form of `G11.adjMatrix ℝ` expanded explicitly over `Fin 11`. -/
private lemma adj_quad_eq (x : Fin 11 → ℝ) :
    dotProduct x ((G11.adjMatrix ℝ).mulVec x) =
      2 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2 +
           x 1 * x 3 + x 2 * x 3 +
           x 3 * x 4 + x 4 * x 5 + x 5 * x 6 + x 6 * x 7 +
           x 7 * x 8 + x 7 * x 9 + x 8 * x 9 +
           x 8 * x 10 + x 9 * x 10) := by
  simp only [dotProduct, Matrix.mulVec, SimpleGraph.adjMatrix_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [show ∀ u v : Fin 11, (if G11.Adj u v then (1 : ℝ) else 0) =
      if g11Adj u v then 1 else 0 from fun _ _ => rfl]
  simp only [g11Adj]
  norm_num
  ring

/-- Exact quadratic form of `G11.lapMatrix ℝ` expanded explicitly over `Fin 11`. -/
private lemma lap_quad_eq (x : Fin 11 → ℝ) :
    dotProduct x ((G11.lapMatrix ℝ).mulVec x) =
      (x 0 - x 1)^2 + (x 0 - x 2)^2 + (x 1 - x 2)^2 +
      (x 1 - x 3)^2 + (x 2 - x 3)^2 +
      (x 3 - x 4)^2 + (x 4 - x 5)^2 + (x 5 - x 6)^2 + (x 6 - x 7)^2 +
      (x 7 - x 8)^2 + (x 7 - x 9)^2 + (x 8 - x 9)^2 +
      (x 8 - x 10)^2 + (x 9 - x 10)^2 := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub, adj_quad_eq]
  have hdeg : ∀ i : Fin 11, (G11.degree i : ℝ) =
      match i.val with
      | 0 => 2 | 1 => 3 | 2 => 3 | 3 => 3 | 4 => 2 | 5 => 2
      | 6 => 2 | 7 => 3 | 8 => 3 | 9 => 3 | _ => 2 := by
    intro i
    fin_cases i <;> dsimp <;> norm_cast
  have hD : dotProduct x ((G11.degMatrix ℝ).mulVec x) =
      2 * (x 0)^2 + 3 * (x 1)^2 + 3 * (x 2)^2 + 3 * (x 3)^2 + 2 * (x 4)^2 +
      2 * (x 5)^2 + 2 * (x 6)^2 + 3 * (x 7)^2 + 3 * (x 8)^2 + 3 * (x 9)^2 + 2 * (x 10)^2 := by
    simp only [dotProduct, SimpleGraph.degMatrix_mulVec_apply, hdeg,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
    ring
  rw [hD]
  ring

/-- Pure real-algebra sum-of-squares positivity for `(37/8)‖x‖² - xᵀ L x`. -/
private lemma lap_sos_identity (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℝ) :
    ((37 : ℝ) / 8) * (x0^2 + x1^2 + x2^2 + x3^2 + x4^2 + x5^2 + x6^2 + x7^2 + x8^2 + x9^2 + x10^2) -
    ((x0 - x1)^2 + (x0 - x2)^2 + (x1 - x2)^2 + (x1 - x3)^2 + (x2 - x3)^2 +
     (x3 - x4)^2 + (x4 - x5)^2 + (x5 - x6)^2 + (x6 - x7)^2 +
     (x7 - x8)^2 + (x7 - x9)^2 + (x8 - x9)^2 + (x8 - x10)^2 + (x9 - x10)^2) =
    (5 / 16) * (x1 - x2)^2 + (5 / 16) * (x8 - x9)^2 +
    (21 / 16) * ((x0 - x10) + (8 / 21) * ((x1 + x2) - (x8 + x9)))^2 +
    (313 / 672) * (((x1 + x2) - (x8 + x9)) + (336 / 313) * (x3 - x7))^2 +
    (1381 / 5008) * ((x3 - x7) + (2504 / 1381) * (x4 - x6))^2 +
    (8969 / 22096) * (x4 - x6)^2 +
    (21 / 16) * ((x0 + x10) + (8 / 21) * ((x1 + x2) + (x8 + x9)))^2 +
    (313 / 672) * (((x1 + x2) + (x8 + x9)) + (336 / 313) * (x3 + x7))^2 +
    (1381 / 5008) * ((x3 + x7) + (2504 / 1381) * (x4 + x6))^2 +
    (8969 / 22096) * ((x4 + x6) + (22096 / 8969) * x5)^2 +
    (11581 / 71752) * x5^2 := by
  ring

private lemma sq_sum11_eq_zero {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : ℝ}
    {u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hc4 : 0 < c4) (hc5 : 0 < c5)
    (hc6 : 0 < c6) (hc7 : 0 < c7) (hc8 : 0 < c8) (hc9 : 0 < c9) (hc10 : 0 < c10) (hc11 : 0 < c11)
    (h : c1 * u1^2 + c2 * u2^2 + c3 * u3^2 + c4 * u4^2 + c5 * u5^2 + c6 * u6^2 +
         c7 * u7^2 + c8 * u8^2 + c9 * u9^2 + c10 * u10^2 + c11 * u11^2 ≤ 0) :
    u1 = 0 ∧ u2 = 0 ∧ u3 = 0 ∧ u4 = 0 ∧ u5 = 0 ∧ u6 = 0 ∧
    u7 = 0 ∧ u8 = 0 ∧ u9 = 0 ∧ u10 = 0 ∧ u11 = 0 := by
  have z : ∀ {c u : ℝ}, 0 < c → c * u^2 ≤ 0 → u = 0 := fun hc hle =>
    sq_eq_zero_iff.mp (le_antisymm (by nlinarith) (sq_nonneg _))
  have p1 : 0 ≤ c1 * u1^2 := by positivity
  have p2 : 0 ≤ c2 * u2^2 := by positivity
  have p3 : 0 ≤ c3 * u3^2 := by positivity
  have p4 : 0 ≤ c4 * u4^2 := by positivity
  have p5 : 0 ≤ c5 * u5^2 := by positivity
  have p6 : 0 ≤ c6 * u6^2 := by positivity
  have p7 : 0 ≤ c7 * u7^2 := by positivity
  have p8 : 0 ≤ c8 * u8^2 := by positivity
  have p9 : 0 ≤ c9 * u9^2 := by positivity
  have p10 : 0 ≤ c10 * u10^2 := by positivity
  have p11 : 0 ≤ c11 * u11^2 := by positivity
  exact ⟨z hc1 (by linarith), z hc2 (by linarith), z hc3 (by linarith), z hc4 (by linarith),
    z hc5 (by linarith), z hc6 (by linarith), z hc7 (by linarith), z hc8 (by linarith),
    z hc9 (by linarith), z hc10 (by linarith), z hc11 (by linarith)⟩

/-- Block-diagonal sum-of-squares certificate proving `(37/8) * ‖x‖² - xᵀ L x > 0` for `x ≠ 0`. -/
private lemma lap_quad_strict_lt (x : Fin 11 → ℝ) (hx : x ≠ 0) :
    dotProduct x ((G11.lapMatrix ℝ).mulVec x) < ((37 : ℝ) / 8) * dotProduct x x := by
  rw [lap_quad_eq]
  have hnorm : dotProduct x x =
      (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 + (x 5)^2 +
      (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2 + (x 10)^2 := by
    simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
    ring
  rw [hnorm]
  by_contra hle
  push Not at hle
  have hle0 : ((37 : ℝ) / 8) * ((x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 + (x 5)^2 +
      (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2 + (x 10)^2) -
      ((x 0 - x 1)^2 + (x 0 - x 2)^2 + (x 1 - x 2)^2 + (x 1 - x 3)^2 + (x 2 - x 3)^2 +
       (x 3 - x 4)^2 + (x 4 - x 5)^2 + (x 5 - x 6)^2 + (x 6 - x 7)^2 +
       (x 7 - x 8)^2 + (x 7 - x 9)^2 + (x 8 - x 9)^2 + (x 8 - x 10)^2 + (x 9 - x 10)^2) ≤ 0 := by
    linarith
  rw [lap_sos_identity] at hle0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    sq_sum11_eq_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hle0
  apply hx
  ext i
  fin_cases i <;> dsimp <;> linarith

/-- Explicit Courant-Fischer witness vectors for `λ₂(G₁₁) > 21/8`. -/
private def vAnti (i : Fin 11) : ℝ :=
  match i.val with
  | 0 => 11 | 1 => 15 | 2 => 15 | 3 => 13 | 4 => 5 | 5 => 0
  | 6 => -5 | 7 => -13 | 8 => -15 | 9 => -15 | _ => -11

private def vSym (i : Fin 11) : ℝ :=
  match i.val with
  | 0 => 11 | 1 => 15 | 2 => 15 | 3 => 13 | 4 => 6 | 5 => 5
  | 6 => 6 | 7 => 13 | 8 => 15 | 9 => 15 | _ => 11

/-- Every nonzero linear combination `a • vAnti + b • vSym` has Rayleigh quotient strictly `> 21/8`. -/
private lemma adj_quad_subspace_gt (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ((21 : ℝ) / 8) * dotProduct (a • vAnti + b • vSym) (a • vAnti + b • vSym) <
      dotProduct (a • vAnti + b • vSym) ((G11.adjMatrix ℝ).mulVec (a • vAnti + b • vSym)) := by
  rw [adj_quad_eq]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, vAnti, vSym]
  norm_num
  have h1 : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb <;> positivity
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- Orthonormal eigenbasis indexed directly by `Fin (Fintype.card (Fin 11))` matching `eigenvalues₀`. -/
private noncomputable def basis0 {M : Matrix (Fin 11) (Fin 11) ℝ} (hM : M.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card (Fin 11))) ℝ (EuclideanSpace ℝ (Fin 11)) :=
  (isSymmetric_toEuclideanLin_iff.mpr hM).eigenvectorBasis finrank_euclideanSpace

private lemma mulVec_basis0 {M : Matrix (Fin 11) (Fin 11) ℝ} (hM : M.IsHermitian)
    (i : Fin (Fintype.card (Fin 11))) :
    M *ᵥ ⇑(basis0 hM i) = (hM.eigenvalues₀ i) • ⇑(basis0 hM i) := by
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin 11) => (⇑z : Fin 11 → ℝ))
    ((isSymmetric_toEuclideanLin_iff.mpr hM).apply_eigenvectorBasis finrank_euclideanSpace i)
  simpa only [basis0, Matrix.IsHermitian.eigenvalues₀, Matrix.toLpLin_apply,
    RCLike.ofReal_real_eq_id, id_eq, WithLp.ofLp_smul] using h

/-- Upper bound: `μ₁(G₁₁) < 37/8`. -/
theorem mu1_lt : lapEig ⟨0, by decide⟩ < (37 : ℝ) / 8 := by
  set hL := lap_isHermitian
  set i0 : Fin (Fintype.card (Fin 11)) := ⟨0, by decide⟩
  set u : Fin 11 → ℝ := ⇑(basis0 hL i0)
  have hdot1 : dotProduct u u = 1 := by
    have hnorm := (basis0 hL).orthonormal.1 i0
    have hinner : inner ℝ (basis0 hL i0) (basis0 hL i0) = 1 := by
      rw [real_inner_self_eq_norm_sq, hnorm]; norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [u] using hinner
  have hne : u ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hdot1
    norm_num at hdot1
  have hμ : lapEig i0 = dotProduct u ((G11.lapMatrix ℝ).mulVec u) := by
    rw [mulVec_basis0 hL i0, dotProduct_smul, smul_eq_mul, hdot1, mul_one]
    rfl
  have hlt := lap_quad_strict_lt u hne
  rw [hdot1, mul_one] at hlt
  linarith

/-- Lower bound: `21/8 < λ₂(G₁₁)`. -/
theorem lambda2_gt : (21 : ℝ) / 8 < adjEig ⟨1, by decide⟩ := by
  set hA := adj_isHermitian
  set i0 : Fin (Fintype.card (Fin 11)) := ⟨0, by decide⟩
  set i1 : Fin (Fintype.card (Fin 11)) := ⟨1, by decide⟩
  set u0 : Fin 11 → ℝ := ⇑(basis0 hA i0)
  -- Pick nonzero (a, b) such that `v = a • vAnti + b • vSym` is orthogonal to the top eigenvector `u0`:
  set c1 : ℝ := dotProduct u0 vAnti
  set c2 : ℝ := dotProduct u0 vSym
  set a : ℝ := if c1 = 0 ∧ c2 = 0 then 1 else c2
  set b : ℝ := if c1 = 0 ∧ c2 = 0 then 0 else -c1
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_cases h : c1 = 0 ∧ c2 = 0
    · left; simp [a, h]
    · simp only [a, b, h, ↓reduceIte]
      by_cases hc2 : c2 = 0
      · right
        have hc1 : c1 ≠ 0 := fun hc1 => h ⟨hc1, hc2⟩
        exact neg_ne_zero.mpr hc1
      · left; exact hc2
  set v : Fin 11 → ℝ := a • vAnti + b • vSym
  have hv_orth : dotProduct u0 v = 0 := by
    simp only [v, dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases h : c1 = 0 ∧ c2 = 0
    · simp [a, b, h, c1, c2]
    · simp only [a, b, h, ↓reduceIte, c1, c2]; ring
  have hv_quad_gt : ((21 : ℝ) / 8) * dotProduct v v < dotProduct v ((G11.adjMatrix ℝ).mulVec v) :=
    adj_quad_subspace_gt a b hab
  have hv_pos : 0 < dotProduct v v := by
    simp only [v, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, vAnti, vSym]
    norm_num
    have h1 : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with ha | hb <;> positivity
    nlinarith [sq_nonneg a, sq_nonneg b]
  let vE : EuclideanSpace ℝ (Fin 11) := (WithLp.equiv 2 (Fin 11 → ℝ)).symm v
  set T := (G11.adjMatrix ℝ).toEuclideanLin
  set b := basis0 hA
  have h_repr : ∑ i : Fin (Fintype.card (Fin 11)), inner ℝ (b i) vE • b i = vE :=
    b.sum_repr' vE
  have h_norm_sq : dotProduct v v =
      ∑ i : Fin (Fintype.card (Fin 11)), (inner ℝ (b i) vE) ^ 2 := by
    have hparse := b.sum_sq_norm_inner_right vE
    have hvv : dotProduct v v = ‖vE‖ ^ 2 := by
      have h1 := real_inner_self_eq_norm_sq vE
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
      simpa [vE] using h1
    rw [hvv, ← hparse]
    congr 1; ext i; simp [Real.norm_eq_abs, sq_abs]
  have h_quad_inner : dotProduct v ((G11.adjMatrix ℝ).mulVec v) = inner ℝ vE (T vE) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have h_Tb : ∀ i, T (b i) = adjEig i • b i := fun i =>
    (isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i
  have h_quad_spec : dotProduct v ((G11.adjMatrix ℝ).mulVec v) =
      ∑ i : Fin (Fintype.card (Fin 11)), adjEig i * (inner ℝ (b i) vE) ^ 2 := by
    rw [h_quad_inner]
    conv_lhs => rhs; rw [← h_repr]
    rw [map_sum]
    simp only [map_smul, h_Tb, inner_sum, inner_smul_right, real_inner_comm vE]
    congr 1; ext i; ring
  have h_c0 : inner ℝ (b i0) vE = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact hv_orth
  have h_le : dotProduct v ((G11.adjMatrix ℝ).mulVec v) ≤ adjEig i1 * dotProduct v v := by
    rw [h_quad_spec, h_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = i0
    · subst hi; simp [h_c0]
    · have hi1 : i1 ≤ i := by
        rcases i with ⟨val, hval⟩
        simp only [i1, Fin.mk_le_mk]
        have hne0 : val ≠ 0 := fun h0 => hi (Fin.ext h0)
        omega
      have hant : adjEig i ≤ adjEig i1 := hA.eigenvalues₀_antitone hi1
      exact mul_le_mul_of_nonneg_right hant (sq_nonneg _)
  nlinarith

/-- Main theorem: `G₁₁` is a connected simple graph on 11 vertices refuting Conjecture 2 (#20829). -/
theorem disprove_conjecture_20829 :
    ∃ (G : SimpleGraph (Fin 11)) (_ : DecidableRel G.Adj),
      G.Connected ∧
      ¬ ((G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1, by decide⟩ ≤
         (G.posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀ ⟨0, by decide⟩ - 2) := by
  refine ⟨G11, inferInstance, g11_connected, ?_⟩
  have h1 := mu1_lt
  have h2 := lambda2_gt
  dsimp only [adjEig, lapEig, adj_isHermitian, lap_isHermitian] at h1 h2
  linarith

#print axioms disprove_conjecture_20829

end Disproof20829
