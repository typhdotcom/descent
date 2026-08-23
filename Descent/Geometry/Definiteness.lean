import Descent.Geometry.Chambers
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Definiteness of the sampled defect matrix

The defect matrix of a field over a finite family of contexts is the
sampled defect datum. It is symmetric with zero diagonal, and --- unlike
the derived kernels of `Descent.Geometry.Kernels` --- it is
gauge-invariant: it consumes the defect observable, not a representative.

Its definiteness theory is two-sided. Ordinary positive semidefiniteness
is degenerate: a positive semidefinite matrix with zero diagonal is zero,
in either sign. The condition a hollow symmetric kernel does support is
conditional negative semidefiniteness --- nonpositive quadratic form on
centered vectors --- which is exactly positive semidefiniteness of the
centered Gram kernel (`condNegSemidef_iff_posSemidef_centeredGram`).

The sampled datum matters. On the square, conditional negativity at the
essential two-point sample detects the submodular chamber exactly; on the
full four-context sample it collapses to the chamber wall. Defect data
determines a chamber; which geometry appears depends on the sampled
observable consumed.
-/

namespace Descent

/-- A real positive semidefinite matrix with zero diagonal is zero. -/
private theorem eq_zero_of_posSemidef_of_diag_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (hdiag : ∀ i, M i i = 0) : M = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa using hdiag i
  have hsymm : M j i = M i j := by
    have h := hM.1.apply i j
    rwa [star_trivial] at h
  have hvi : ∀ k, M.mulVec (Pi.single i (1 : ℝ)) k = M k i := fun k => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hvj : ∀ k, M.mulVec (Pi.single j (1 : ℝ)) k = M k j := fun k => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hq := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - M i j • Pi.single j 1)
  rw [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    smul_dotProduct, single_dotProduct, single_dotProduct] at hq
  simp only [one_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvi, hvj,
    hdiag, hsymm] at hq
  have h2 : M i j * M i j ≤ 0 := by nlinarith [hq]
  have h3 : M i j * M i j = 0 := le_antisymm h2 (mul_self_nonneg _)
  simpa using mul_self_eq_zero.mp h3

variable {R : Type*} [Lattice R] {ι : Type*}

/-- The defect matrix of a field over a family of contexts. -/
def defectMatrix (K : ContextField R ℝ) (r : ι → R) : Matrix ι ι ℝ :=
  Matrix.of fun i j => defect K (r i) (r j)

@[simp]
theorem defectMatrix_apply (K : ContextField R ℝ) (r : ι → R) (i j : ι) :
    defectMatrix K r i j = defect K (r i) (r j) :=
  rfl

/-- The defect matrix is symmetric. -/
theorem isHermitian_defectMatrix (K : ContextField R ℝ) (r : ι → R) :
    (defectMatrix K r).IsHermitian :=
  Matrix.IsHermitian.ext_iff.mpr fun i j => by
    rw [star_trivial, defectMatrix_apply, defectMatrix_apply,
      defect_comm K (r j) (r i)]

/-- The defect matrix has zero diagonal. -/
@[simp]
theorem defectMatrix_diag (K : ContextField R ℝ) (r : ι → R) (i : ι) :
    defectMatrix K r i i = 0 :=
  defect_self K (r i)

/-- The defect matrix is gauge-invariant: it consumes only the defect
observable. -/
theorem defectMatrix_eq_of_defectEquiv {K K' : ContextField R ℝ}
    (h : DefectEquiv K K') (r : ι → R) : defectMatrix K r = defectMatrix K' r := by
  ext i j
  exact congrFun (congrFun h (r i)) (r j)

/-- Shifting by a valuation leaves the defect matrix unchanged. -/
theorem defectMatrix_add_of_isValuation {K G : ContextField R ℝ}
    (hG : IsValuation G) (r : ι → R) :
    defectMatrix (K + G) r = defectMatrix K r := by
  ext i j
  simp only [defectMatrix_apply]
  rw [defect_add, hG (r i) (r j), add_zero]

/-- Definiteness of the raw defect matrix is degenerate: it is positive
semidefinite exactly when it vanishes. -/
theorem posSemidef_defectMatrix_iff [Fintype ι] [DecidableEq ι]
    {K : ContextField R ℝ} {r : ι → R} :
    (defectMatrix K r).PosSemidef ↔ defectMatrix K r = 0 := by
  constructor
  · exact fun h =>
      eq_zero_of_posSemidef_of_diag_eq_zero h (defectMatrix_diag K r)
  · intro h
    rw [h]
    exact Matrix.PosSemidef.zero

/-- The opposite sign is equally degenerate. -/
theorem posSemidef_neg_defectMatrix_iff [Fintype ι] [DecidableEq ι]
    {K : ContextField R ℝ} {r : ι → R} :
    (-defectMatrix K r).PosSemidef ↔ defectMatrix K r = 0 := by
  constructor
  · intro h
    have h0 := eq_zero_of_posSemidef_of_diag_eq_zero h
      fun i => by simp [Matrix.neg_apply]
    rwa [neg_eq_zero] at h0
  · intro h
    rw [h, neg_zero]
    exact Matrix.PosSemidef.zero

/-! ### Conditional negativity and the centered Gram bridge -/

/-- Conditional negative semidefiniteness: the quadratic form is
nonpositive on centered vectors. -/
def CondNegSemidef {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, ∑ i, x i = 0 → dotProduct x (M.mulVec x) ≤ 0

/-- The Gram kernel of `M` centered at a base index. -/
noncomputable def centeredGram {ι : Type*} (M : Matrix ι ι ℝ) (i₀ : ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (M i i₀ + M i₀ j - M i j) / 2

@[simp]
theorem centeredGram_apply {ι : Type*} (M : Matrix ι ι ℝ) (i₀ i j : ι) :
    centeredGram M i₀ i j = (M i i₀ + M i₀ j - M i j) / 2 :=
  rfl

private theorem quad_expand {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v w : ι → ℝ) :
    dotProduct v (M.mulVec w) = ∑ i, ∑ j, v i * (M i j * w j) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

private theorem mulVec_single_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (j k : ι) : M.mulVec (Pi.single j 1) k = M k j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem sum_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : ℝ) (p q r : ι) :
    ∑ i, (a • Pi.single p 1 + b • Pi.single q 1 + c • Pi.single r 1 : ι → ℝ) i
      = a + b + c := by
  simp [Pi.single_apply, Finset.sum_add_distrib, mul_ite]

private theorem quad_three {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (a b c : ℝ) (p q r : ι) :
    dotProduct (a • Pi.single p 1 + b • Pi.single q 1 + c • Pi.single r 1)
        (M.mulVec (a • Pi.single p 1 + b • Pi.single q 1 + c • Pi.single r 1))
      = a * a * M p p + a * b * M p q + a * c * M p r
        + b * a * M q p + b * b * M q q + b * c * M q r
        + c * a * M r p + c * b * M r q + c * c * M r r := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    single_dotProduct, one_mul, mulVec_single_one, smul_eq_mul]
  ring

private theorem isHermitian_centeredGram {ι : Type*} {M : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (i₀ : ι) : (centeredGram M i₀).IsHermitian := by
  have ms : ∀ a b, M b a = M a b := fun a b => by
    have h := hM.apply a b
    rwa [star_trivial] at h
  refine Matrix.IsHermitian.ext_iff.mpr fun i j => ?_
  rw [star_trivial, centeredGram_apply, centeredGram_apply, ms i₀ j, ms i i₀, ms i j]
  ring

/-- The centered Gram form is minus half the raw form at the centered
vector. Only the base diagonal entry needs to vanish. -/
private theorem centeredGram_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} {i₀ : ι} (h0 : M i₀ i₀ = 0) (y : ι → ℝ) :
    dotProduct y ((centeredGram M i₀).mulVec y)
      = -(dotProduct (y - (∑ k, y k) • Pi.single i₀ 1)
          (M.mulVec (y - (∑ k, y k) • Pi.single i₀ 1)) / 2) := by
  have hMe : ∀ k, M.mulVec (Pi.single i₀ (1 : ℝ)) k = M k i₀ := fun k => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hA : dotProduct y (M.mulVec (Pi.single i₀ 1)) = ∑ i, y i * M i i₀ := by
    simp only [dotProduct, hMe]
  have hB : dotProduct (Pi.single i₀ (1 : ℝ)) (M.mulVec y) = ∑ j, M i₀ j * y j := by
    rw [single_dotProduct, one_mul]
    simp [Matrix.mulVec, dotProduct]
  have hE : dotProduct (Pi.single i₀ (1 : ℝ)) (M.mulVec (Pi.single i₀ 1)) = 0 := by
    rw [single_dotProduct, one_mul, hMe, h0]
  rw [quad_expand]
  simp only [centeredGram_apply]
  have hterm : ∀ i : ι, ∀ j : ι,
      y i * ((M i i₀ + M i₀ j - M i j) / 2 * y j)
        = (y i * M i i₀ * y j + M i₀ j * y j * y i - y i * (M i j * y j)) / 2 := by
    intros
    ring
  have hS1 : ∑ i, ∑ j, y i * M i i₀ * y j
      = (∑ i, y i * M i i₀) * ∑ j, y j :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have hS2 : ∑ i, ∑ j, M i₀ j * y j * y i
      = (∑ j, M i₀ j * y j) * ∑ i, y i := by
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
  have hS3 : ∑ i, ∑ j, y i * (M i j * y j) = dotProduct y (M.mulVec y) :=
    (quad_expand M y y).symm
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hS1, hS2, hS3, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    smul_dotProduct, dotProduct_sub, dotProduct_smul, dotProduct_sub,
    dotProduct_smul, hA, hB, hE]
  simp only [smul_eq_mul]
  ring

/-- The bridge: for a symmetric kernel whose base diagonal entry vanishes,
conditional negativity is exactly positive semidefiniteness of the
centered Gram kernel. -/
theorem condNegSemidef_iff_posSemidef_centeredGram {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) {i₀ : ι}
    (h0 : M i₀ i₀ = 0) :
    CondNegSemidef M ↔ (centeredGram M i₀).PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_centeredGram hM i₀) fun y => ?_
    rw [star_trivial]
    show 0 ≤ dotProduct y ((centeredGram M i₀).mulVec y)
    rw [centeredGram_form h0 y]
    have hx : ∑ i, ((y - (∑ k, y k) • Pi.single i₀ 1 : ι → ℝ)) i = 0 := by
      simp [Pi.single_apply, Finset.sum_sub_distrib, mul_ite]
    have hq := h _ hx
    linarith
  · intro h x hx
    have hform := centeredGram_form h0 x
    rw [hx, zero_smul, sub_zero] at hform
    have hq := h.dotProduct_mulVec_nonneg x
    rw [star_trivial] at hq
    have hq' : 0 ≤ dotProduct x ((centeredGram M i₀).mulVec x) := hq
    rw [hform] at hq'
    linarith

namespace Square

/-- At the essential two-point sample, the conditionally-negative
observable detects the submodular chamber exactly. -/
theorem condNegSemidef_defectMatrix_pair_iff {K : ContextField Square ℝ} :
    CondNegSemidef (defectMatrix K ![left, right]) ↔ Submodular K := by
  have h0 : (![left, right] : Fin 2 → Square) 0 = left := by decide
  have h1 : (![left, right] : Fin 2 → Square) 1 = right := by decide
  constructor
  · intro h
    have hq := h ((1 : ℝ) • Pi.single 0 1 + (-1 : ℝ) • Pi.single 1 1 + (0 : ℝ) • Pi.single 0 1)
      ((sum_three 1 (-1) 0 0 1 0).trans (by norm_num))
    rw [quad_three] at hq
    simp only [defectMatrix_apply, h0, h1, defect_self, defect_comm K right left] at hq
    refine submodular_iff.mpr (by nlinarith [hq])
  · intro hs x hx
    rw [Fin.sum_univ_two] at hx
    have hd := hs left right
    have hx1 : x 1 = -x 0 := by linarith
    rw [quad_expand]
    simp only [Fin.sum_univ_two, defectMatrix_apply, h0, h1, defect_self,
      defect_comm K right left, hx1]
    nlinarith [mul_nonneg hd (sq_nonneg (x 0))]

/-- At the full four-context sample, conditional negativity collapses to
the chamber wall: which geometry is visible depends on the sampled
datum. -/
theorem condNegSemidef_defectMatrix_square_iff {K : ContextField Square ℝ} :
    CondNegSemidef (defectMatrix K ![⊥, left, right, ⊤]) ↔ IsValuation K := by
  have e0 : (![⊥, left, right, ⊤] : Fin 4 → Square) 0 = ⊥ := by decide
  have e1 : (![⊥, left, right, ⊤] : Fin 4 → Square) 1 = left := by decide
  have e2 : (![⊥, left, right, ⊤] : Fin 4 → Square) 2 = right := by decide
  constructor
  · intro h
    have h1 := h ((1 : ℝ) • Pi.single 1 1 + (-1 : ℝ) • Pi.single 2 1 + (0 : ℝ) • Pi.single 0 1)
      ((sum_three 1 (-1) 0 1 2 0).trans (by norm_num))
    have h2 := h ((1 : ℝ) • Pi.single 1 1 + (1 : ℝ) • Pi.single 2 1 + (-2 : ℝ) • Pi.single 0 1)
      ((sum_three 1 1 (-2) 1 2 0).trans (by norm_num))
    rw [quad_three] at h1 h2
    simp only [defectMatrix_apply, e0, e1, e2, defect_self,
      defect_comm K right left,
      defect_of_le K (bot_le : (⊥ : Square) ≤ left),
      defect_of_le K (bot_le : (⊥ : Square) ≤ right),
      defect_of_ge K (bot_le : (⊥ : Square) ≤ left),
      defect_of_ge K (bot_le : (⊥ : Square) ≤ right)] at h1 h2
    have hd : defect K left right = 0 := by nlinarith [h1, h2]
    intro a b
    rw [defect_eq_defectData K, hd]
    simp [defectData]
  · intro hv x hx
    have hz : ∀ a b, defect K a b = 0 := hv
    rw [quad_expand]
    simp [hz]

end Square

end Descent
