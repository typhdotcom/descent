import Descent.Core.Defect
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Definiteness of the raw defect matrix

The defect matrix of a field over a finite family of contexts is symmetric
with zero diagonal. That already decides its definiteness theory: a
positive semidefinite matrix with zero diagonal is zero, so the raw defect
matrix is positive semidefinite exactly when it vanishes, and the same
holds for its negation. Definiteness carries no geometry at the level of
the raw matrix; canonical geometric structure lives in the derived kernels
of `Descent.Geometry.Kernels`.
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

end Descent
