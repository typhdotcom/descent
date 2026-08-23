import Descent.Realization.FiniteGibbs

/-!
# The algebraic envelope of the finite Gibbs laws

The recognition identity, the exact multiplicative correction, the
nonnegative defect, and the sharp zero law never consumed state sets:
they factor entirely through a positive monotone valuation. This file
states that discovery as the interface it is.

`IsPositiveValuation Z` is the literal field-level predicate — positive,
monotone, a valuation — and the four laws are proved from it alone.
Every finite Gibbs partition function satisfies it
(`FiniteGibbs.isPositiveValuation_partition`), and conversely, over a
decidable carrier every positive valuation is the total mass of the
trivial singleton presentation `states r = {r}`, `weight = Z`
(`IsPositiveValuation.exists_singleton_presentation`): finite-sum
state-set geometry, by itself, adds no restriction beyond this envelope.
-/

namespace Descent

variable {R : Type*} [Lattice R]

/-- The algebraic envelope of a partition function: positive, monotone,
and a valuation. -/
structure IsPositiveValuation (Z : ContextField R ℝ) : Prop where
  pos : ∀ r, 0 < Z r
  mono : Monotone Z
  valuation : IsValuation Z

/-- The logarithmic field of a positive field. -/
noncomputable def logField (Z : ContextField R ℝ) : ContextField R ℝ := fun r =>
  Real.log (Z r)

namespace IsPositiveValuation

variable {Z : ContextField R ℝ} (hZ : IsPositiveValuation Z)

include hZ

theorem ne_zero (r : R) : Z r ≠ 0 :=
  (hZ.pos r).ne'

theorem mem_gauge : Z ∈ gauge R ℝ :=
  mem_gauge_iff.mpr hZ.valuation

theorem logField_mono : Monotone (logField Z) := fun a _ h =>
  Real.log_le_log (hZ.pos a) (hZ.mono h)

theorem exp_logField (r : R) : Real.exp (logField Z r) = Z r :=
  Real.exp_log (hZ.pos r)

/-- The recognition identity, from the envelope alone. -/
theorem defect_logField (a b : R) :
    defect (logField Z) a b
      = Real.log (Z a * Z b / (Z (a ⊓ b) * Z (a ⊔ b))) := by
  rw [Real.log_div (mul_ne_zero (hZ.ne_zero a) (hZ.ne_zero b))
      (mul_ne_zero (hZ.ne_zero (a ⊓ b)) (hZ.ne_zero (a ⊔ b))),
    Real.log_mul (hZ.ne_zero a) (hZ.ne_zero b),
    Real.log_mul (hZ.ne_zero (a ⊓ b)) (hZ.ne_zero (a ⊔ b)),
    defect_def, sub_add_eq_sub_sub]
  rfl

/-- The exact multiplicative correction, from the valuation law alone. -/
theorem mul_eq (a b : R) :
    Z a * Z b
      = Z (a ⊓ b) * Z (a ⊔ b) + (Z a - Z (a ⊓ b)) * (Z b - Z (a ⊓ b)) := by
  have h := hZ.valuation a b
  rw [defect_def] at h
  have hsup : Z (a ⊔ b) = Z a + Z b - Z (a ⊓ b) := by linarith
  rw [hsup]
  ring

/-- The nonnegative defect, from the envelope alone. -/
theorem defect_logField_nonneg (a b : R) :
    0 ≤ defect (logField Z) a b := by
  rw [hZ.defect_logField a b]
  refine Real.log_nonneg ((one_le_div
    (mul_pos (hZ.pos (a ⊓ b)) (hZ.pos (a ⊔ b)))).mpr ?_)
  have h := hZ.mul_eq a b
  have h1 := sub_nonneg.mpr (hZ.mono (inf_le_left : a ⊓ b ≤ a))
  have h2 := sub_nonneg.mpr (hZ.mono (inf_le_right : a ⊓ b ≤ b))
  linarith [mul_nonneg h1 h2]

theorem defect_logField_eq_zero_iff_mul {a b : R} :
    defect (logField Z) a b = 0
      ↔ Z a * Z b = Z (a ⊓ b) * Z (a ⊔ b) := by
  rw [hZ.defect_logField a b]
  have hpos : 0 < Z (a ⊓ b) * Z (a ⊔ b) :=
    mul_pos (hZ.pos (a ⊓ b)) (hZ.pos (a ⊔ b))
  constructor
  · intro h
    have h1 := Real.eq_one_of_pos_of_log_eq_zero
      (div_pos (mul_pos (hZ.pos a) (hZ.pos b)) hpos) h
    rw [div_eq_one_iff_eq hpos.ne'] at h1
    exact h1
  · intro h
    rw [h, div_self hpos.ne']
    exact Real.log_one

/-- The sharp zero law at the envelope level: zero defect exactly when
the meet carries the full value of one side. -/
theorem defect_logField_eq_zero_iff {a b : R} :
    defect (logField Z) a b = 0
      ↔ Z (a ⊓ b) = Z a ∨ Z (a ⊓ b) = Z b := by
  rw [hZ.defect_logField_eq_zero_iff_mul, hZ.mul_eq a b]
  constructor
  · intro h
    have h0 : (Z a - Z (a ⊓ b)) * (Z b - Z (a ⊓ b)) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact Or.inl (sub_eq_zero.mp h').symm
    · exact Or.inr (sub_eq_zero.mp h').symm
  · rintro (h | h) <;>
      rw [← h] <;>
      ring

/-- The converse boundary: over a decidable carrier, every positive
valuation is the total mass of the trivial singleton presentation.
Finite-sum state-set geometry adds no restriction beyond the
envelope. -/
theorem exists_singleton_presentation [DecidableEq R] :
    ∃ (states : R → Finset R) (weight : R → ℝ),
      (∀ r, (states r).Nonempty) ∧ (∀ o, 0 < weight o) ∧
        ∀ r, (∑ o ∈ states r, weight o) = Z r :=
  ⟨fun r => {r}, Z, fun r => ⟨r, Finset.mem_singleton_self r⟩, hZ.pos,
    fun r => Finset.sum_singleton Z r⟩

end IsPositiveValuation

/-- Every finite Gibbs partition function lies in the envelope. -/
theorem FiniteGibbs.isPositiveValuation_partition {Ω : Type*} [DecidableEq Ω]
    (X : FiniteGibbs R Ω) : IsPositiveValuation X.partition :=
  ⟨X.partition_pos, X.partition_mono, X.isValuation_partition⟩

/-- The log-partition is the logarithmic field of the partition. -/
theorem FiniteGibbs.logPartition_eq_logField {Ω : Type*} [DecidableEq Ω]
    (X : FiniteGibbs R Ω) : X.logPartition = logField X.partition :=
  rfl

end Descent
