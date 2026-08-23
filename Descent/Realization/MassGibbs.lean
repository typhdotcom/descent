import Descent.Realization.FiniteGibbs

/-!
# The mass-compatible realization

The finite Gibbs class demands its state map be a lattice homomorphism
into finite sets — literal intersection and union — and that demand is
its proved expressive boundary: it cannot cross a nondistributive
context system. This class weakens the demand to the level of weighted
mass. Its primitive data are nonempty finite state sets with positive
weights, and its compatibility laws speak only of masses:

* **meet compatibility** — meets do not gain mass;
* **join compatibility** — meet and join masses account exactly for the
  pair.

Every finite Gibbs realization induces a mass-compatible one with the
same partition function (`FiniteGibbs.toMassGibbs`), and the realization
laws that generated the defect calculus survive the weaker interface:
the partition function is a positive monotone valuation, the recognition
identity holds, the log-partition defect is nonnegative with the exact
correction

    Z a · Z b = Z (a ⊓ b) · Z (a ⊔ b)
                + (Z a - Z (a ⊓ b)) · (Z b - Z (a ⊓ b)),

and the sharp zero law becomes mass degeneracy: zero defect exactly when
the meet carries the full mass of one side.
-/

namespace Descent

/-- A mass-compatible realization: nonempty finite state sets with
positive weights, compatible with meet and join at the level of weighted
mass only. -/
structure MassGibbs (R Ω : Type*) [Lattice R] [DecidableEq Ω] where
  states : R → Finset Ω
  states_nonempty : ∀ r, (states r).Nonempty
  weight : Ω → ℝ
  weight_pos : ∀ o, 0 < weight o
  sum_weight_inf_le :
    ∀ a b, ∑ o ∈ states (a ⊓ b), weight o ≤ ∑ o ∈ states a, weight o
  sum_weight_inf_add_sup :
    ∀ a b, (∑ o ∈ states (a ⊓ b), weight o) + ∑ o ∈ states (a ⊔ b), weight o
      = (∑ o ∈ states a, weight o) + ∑ o ∈ states b, weight o

namespace MassGibbs

variable {R Ω : Type*} [Lattice R] [DecidableEq Ω] (M : MassGibbs R Ω)

/-- The partition function: total mass of the state space. -/
noncomputable def partition : ContextField R ℝ := fun r =>
  ∑ o ∈ M.states r, M.weight o

theorem partition_pos (r : R) : 0 < M.partition r :=
  Finset.sum_pos (fun o _ => M.weight_pos o) (M.states_nonempty r)

theorem partition_ne_zero (r : R) : M.partition r ≠ 0 :=
  (M.partition_pos r).ne'

theorem partition_inf_le_left (a b : R) :
    M.partition (a ⊓ b) ≤ M.partition a :=
  M.sum_weight_inf_le a b

theorem partition_inf_le_right (a b : R) :
    M.partition (a ⊓ b) ≤ M.partition b := by
  rw [show a ⊓ b = b ⊓ a from inf_comm a b]
  exact M.partition_inf_le_left b a

/-- The additive law survives the weaker interface: the partition
function is a valuation. -/
theorem isValuation_partition : IsValuation M.partition := by
  intro a b
  have h : M.partition (a ⊓ b) + M.partition (a ⊔ b)
      = M.partition a + M.partition b := M.sum_weight_inf_add_sup a b
  rw [defect_def]
  linarith

theorem partition_mem_gauge : M.partition ∈ gauge R ℝ :=
  mem_gauge_iff.mpr M.isValuation_partition

/-- Monotonicity survives: mass grows along the order. -/
theorem partition_mono : Monotone M.partition := by
  intro a b hab
  have h := M.partition_inf_le_right a b
  rw [inf_eq_left.mpr hab] at h
  exact h

/-- The log-partition field. -/
noncomputable def logPartition : ContextField R ℝ := fun r =>
  Real.log (M.partition r)

theorem logPartition_mono : Monotone M.logPartition := fun a _ h =>
  Real.log_le_log (M.partition_pos a) (M.partition_mono h)

theorem exp_logPartition (r : R) :
    Real.exp (M.logPartition r) = M.partition r :=
  Real.exp_log (M.partition_pos r)

/-- The recognition identity survives: the log-partition defect is the
logarithm of the multiplicativity ratio. -/
theorem defect_logPartition (a b : R) :
    defect M.logPartition a b
      = Real.log (M.partition a * M.partition b
          / (M.partition (a ⊓ b) * M.partition (a ⊔ b))) := by
  rw [Real.log_div (mul_ne_zero (M.partition_ne_zero a) (M.partition_ne_zero b))
      (mul_ne_zero (M.partition_ne_zero (a ⊓ b)) (M.partition_ne_zero (a ⊔ b))),
    Real.log_mul (M.partition_ne_zero a) (M.partition_ne_zero b),
    Real.log_mul (M.partition_ne_zero (a ⊓ b)) (M.partition_ne_zero (a ⊔ b)),
    defect_def, sub_add_eq_sub_sub]
  rfl

/-- The exact multiplicative correction at the mass level. -/
theorem partition_mul_partition (a b : R) :
    M.partition a * M.partition b
      = M.partition (a ⊓ b) * M.partition (a ⊔ b)
        + (M.partition a - M.partition (a ⊓ b))
          * (M.partition b - M.partition (a ⊓ b)) := by
  have h := M.isValuation_partition a b
  rw [defect_def] at h
  have hsup : M.partition (a ⊔ b)
      = M.partition a + M.partition b - M.partition (a ⊓ b) := by
    linarith
  rw [hsup]
  ring

/-- The universal sign survives the weaker interface. -/
theorem defect_logPartition_nonneg (a b : R) :
    0 ≤ defect M.logPartition a b := by
  rw [M.defect_logPartition a b]
  refine Real.log_nonneg ((one_le_div
    (mul_pos (M.partition_pos (a ⊓ b)) (M.partition_pos (a ⊔ b)))).mpr ?_)
  have h := M.partition_mul_partition a b
  have h1 := sub_nonneg.mpr (M.partition_inf_le_left a b)
  have h2 := sub_nonneg.mpr (M.partition_inf_le_right a b)
  linarith [mul_nonneg h1 h2]

theorem defect_logPartition_eq_zero_iff_mul {a b : R} :
    defect M.logPartition a b = 0
      ↔ M.partition a * M.partition b
        = M.partition (a ⊓ b) * M.partition (a ⊔ b) := by
  rw [M.defect_logPartition a b]
  have hpos : 0 < M.partition (a ⊓ b) * M.partition (a ⊔ b) :=
    mul_pos (M.partition_pos (a ⊓ b)) (M.partition_pos (a ⊔ b))
  constructor
  · intro h
    have h1 := Real.eq_one_of_pos_of_log_eq_zero
      (div_pos (mul_pos (M.partition_pos a) (M.partition_pos b)) hpos) h
    rw [div_eq_one_iff_eq hpos.ne'] at h1
    exact h1
  · intro h
    rw [h, div_self hpos.ne']
    exact Real.log_one

/-- The sharp zero law at the mass level: zero defect exactly when the
meet carries the full mass of one side. -/
theorem defect_logPartition_eq_zero_iff {a b : R} :
    defect M.logPartition a b = 0
      ↔ M.partition (a ⊓ b) = M.partition a
        ∨ M.partition (a ⊓ b) = M.partition b := by
  rw [M.defect_logPartition_eq_zero_iff_mul, M.partition_mul_partition a b]
  constructor
  · intro h
    have h0 : (M.partition a - M.partition (a ⊓ b))
        * (M.partition b - M.partition (a ⊓ b)) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact Or.inl (sub_eq_zero.mp h').symm
    · exact Or.inr (sub_eq_zero.mp h').symm
  · rintro (h | h) <;>
      rw [← h] <;>
      ring

end MassGibbs

/-- Every finite Gibbs realization induces a mass-compatible one: literal
set compatibility implies mass compatibility. -/
noncomputable def FiniteGibbs.toMassGibbs {R Ω : Type*} [Lattice R]
    [DecidableEq Ω] (X : FiniteGibbs R Ω) : MassGibbs R Ω where
  states := X.states
  states_nonempty := X.states_nonempty
  weight := X.weight
  weight_pos := X.weight_pos
  sum_weight_inf_le a b := by
    rw [X.states_inf]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
      fun o _ _ => (X.weight_pos o).le
  sum_weight_inf_add_sup a b := by
    rw [X.states_inf, X.states_sup, add_comm]
    exact Finset.sum_union_inter

@[simp]
theorem FiniteGibbs.toMassGibbs_partition {R Ω : Type*} [Lattice R]
    [DecidableEq Ω] (X : FiniteGibbs R Ω) :
    X.toMassGibbs.partition = X.partition :=
  rfl

@[simp]
theorem FiniteGibbs.toMassGibbs_logPartition {R Ω : Type*} [Lattice R]
    [DecidableEq Ω] (X : FiniteGibbs R Ω) :
    X.toMassGibbs.logPartition = X.logPartition :=
  rfl

end Descent
