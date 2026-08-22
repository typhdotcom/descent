import Descent.Core.Gauge
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Gibbs realizations

The first generative model behind a context field: each context `r` carries a
finite nonempty state space `states r` inside a common carrier, each state `x`
carries an energy `energy x`, and the realization produces

    Z r = ∑ x ∈ states r, exp (-energy x),      K = log Z.

State spaces are nonempty so `Z` is positive and the logarithm is literal.

The recognition bridge into the core calculus is exact in both readings of the
same realization:

* the pairwise defect of the log-partition field is the logarithm of the
  multiplicativity ratio `Z a * Z b / (Z (a ⊓ b) * Z (a ⊔ b))`
  (`defect_logPartition`), so it vanishes at a square exactly when the
  partition function multiplies across it;
* when the state map turns meet and join into intersection and union, the
  partition function itself is a valuation (`isValuation_partition`) --- the
  additive reading lands in the gauge.

Gibbs language is used only where it is mathematically literal: `weight` is
the Boltzmann weight `exp (-energy x)`, a product realization juxtaposes
independent systems and its partition function factors (`partition_prod`),
and shifting the energy zero point moves the log-partition by a constant
field, which is gauge (`defectEquiv_logPartition_shift`).
-/

namespace Descent

/-- A finite Gibbs realization: finite nonempty state spaces indexed by
contexts, and an energy on states. Nonemptiness keeps the partition function
positive, so its logarithm is literal. -/
structure FiniteGibbs (R Ω : Type*) where
  /-- The state space of a context. -/
  states : R → Finset Ω
  /-- Every context has at least one state. -/
  states_nonempty : ∀ r, (states r).Nonempty
  /-- The energy of a state. -/
  energy : Ω → ℝ

namespace FiniteGibbs

variable {R Ω : Type*} (X : FiniteGibbs R Ω)

/-- The Boltzmann weight of a state. -/
noncomputable def weight (x : Ω) : ℝ :=
  Real.exp (-X.energy x)

theorem weight_pos (x : Ω) : 0 < X.weight x :=
  Real.exp_pos _

/-- The partition function `Z r = ∑ x ∈ states r, exp (-energy x)`. -/
noncomputable def partition : ContextField R ℝ :=
  fun r => ∑ x ∈ X.states r, X.weight x

theorem partition_pos (r : R) : 0 < X.partition r :=
  Finset.sum_pos (fun x _ => X.weight_pos x) (X.states_nonempty r)

theorem partition_ne_zero (r : R) : X.partition r ≠ 0 :=
  (X.partition_pos r).ne'

/-- The log-partition field `K = log Z`, the field the realization presents
to the defect calculus. -/
noncomputable def logPartition : ContextField R ℝ :=
  fun r => Real.log (X.partition r)

/-- The counting realization on a family of state spaces: zero energy, so
the partition function is the counting measure. -/
def counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty) :
    FiniteGibbs R Ω :=
  ⟨states, h, fun _ => 0⟩

@[simp]
theorem states_counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty) :
    (counting states h).states = states :=
  rfl

theorem partition_counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty)
    (r : R) : (counting states h).partition r = (states r).card := by
  simp [partition, counting, weight, Real.exp_zero]

/-! ### The recognition bridge -/

section Lattice

variable [Lattice R]

/-- The recognition bridge: the pairwise defect of the log-partition field is
the logarithm of the multiplicativity ratio of the partition function. -/
theorem defect_logPartition (a b : R) :
    defect X.logPartition a b =
      Real.log (X.partition a * X.partition b /
        (X.partition (a ⊓ b) * X.partition (a ⊔ b))) := by
  rw [Real.log_div (mul_ne_zero (X.partition_ne_zero a) (X.partition_ne_zero b))
      (mul_ne_zero (X.partition_ne_zero (a ⊓ b)) (X.partition_ne_zero (a ⊔ b))),
    Real.log_mul (X.partition_ne_zero a) (X.partition_ne_zero b),
    Real.log_mul (X.partition_ne_zero (a ⊓ b)) (X.partition_ne_zero (a ⊔ b)),
    defect_def, sub_add_eq_sub_sub]
  rfl

/-- The exact obstruction: the log-partition satisfies the valuation law at a
square exactly when the partition function multiplies across it. -/
theorem defect_logPartition_eq_zero_iff {a b : R} :
    defect X.logPartition a b = 0 ↔
      X.partition a * X.partition b =
        X.partition (a ⊓ b) * X.partition (a ⊔ b) := by
  rw [X.defect_logPartition a b]
  constructor
  · intro h
    have h1 := Real.eq_one_of_pos_of_log_eq_zero
      (div_pos (mul_pos (X.partition_pos a) (X.partition_pos b))
        (mul_pos (X.partition_pos (a ⊓ b)) (X.partition_pos (a ⊔ b)))) h
    exact (div_eq_one_iff_eq
      (mul_ne_zero (X.partition_ne_zero (a ⊓ b)) (X.partition_ne_zero (a ⊔ b)))).mp h1
  · intro h
    rw [h, div_self
      (mul_ne_zero (X.partition_ne_zero (a ⊓ b)) (X.partition_ne_zero (a ⊔ b))),
      Real.log_one]

/-- The log-partition is a valuation exactly when the partition function is
multiplicative. -/
theorem isValuation_logPartition_iff :
    IsValuation X.logPartition ↔
      ∀ a b, X.partition a * X.partition b =
        X.partition (a ⊓ b) * X.partition (a ⊔ b) :=
  forall₂_congr fun _ _ => X.defect_logPartition_eq_zero_iff

/-- The additive recognition: when the state map turns meet and join into
intersection and union, the partition function itself is a valuation. -/
theorem isValuation_partition [DecidableEq Ω]
    (hinf : ∀ a b, X.states (a ⊓ b) = X.states a ∩ X.states b)
    (hsup : ∀ a b, X.states (a ⊔ b) = X.states a ∪ X.states b) :
    IsValuation X.partition := by
  intro a b
  have h := Finset.sum_union_inter (s₁ := X.states a) (s₂ := X.states b)
    (f := X.weight)
  simp only [defect, partition, hinf, hsup]
  linarith

theorem partition_mem_gauge [DecidableEq Ω]
    (hinf : ∀ a b, X.states (a ⊓ b) = X.states a ∩ X.states b)
    (hsup : ∀ a b, X.states (a ⊔ b) = X.states a ∪ X.states b) :
    X.partition ∈ gauge R ℝ :=
  mem_gauge_iff.mpr (X.isValuation_partition hinf hsup)

end Lattice

/-! ### The energy zero point is gauge -/

/-- Shifting the energy zero point. -/
def shift (c : ℝ) : FiniteGibbs R Ω :=
  ⟨X.states, X.states_nonempty, fun x => X.energy x + c⟩

@[simp]
theorem states_shift (c : ℝ) : (X.shift c).states = X.states :=
  rfl

theorem weight_shift (c : ℝ) (x : Ω) :
    (X.shift c).weight x = Real.exp (-c) * X.weight x := by
  simp [weight, shift, Real.exp_add]

theorem partition_shift (c : ℝ) (r : R) :
    (X.shift c).partition r = Real.exp (-c) * X.partition r := by
  simp [partition, weight_shift, Finset.mul_sum]

theorem logPartition_shift (c : ℝ) (r : R) :
    (X.shift c).logPartition r = X.logPartition r - c := by
  rw [logPartition, partition_shift,
    Real.log_mul (Real.exp_ne_zero _) (X.partition_ne_zero r), Real.log_exp,
    neg_add_eq_sub]
  rfl

/-- Shifting the energy zero point moves the log-partition by a constant
field, which is a valuation: the defect observable cannot see the zero
point. -/
theorem defectEquiv_logPartition_shift [Lattice R] (c : ℝ) :
    DefectEquiv (X.shift c).logPartition X.logPartition := by
  rw [defectEquiv_iff_sub_isValuation]
  have h : (X.shift c).logPartition - X.logPartition
      = ContextField.const R (-c) := by
    funext r
    rw [Pi.sub_apply, logPartition_shift, ContextField.const_apply,
      sub_sub_cancel_left]
  rw [h]
  exact ContextField.isValuation_const (-c)

/-! ### Naturality -/

/-- Pulling a realization back along a map of context systems. -/
def comap {R' : Type*} (f : R' → R) : FiniteGibbs R' Ω where
  states r := X.states (f r)
  states_nonempty r := X.states_nonempty (f r)
  energy := X.energy

@[simp]
theorem partition_comap {R' : Type*} (f : R' → R) :
    (X.comap f).partition = X.partition ∘ f :=
  rfl

@[simp]
theorem logPartition_comap {R' : Type*} (f : R' → R) :
    (X.comap f).logPartition = X.logPartition ∘ f :=
  rfl

/-- Realization-level naturality: pulling back along a lattice homomorphism
pulls the defect observable back with it. -/
theorem defect_logPartition_comap [Lattice R] {R' : Type*} [Lattice R']
    (f : LatticeHom R' R) (a b : R') :
    defect (X.comap f).logPartition a b = defect X.logPartition (f a) (f b) := by
  rw [logPartition_comap]
  exact defect_comp f X.logPartition a b

/-! ### Products -/

section Prod

variable {S Ψ : Type*} (Y : FiniteGibbs S Ψ)

/-- The product of two realizations: product state spaces with additive
energy, the independent juxtaposition. -/
def prod : FiniteGibbs (R × S) (Ω × Ψ) where
  states p := X.states p.1 ×ˢ Y.states p.2
  states_nonempty p := (X.states_nonempty p.1).product (Y.states_nonempty p.2)
  energy x := X.energy x.1 + Y.energy x.2

@[simp]
theorem states_prod (p : R × S) :
    (X.prod Y).states p = X.states p.1 ×ˢ Y.states p.2 :=
  rfl

theorem weight_prod (x : Ω × Ψ) :
    (X.prod Y).weight x = X.weight x.1 * Y.weight x.2 := by
  simp only [weight, prod, neg_add_rev, Real.exp_add]
  exact mul_comm _ _

/-- The partition function of a product realization factors. -/
theorem partition_prod (p : R × S) :
    (X.prod Y).partition p = X.partition p.1 * Y.partition p.2 := by
  simp only [partition, states_prod, weight_prod, Finset.sum_product]
  exact (Finset.sum_mul_sum _ _ _ _).symm

/-- The log-partition of a product realization is the sum of the pulled-back
factor log-partitions. -/
theorem logPartition_prod (p : R × S) :
    (X.prod Y).logPartition p = X.logPartition p.1 + Y.logPartition p.2 := by
  simp only [logPartition, partition_prod]
  exact Real.log_mul (X.partition_ne_zero _) (Y.partition_ne_zero _)

/-- The defect observable of a product realization splits componentwise. -/
theorem defect_logPartition_prod [Lattice R] [Lattice S] (a b : R × S) :
    defect (X.prod Y).logPartition a b
      = defect X.logPartition a.1 b.1 + defect Y.logPartition a.2 b.2 := by
  have h : (X.prod Y).logPartition
      = fun p : R × S => X.logPartition p.1 + Y.logPartition p.2 :=
    funext fun p => X.logPartition_prod Y p
  rw [h]
  exact defect_fst_add_snd X.logPartition Y.logPartition a b

/-- Independence: a product of realizations with valuation log-partitions has
valuation log-partition. -/
theorem isValuation_logPartition_prod [Lattice R] [Lattice S]
    (hX : IsValuation X.logPartition) (hY : IsValuation Y.logPartition) :
    IsValuation (X.prod Y).logPartition := fun a b => by
  rw [defect_logPartition_prod, hX a.1 b.1, hY a.2 b.2, add_zero]

end Prod

end FiniteGibbs

end Descent
