import Descent.Core.Gauge
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sum

/-!
# Finite Gibbs realizations

The first generative model behind a context field. A finite Gibbs realization
is a lattice homomorphism from contexts to finite nonempty state spaces ---
meet is intersection, join is union --- together with an energy on states. It
produces

    Z r = ∑ x ∈ states r, exp (-energy x),      K = log Z.

State spaces are nonempty so `Z` is positive and the logarithm is literal.
The lattice compatibility is structural: without it the class realizes every
field exactly (`states r = {r}`, `energy = -K`) and constrains nothing.

The two readings of the same realization obey different laws. The partition
function of every realization is a valuation (`isValuation_partition`): the
additive reading lands in the gauge. The log-partition is governed by the
recognition identity `defect_logPartition` --- its defect is the logarithm of
the multiplicativity ratio --- and by the exact correction
`partition_mul_partition`, which gives that defect a universal sign
(`defect_logPartition_nonneg`) and a sharp vanishing law: zero defect at a
square is exactly nested state spaces
(`defect_logPartition_eq_zero_iff_subset`), and it forces the partition
function at the meet to agree with one of the sides
(`partition_inf_eq_of_defect_eq_zero`). Nothing in this class factors
nontrivially; the product of realizations is not a construction of the class
because product state maps do not send join to union.

Log-partitions are monotone (`logPartition_mono`), and the class is genuinely
restrictive: an explicit field on the two-element chain is the log-partition
of no realization over any state carrier (`exists_not_logPartition`).

Gibbs language is used only where it is mathematically literal: `weight` is
the Boltzmann weight `exp (-energy x)`, `mass` is the total weight of a set
of states, and shifting the energy zero point moves the log-partition by a
constant field, which is gauge (`defectEquiv_logPartition_shift`).
-/

namespace Descent

/-- A finite Gibbs realization: a lattice homomorphism from contexts to
finite nonempty state spaces --- meet is intersection, join is union ---
together with an energy on states. Nonemptiness keeps the partition function
positive, so its logarithm is literal; the lattice compatibility is what
makes the class restrictive. -/
structure FiniteGibbs (R Ω : Type*) [Lattice R] [DecidableEq Ω] where
  /-- The state space of a context. -/
  states : R → Finset Ω
  /-- Every context has at least one state. -/
  states_nonempty : ∀ r, (states r).Nonempty
  /-- The state map sends meet to intersection. -/
  states_inf : ∀ a b, states (a ⊓ b) = states a ∩ states b
  /-- The state map sends join to union. -/
  states_sup : ∀ a b, states (a ⊔ b) = states a ∪ states b
  /-- The energy of a state. -/
  energy : Ω → ℝ

namespace FiniteGibbs

variable {R Ω : Type*} [Lattice R] [DecidableEq Ω] (X : FiniteGibbs R Ω)

/-- The Boltzmann weight of a state. -/
noncomputable def weight (x : Ω) : ℝ :=
  Real.exp (-X.energy x)

theorem weight_pos (x : Ω) : 0 < X.weight x :=
  Real.exp_pos _

/-! ### Mass -/

/-- The mass of a finite set of states: its total Boltzmann weight. -/
noncomputable def mass (s : Finset Ω) : ℝ :=
  ∑ x ∈ s, X.weight x

theorem mass_nonneg (s : Finset Ω) : 0 ≤ X.mass s :=
  Finset.sum_nonneg fun x _ => (X.weight_pos x).le

theorem mass_pos {s : Finset Ω} (h : s.Nonempty) : 0 < X.mass s :=
  Finset.sum_pos (fun x _ => X.weight_pos x) h

theorem mass_eq_zero_iff {s : Finset Ω} : X.mass s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hs
    exact (X.mass_pos (Finset.nonempty_iff_ne_empty.mpr hs)).ne' h
  · rintro rfl
    simp [mass]

theorem mass_inter_add_mass_sdiff (s t : Finset Ω) :
    X.mass (s ∩ t) + X.mass (s \ t) = X.mass s := by
  have h := Finset.sum_sdiff (f := X.weight) (Finset.inter_subset_left (s₁ := s) (s₂ := t))
  rw [Finset.sdiff_inter_self_left] at h
  simp only [mass]
  linarith

theorem mass_union_add_mass_inter (s t : Finset Ω) :
    X.mass (s ∪ t) + X.mass (s ∩ t) = X.mass s + X.mass t :=
  Finset.sum_union_inter

/-- The exact multiplicative correction for masses: the product over two sets
exceeds the product over intersection and union by exactly the product of
the masses of the two differences. -/
theorem mass_mul_mass (s t : Finset Ω) :
    X.mass s * X.mass t
      = X.mass (s ∩ t) * X.mass (s ∪ t) + X.mass (s \ t) * X.mass (t \ s) := by
  have h1 := X.mass_inter_add_mass_sdiff s t
  have h2 := X.mass_inter_add_mass_sdiff t s
  have h3 := X.mass_union_add_mass_inter s t
  rw [Finset.inter_comm t s] at h2
  have hx : X.mass (s \ t) = X.mass s - X.mass (s ∩ t) := by linarith
  have hy : X.mass (t \ s) = X.mass t - X.mass (s ∩ t) := by linarith
  have hu : X.mass (s ∪ t) = X.mass s + X.mass t - X.mass (s ∩ t) := by linarith
  rw [hx, hy, hu]
  ring

/-! ### The partition function and the log-partition field -/

/-- The partition function: the mass of the state space. -/
noncomputable def partition : ContextField R ℝ :=
  fun r => X.mass (X.states r)

theorem partition_pos (r : R) : 0 < X.partition r :=
  X.mass_pos (X.states_nonempty r)

theorem partition_ne_zero (r : R) : X.partition r ≠ 0 :=
  (X.partition_pos r).ne'

/-- The log-partition field `K = log Z`, the field the realization presents
to the defect calculus. -/
noncomputable def logPartition : ContextField R ℝ :=
  fun r => Real.log (X.partition r)

/-- The state map, packaged as a lattice homomorphism into the
distributive lattice of finite sets. -/
def statesHom : LatticeHom R (Finset Ω) where
  toFun := X.states
  map_sup' a b := by
    rw [X.states_sup, Finset.sup_eq_union]
  map_inf' a b := by
    rw [X.states_inf, Finset.inf_eq_inter]

@[simp]
theorem statesHom_apply (r : R) : X.statesHom r = X.states r :=
  rfl

theorem states_mono {a b : R} (h : a ≤ b) : X.states a ⊆ X.states b := by
  have hab : X.states a = X.states a ∩ X.states b := by
    rw [← X.states_inf, inf_eq_left.mpr h]
  rw [hab]
  exact Finset.inter_subset_right

theorem partition_mono : Monotone X.partition := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (X.states_mono h)
    fun x _ _ => (X.weight_pos x).le

/-- Log-partitions are monotone fields. -/
theorem logPartition_mono : Monotone X.logPartition := fun a _ h =>
  Real.log_le_log (X.partition_pos a) (X.partition_mono h)

/-- The counting realization on a lattice homomorphism of state spaces: zero
energy, so the partition function is the counting measure. -/
def counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty)
    (hinf : ∀ a b, states (a ⊓ b) = states a ∩ states b)
    (hsup : ∀ a b, states (a ⊔ b) = states a ∪ states b) :
    FiniteGibbs R Ω :=
  ⟨states, h, hinf, hsup, fun _ => 0⟩

@[simp]
theorem states_counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty)
    (hinf : ∀ a b, states (a ⊓ b) = states a ∩ states b)
    (hsup : ∀ a b, states (a ⊔ b) = states a ∪ states b) :
    (counting states h hinf hsup).states = states :=
  rfl

theorem partition_counting (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty)
    (hinf : ∀ a b, states (a ⊓ b) = states a ∩ states b)
    (hsup : ∀ a b, states (a ⊔ b) = states a ∪ states b) (r : R) :
    (counting states h hinf hsup).partition r = (states r).card := by
  simp [partition, mass, counting, weight, Real.exp_zero]

/-! ### The recognition bridge -/

/-- The additive law of the class: the partition function of every
realization is a valuation. -/
theorem isValuation_partition : IsValuation X.partition := by
  intro a b
  have h := X.mass_union_add_mass_inter (X.states a) (X.states b)
  simp only [defect, partition, X.states_inf, X.states_sup]
  linarith

/-- The additive recognition law: partition functions land in the gauge. -/
theorem partition_mem_gauge : X.partition ∈ gauge R ℝ :=
  mem_gauge_iff.mpr X.isValuation_partition

theorem exp_logPartition (r : R) : Real.exp (X.logPartition r) = X.partition r :=
  Real.exp_log (X.partition_pos r)

theorem exp_comp_logPartition : Real.exp ∘ X.logPartition = X.partition :=
  funext X.exp_logPartition

/-- The additive law in field coordinates: the exponential of every
log-partition is a valuation. -/
theorem isValuation_exp_logPartition : IsValuation (Real.exp ∘ X.logPartition) := by
  rw [X.exp_comp_logPartition]
  exact X.isValuation_partition

/-- The recognition identity: the pairwise defect of the log-partition field
is the logarithm of the multiplicativity ratio of the partition function. -/
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

/-- The log-partition satisfies the valuation law at a square exactly when
the partition function multiplies across it. -/
theorem defect_logPartition_eq_zero_iff_mul {a b : R} :
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

/-- The exact multiplicative correction: across a comparison square the
product of partition functions is the product at meet and join plus the
masses of the two state-space differences. -/
theorem partition_mul_partition (a b : R) :
    X.partition a * X.partition b
      = X.partition (a ⊓ b) * X.partition (a ⊔ b)
        + X.mass (X.states a \ X.states b) * X.mass (X.states b \ X.states a) := by
  simp only [partition, X.states_inf, X.states_sup]
  exact X.mass_mul_mass _ _

/-- The universal sign of the class: the defect of a log-partition is
nonnegative. -/
theorem defect_logPartition_nonneg (a b : R) : 0 ≤ defect X.logPartition a b := by
  rw [X.defect_logPartition a b]
  refine Real.log_nonneg ?_
  rw [one_le_div (mul_pos (X.partition_pos (a ⊓ b)) (X.partition_pos (a ⊔ b))),
    X.partition_mul_partition a b]
  have h := mul_nonneg (X.mass_nonneg (X.states a \ X.states b))
    (X.mass_nonneg (X.states b \ X.states a))
  linarith

/-- The sharp vanishing law: the defect of the log-partition vanishes at a
square exactly when the state spaces are nested. -/
theorem defect_logPartition_eq_zero_iff_subset {a b : R} :
    defect X.logPartition a b = 0 ↔
      X.states a ⊆ X.states b ∨ X.states b ⊆ X.states a := by
  rw [X.defect_logPartition_eq_zero_iff_mul, X.partition_mul_partition a b,
    add_eq_left, mul_eq_zero, X.mass_eq_zero_iff, X.mass_eq_zero_iff,
    Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset]

/-- The log-partition is a valuation exactly when every pair of state spaces
is nested. -/
theorem isValuation_logPartition_iff :
    IsValuation X.logPartition ↔
      ∀ a b, X.states a ⊆ X.states b ∨ X.states b ⊆ X.states a :=
  forall₂_congr fun _ _ => X.defect_logPartition_eq_zero_iff_subset

/-- Zero defect is degenerate: it forces the partition function at the meet
to agree with one of the sides, so nothing in this class factors
nontrivially. -/
theorem partition_inf_eq_of_defect_eq_zero {a b : R}
    (h : defect X.logPartition a b = 0) :
    X.partition (a ⊓ b) = X.partition a ∨ X.partition (a ⊓ b) = X.partition b := by
  rcases X.defect_logPartition_eq_zero_iff_subset.mp h with hs | hs
  · left
    show X.mass (X.states (a ⊓ b)) = X.mass (X.states a)
    rw [X.states_inf, Finset.inter_eq_left.mpr hs]
  · right
    show X.mass (X.states (a ⊓ b)) = X.mass (X.states b)
    rw [X.states_inf, Finset.inter_comm, Finset.inter_eq_left.mpr hs]

/-- The class is genuinely restrictive already on the two-element chain:
log-partitions are monotone, so an explicit non-monotone field is the
log-partition of no realization, over any state carrier. -/
theorem exists_not_logPartition :
    ∃ K : ContextField Bool ℝ,
      ∀ {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Bool Ω'),
        X'.logPartition ≠ K := by
  refine ⟨fun b => cond b 0 1, fun {Ω'} _ X' h => ?_⟩
  have hm := X'.logPartition_mono (Bool.false_le true)
  rw [h] at hm
  norm_num at hm

/-! ### The energy zero point is gauge -/

/-- Shifting the energy zero point. -/
def shift (c : ℝ) : FiniteGibbs R Ω :=
  ⟨X.states, X.states_nonempty, X.states_inf, X.states_sup,
    fun x => X.energy x + c⟩

@[simp]
theorem states_shift (c : ℝ) : (X.shift c).states = X.states :=
  rfl

theorem weight_shift (c : ℝ) (x : Ω) :
    (X.shift c).weight x = Real.exp (-c) * X.weight x := by
  simp [weight, shift, Real.exp_add]

theorem partition_shift (c : ℝ) (r : R) :
    (X.shift c).partition r = Real.exp (-c) * X.partition r := by
  simp [partition, mass, weight_shift, Finset.mul_sum]

theorem logPartition_shift (c : ℝ) (r : R) :
    (X.shift c).logPartition r = X.logPartition r - c := by
  rw [logPartition, partition_shift,
    Real.log_mul (Real.exp_ne_zero _) (X.partition_ne_zero r), Real.log_exp,
    neg_add_eq_sub]
  rfl

/-- Shifting the energy zero point moves the log-partition by a constant
field, which is a valuation: the defect observable cannot see the zero
point. -/
theorem defectEquiv_logPartition_shift (c : ℝ) :
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

/-- Pulling a realization back along a lattice homomorphism of context
systems. -/
def comap {R' : Type*} [Lattice R'] (f : LatticeHom R' R) : FiniteGibbs R' Ω where
  states r := X.states (f r)
  states_nonempty r := X.states_nonempty (f r)
  states_inf a b := by rw [map_inf]; exact X.states_inf (f a) (f b)
  states_sup a b := by rw [map_sup]; exact X.states_sup (f a) (f b)
  energy := X.energy

@[simp]
theorem partition_comap {R' : Type*} [Lattice R'] (f : LatticeHom R' R) :
    (X.comap f).partition = X.partition ∘ f :=
  rfl

@[simp]
theorem logPartition_comap {R' : Type*} [Lattice R'] (f : LatticeHom R' R) :
    (X.comap f).logPartition = X.logPartition ∘ f :=
  rfl

/-- Realization-level naturality: pulling back along a lattice homomorphism
pulls the defect observable back with it. -/
theorem defect_logPartition_comap {R' : Type*} [Lattice R']
    (f : LatticeHom R' R) (a b : R') :
    defect (X.comap f).logPartition a b = defect X.logPartition (f a) (f b) := by
  rw [logPartition_comap]
  exact defect_comp f X.logPartition a b

/-! ### Disjoint sums -/

section DisjSum

variable {Ψ : Type*} [DecidableEq Ψ] (Y : FiniteGibbs R Ψ)

/-- The disjoint sum of two realizations over the same context system: the
juxtaposition that stays in the class, adding state spaces. -/
def disjSum : FiniteGibbs R (Ω ⊕ Ψ) where
  states r := (X.states r).disjSum (Y.states r)
  states_nonempty r := by
    obtain ⟨x, hx⟩ := X.states_nonempty r
    exact ⟨Sum.inl x, Finset.inl_mem_disjSum.mpr hx⟩
  states_inf a b := by
    rw [X.states_inf, Y.states_inf]
    ext x
    cases x <;> simp
  states_sup a b := by
    rw [X.states_sup, Y.states_sup]
    ext x
    cases x <;> simp
  energy := Sum.elim X.energy Y.energy

@[simp]
theorem states_disjSum (r : R) :
    (X.disjSum Y).states r = (X.states r).disjSum (Y.states r) :=
  rfl

/-- The partition function of a disjoint sum adds. -/
theorem partition_disjSum (r : R) :
    (X.disjSum Y).partition r = X.partition r + Y.partition r := by
  simp only [partition, mass, states_disjSum, Finset.sum_disjSum]
  rfl

end DisjSum

end FiniteGibbs

end Descent
