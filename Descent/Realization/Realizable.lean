import Descent.Models.Chain
import Descent.Models.Square
import Descent.Realization.FiniteGibbs
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable

/-!
# Realizability

The inverse problem for the finite Gibbs class: which fields are
log-partitions?

`Realizable K` names the datum: a realization whose log-partition is exactly
`K`. The necessary conditions are the M4 laws read in field coordinates ---
`K` is monotone, `Real.exp ∘ K` is a valuation, the defect of `K` is
nonnegative --- and positivity is absorbed by the exponential.

The results separate the axes of the inverse problem:

* order and algebra are jointly sufficient on the minimal chain
  (`realizable_bool_iff`: realizable exactly when monotone, the valuation
  law being vacuous on a chain) and on the square (`Square.realizable_iff`:
  realizable exactly when monotone and exponentially a valuation);
* they are not sufficient in general: on the chain `ℝ` the identity field
  is monotone and exponentially a valuation, but no family of finite state
  spaces grows strictly along an uncountable chain
  (`exists_monotone_isValuation_not_realizable`) --- finiteness is a
  separate axis;
* uniqueness lives at the level of the partition function alone: the field
  determines it (`partition_eq_of_logPartition_eq`), while distinct
  realizations share a log-partition (`exists_logPartition_eq_of_ne`) and
  distinct fields share defect data (`exists_defectEquiv_logPartition_ne`).
-/

namespace Descent

open FiniteGibbs

variable {R : Type*} [Lattice R]

/-- `K` is realizable when it is the log-partition of a finite Gibbs
realization. The negative results of this development are proved in the
stronger form `∀ Ω, X.logPartition ≠ K`, over state carriers in every
universe. -/
def Realizable (K : ContextField R ℝ) : Prop :=
  ∃ (Ω : Type) (_ : DecidableEq Ω) (X : FiniteGibbs R Ω), X.logPartition = K

/-- Order compatibility is necessary: realizable fields are monotone. -/
theorem Realizable.monotone {K : ContextField R ℝ} (h : Realizable K) : Monotone K := by
  obtain ⟨Ω, _, X, rfl⟩ := h
  exact X.logPartition_mono

/-- Algebraic compatibility is necessary: realizable fields are
exponentially valuations. -/
theorem Realizable.isValuation_exp {K : ContextField R ℝ} (h : Realizable K) :
    IsValuation (Real.exp ∘ K) := by
  obtain ⟨Ω, _, X, rfl⟩ := h
  exact X.isValuation_exp_logPartition

/-- The universal sign, as a necessary condition on the field datum. -/
theorem Realizable.defect_nonneg {K : ContextField R ℝ} (h : Realizable K) (a b : R) :
    0 ≤ defect K a b := by
  obtain ⟨Ω, _, X, rfl⟩ := h
  exact X.defect_logPartition_nonneg a b

/-! ### The minimal chain

On `Bool` the valuation law is vacuous, and realizability is exactly the
order condition. -/

section BoolChain

variable (K : ContextField Bool ℝ)

open Classical in
private noncomputable def boolStates (b : Bool) : Finset (Fin 2) :=
  Finset.univ.filter fun x => x = 0 ∨ x = 1 ∧ K false < K true ∧ b = true

private theorem mem_boolStates {x : Fin 2} {b : Bool} :
    x ∈ boolStates K b ↔ x = 0 ∨ x = 1 ∧ K false < K true ∧ b = true := by
  classical
  simp [boolStates]

private theorem boolStates_inf (a b : Bool) :
    boolStates K (a ⊓ b) = boolStates K a ∩ boolStates K b := by
  ext x
  simp only [Finset.mem_inter, mem_boolStates,
    show ∀ u v : Bool, u ⊓ v = true ↔ u = true ∧ v = true from by decide]
  tauto

private theorem boolStates_sup (a b : Bool) :
    boolStates K (a ⊔ b) = boolStates K a ∪ boolStates K b := by
  ext x
  simp only [Finset.mem_union, mem_boolStates,
    show ∀ u v : Bool, u ⊔ v = true ↔ u = true ∨ v = true from by decide]
  tauto

private noncomputable def boolGibbs : FiniteGibbs Bool (Fin 2) where
  states := boolStates K
  states_nonempty := fun _ => ⟨0, (mem_boolStates K).mpr (Or.inl rfl)⟩
  states_inf := boolStates_inf K
  states_sup := boolStates_sup K
  energy := fun x =>
    if x = 0 then -K false else -Real.log (Real.exp (K true) - Real.exp (K false))

private theorem weight_boolGibbs_zero : (boolGibbs K).weight 0 = Real.exp (K false) := by
  simp [weight, boolGibbs]

private theorem weight_boolGibbs_one (h : K false < K true) :
    (boolGibbs K).weight 1 = Real.exp (K true) - Real.exp (K false) := by
  have h1 : (0 : ℝ) < Real.exp (K true) - Real.exp (K false) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr h)
  simp [weight, boolGibbs, Real.exp_log h1]

private theorem partition_boolGibbs_false :
    (boolGibbs K).partition false = Real.exp (K false) := by
  have hs : boolStates K false = {0} := by
    ext x
    simp [mem_boolStates]
  show (boolGibbs K).mass (boolStates K false) = _
  rw [hs]
  simp only [mass, Finset.sum_singleton]
  exact weight_boolGibbs_zero K

private theorem partition_boolGibbs_true (h : K false ≤ K true) :
    (boolGibbs K).partition true = Real.exp (K true) := by
  show (boolGibbs K).mass (boolStates K true) = _
  rcases eq_or_lt_of_le h with heq | hlt
  · have hs : boolStates K true = {0} := by
      ext x
      simp [mem_boolStates, not_lt.mpr heq.ge]
    rw [hs]
    simp only [mass, Finset.sum_singleton]
    rw [weight_boolGibbs_zero, heq]
  · have hs : boolStates K true = {0, 1} := by
      ext x
      simp [mem_boolStates, hlt]
    rw [hs]
    simp only [mass]
    rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), weight_boolGibbs_zero,
      weight_boolGibbs_one K hlt]
    ring

/-- Realizability on the minimal chain is exactly the order condition: on a
chain the valuation law is vacuous, and monotonicity alone is sharp. -/
theorem realizable_bool_iff {K : ContextField Bool ℝ} :
    Realizable K ↔ K false ≤ K true := by
  constructor
  · exact fun h => h.monotone (Bool.false_le true)
  · intro h
    refine ⟨Fin 2, inferInstance, boolGibbs K, funext fun b => ?_⟩
    cases b
    · show Real.log ((boolGibbs K).partition false) = K false
      rw [partition_boolGibbs_false, Real.log_exp]
    · show Real.log ((boolGibbs K).partition true) = K true
      rw [partition_boolGibbs_true K h, Real.log_exp]

end BoolChain

/-! ### The square

On the square the necessary order and algebra conditions are jointly
sufficient: a monotone, exponentially-valuation field is realized by a
three-state carrier --- one shared state, one state private to each side of
the nondegenerate square, included exactly when its side strictly increases
mass. -/

namespace Square

private theorem left_le_sup_iff (a b : Square) :
    left ≤ a ⊔ b ↔ left ≤ a ∨ left ≤ b := by
  revert a b; decide

private theorem right_le_sup_iff (a b : Square) :
    right ≤ a ⊔ b ↔ right ≤ a ∨ right ≤ b := by
  revert a b; decide

variable (K : ContextField Square ℝ)

open Classical in
private noncomputable def sqStates (p : Square) : Finset (Fin 3) :=
  Finset.univ.filter fun x =>
    x = 0 ∨ x = 1 ∧ K ⊥ < K left ∧ left ≤ p ∨ x = 2 ∧ K ⊥ < K right ∧ right ≤ p

private theorem mem_sqStates {x : Fin 3} {p : Square} :
    x ∈ sqStates K p ↔
      x = 0 ∨ x = 1 ∧ K ⊥ < K left ∧ left ≤ p ∨ x = 2 ∧ K ⊥ < K right ∧ right ≤ p := by
  classical
  simp [sqStates]

private theorem sqStates_inf (a b : Square) :
    sqStates K (a ⊓ b) = sqStates K a ∩ sqStates K b := by
  ext x
  simp only [Finset.mem_inter, mem_sqStates, le_inf_iff]
  fin_cases x <;> simp <;> tauto

private theorem sqStates_sup (a b : Square) :
    sqStates K (a ⊔ b) = sqStates K a ∪ sqStates K b := by
  ext x
  simp only [Finset.mem_union, mem_sqStates, left_le_sup_iff, right_le_sup_iff]
  fin_cases x <;> simp <;> tauto

private noncomputable def sqGibbs : FiniteGibbs Square (Fin 3) where
  states := sqStates K
  states_nonempty := fun _ => ⟨0, (mem_sqStates K).mpr (Or.inl rfl)⟩
  states_inf := sqStates_inf K
  states_sup := sqStates_sup K
  energy := fun x =>
    if x = 0 then -K ⊥
    else if x = 1 then -Real.log (Real.exp (K left) - Real.exp (K ⊥))
    else -Real.log (Real.exp (K right) - Real.exp (K ⊥))

private theorem weight_sqGibbs_zero : (sqGibbs K).weight 0 = Real.exp (K ⊥) := by
  simp [weight, sqGibbs]

private theorem weight_sqGibbs_one (h : K ⊥ < K left) :
    (sqGibbs K).weight 1 = Real.exp (K left) - Real.exp (K ⊥) := by
  have h1 : (0 : ℝ) < Real.exp (K left) - Real.exp (K ⊥) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr h)
  simp [weight, sqGibbs, Real.exp_log h1]

private theorem weight_sqGibbs_two (h : K ⊥ < K right) :
    (sqGibbs K).weight 2 = Real.exp (K right) - Real.exp (K ⊥) := by
  have h2 : (0 : ℝ) < Real.exp (K right) - Real.exp (K ⊥) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr h)
  simp [weight, sqGibbs, Real.exp_log h2]

private theorem partition_sqGibbs_bot : (sqGibbs K).partition ⊥ = Real.exp (K ⊥) := by
  have hs : sqStates K ⊥ = {0} := by
    ext x
    simp [mem_sqStates, show ¬left ≤ (⊥ : Square) from by decide,
      show ¬right ≤ (⊥ : Square) from by decide]
  show (sqGibbs K).mass (sqStates K ⊥) = _
  rw [hs]
  simp only [mass, Finset.sum_singleton]
  exact weight_sqGibbs_zero K

private theorem partition_sqGibbs_left (h : K ⊥ ≤ K left) :
    (sqGibbs K).partition left = Real.exp (K left) := by
  show (sqGibbs K).mass (sqStates K left) = _
  rcases eq_or_lt_of_le h with heq | hlt
  · have hs : sqStates K left = {0} := by
      ext x
      simp [mem_sqStates, not_lt.mpr heq.ge, show ¬right ≤ left from by decide]
    rw [hs]
    simp only [mass, Finset.sum_singleton]
    rw [weight_sqGibbs_zero, heq]
  · have hs : sqStates K left = {0, 1} := by
      ext x
      simp [mem_sqStates, hlt, show ¬right ≤ left from by decide]
    rw [hs]
    simp only [mass]
    rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), weight_sqGibbs_zero,
      weight_sqGibbs_one K hlt]
    ring

private theorem partition_sqGibbs_right (h : K ⊥ ≤ K right) :
    (sqGibbs K).partition right = Real.exp (K right) := by
  show (sqGibbs K).mass (sqStates K right) = _
  rcases eq_or_lt_of_le h with heq | hlt
  · have hs : sqStates K right = {0} := by
      ext x
      simp [mem_sqStates, not_lt.mpr heq.ge, show ¬left ≤ right from by decide]
    rw [hs]
    simp only [mass, Finset.sum_singleton]
    rw [weight_sqGibbs_zero, heq]
  · have hs : sqStates K right = {0, 2} := by
      ext x
      simp [mem_sqStates, hlt, show ¬left ≤ right from by decide]
    rw [hs]
    simp only [mass]
    rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2), weight_sqGibbs_zero,
      weight_sqGibbs_two K hlt]
    ring

private theorem partition_sqGibbs_top (hm : Monotone K)
    (hv : Real.exp (K left) + Real.exp (K right) = Real.exp (K ⊥) + Real.exp (K ⊤)) :
    (sqGibbs K).partition ⊤ = Real.exp (K ⊤) := by
  show (sqGibbs K).mass (sqStates K ⊤) = _
  rcases eq_or_lt_of_le (hm (bot_le : (⊥ : Square) ≤ left)) with hleq | hllt <;>
    rcases eq_or_lt_of_le (hm (bot_le : (⊥ : Square) ≤ right)) with hreq | hrlt
  · have hs : sqStates K ⊤ = {0} := by
      ext x
      simp [mem_sqStates, not_lt.mpr hleq.ge, not_lt.mpr hreq.ge]
    rw [hs]
    simp only [mass, Finset.sum_singleton]
    rw [weight_sqGibbs_zero]
    rw [← hleq, ← hreq] at hv
    linarith
  · have hs : sqStates K ⊤ = {0, 2} := by
      ext x
      simp [mem_sqStates, not_lt.mpr hleq.ge, hrlt, show right ≤ (⊤ : Square) from le_top]
    rw [hs]
    simp only [mass]
    rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2), weight_sqGibbs_zero,
      weight_sqGibbs_two K hrlt]
    rw [← hleq] at hv
    linarith
  · have hs : sqStates K ⊤ = {0, 1} := by
      ext x
      simp [mem_sqStates, not_lt.mpr hreq.ge, hllt, show left ≤ (⊤ : Square) from le_top]
    rw [hs]
    simp only [mass]
    rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), weight_sqGibbs_zero,
      weight_sqGibbs_one K hllt]
    rw [← hreq] at hv
    linarith
  · have hs : sqStates K ⊤ = {0, 1, 2} := by
      ext x
      simp [mem_sqStates, hllt, hrlt, show left ≤ (⊤ : Square) from le_top,
        show right ≤ (⊤ : Square) from le_top]
    rw [hs, show ({0, 1, 2} : Finset (Fin 3)) = Finset.univ from by decide]
    simp only [mass]
    rw [Fin.sum_univ_three, weight_sqGibbs_zero, weight_sqGibbs_one K hllt,
      weight_sqGibbs_two K hrlt]
    linarith

private theorem partition_sqGibbs (hm : Monotone K)
    (hv : Real.exp (K left) + Real.exp (K right) = Real.exp (K ⊥) + Real.exp (K ⊤))
    (p : Square) : (sqGibbs K).partition p = Real.exp (K p) := by
  rcases p with ⟨_ | _, _ | _⟩
  · rw [show ((false, false) : Square) = ⊥ from by decide]
    exact partition_sqGibbs_bot K
  · rw [show ((false, true) : Square) = right from by decide]
    exact partition_sqGibbs_right K (hm bot_le)
  · rw [show ((true, false) : Square) = left from by decide]
    exact partition_sqGibbs_left K (hm bot_le)
  · rw [show ((true, true) : Square) = ⊤ from by decide]
    exact partition_sqGibbs_top K hm hv

/-- Realizability on the square, characterized: exactly the monotone fields
that are exponentially valuations. Positivity is absorbed by the
exponential; order and algebra are the entire obstruction. -/
theorem realizable_iff {K : ContextField Square ℝ} :
    Realizable K ↔ Monotone K ∧ IsValuation (Real.exp ∘ K) := by
  constructor
  · exact fun h => ⟨h.monotone, h.isValuation_exp⟩
  · rintro ⟨hm, hv⟩
    have hv' : Real.exp (K left) + Real.exp (K right)
        = Real.exp (K ⊥) + Real.exp (K ⊤) := isValuation_iff.mp hv
    refine ⟨Fin 3, inferInstance, sqGibbs K, funext fun p => ?_⟩
    show Real.log ((sqGibbs K).partition p) = K p
    rw [partition_sqGibbs K hm hv' p, Real.log_exp]

end Square

/-! ### Finiteness

Order and algebra are not the entire obstruction in general. On the chain
`ℝ` every field is exponentially a valuation and the identity field is
monotone, but a realization of it would need finite state spaces growing
strictly along an uncountable chain, and no such family exists. In the
finite class, the analytic axis of the inverse problem appears as this
finiteness obstruction. -/

/-- The identity field on the chain `ℝ` is the log-partition of no
realization over any state carrier: its partition function would be
strictly monotone, forcing strictly growing finite state spaces along an
uncountable chain. -/
theorem id_not_logPartition {Ω : Type*} [DecidableEq Ω] (X : FiniteGibbs ℝ Ω) :
    X.logPartition ≠ id := by
  intro h
  have hcard : StrictMono fun x : ℝ => (X.states x).card := by
    intro a b hab
    refine Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨X.states_mono hab.le, fun he => ?_⟩)
    have hZ : X.partition a = X.partition b := congrArg X.mass he
    have ha : X.partition a = Real.exp a := by rw [← X.exp_logPartition, congrFun h a, id_eq]
    have hb : X.partition b = Real.exp b := by rw [← X.exp_logPartition, congrFun h b, id_eq]
    rw [ha, hb] at hZ
    exact absurd hZ (Real.exp_lt_exp.mpr hab).ne
  exact not_countable ((countable_iff_exists_injective ℝ).mpr ⟨_, hcard.injective⟩)

/-- Monotonicity and the exponential valuation law do not characterize
realizability in general: on the chain `ℝ` both hold of the identity field,
and finiteness obstructs anyway. -/
theorem exists_monotone_isValuation_not_realizable :
    ∃ K : ContextField ℝ ℝ, Monotone K ∧ IsValuation (Real.exp ∘ K) ∧ ¬Realizable K := by
  refine ⟨id, monotone_id, isValuation_of_linearOrder _, fun h => ?_⟩
  obtain ⟨Ω, _, X, hX⟩ := h
  exact id_not_logPartition X hX

/-! ### Uniqueness

The field datum determines the partition function and nothing more:
distinct realizations share a log-partition, and distinct fields share
defect data. Uniqueness in the inverse problem lives at the level of the
partition function alone. -/

section Uniqueness

variable {Ω Ψ : Type*} [DecidableEq Ω] [DecidableEq Ψ]

/-- The field datum determines the partition function. -/
theorem partition_eq_of_logPartition_eq {X : FiniteGibbs R Ω} {Y : FiniteGibbs R Ψ}
    (h : X.logPartition = Y.logPartition) : X.partition = Y.partition := by
  funext r
  rw [← X.exp_logPartition, ← Y.exp_logPartition, h]

private noncomputable def pair (e₀ e₁ : ℝ) : FiniteGibbs Bool (Fin 2) where
  states := fun _ => {0, 1}
  states_nonempty := fun _ => ⟨0, by decide⟩
  states_inf := fun _ _ => (Finset.inter_self _).symm
  states_sup := fun _ _ => (Finset.union_self _).symm
  energy := fun x => if x = 0 then e₀ else e₁

private theorem partition_pair (e₀ e₁ : ℝ) (b : Bool) :
    (pair e₀ e₁).partition b = Real.exp (-e₀) + Real.exp (-e₁) := by
  show (pair e₀ e₁).mass {0, 1} = _
  simp only [mass]
  rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
  simp [weight, pair]

/-- The field datum does not determine the realization: two realizations
with the same log-partition and different energies. -/
theorem exists_logPartition_eq_of_ne :
    ∃ X X' : FiniteGibbs Bool (Fin 2), X.logPartition = X'.logPartition ∧ X ≠ X' := by
  refine ⟨pair 0 0, pair (-Real.log (3 / 2)) (-Real.log (1 / 2)),
    funext fun b => ?_, fun h => ?_⟩
  · show Real.log ((pair 0 0).partition b) = Real.log ((pair _ _).partition b)
    rw [partition_pair, partition_pair, neg_zero, Real.exp_zero, neg_neg, neg_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  · have hE := congrArg (fun X : FiniteGibbs Bool (Fin 2) => X.energy 0) h
    simp only [pair] at hE
    rw [if_true, if_true] at hE
    have h32 : Real.log (3 / 2) = 0 := by linarith
    rcases Real.log_eq_zero.mp h32 with h' | h' | h' <;> norm_num at h'

/-- Defect data does not determine the field, even within the realizable
class: a realization and its shift share defect data and differ as
fields. -/
theorem exists_defectEquiv_logPartition_ne :
    ∃ X X' : FiniteGibbs Bool (Fin 2),
      DefectEquiv X.logPartition X'.logPartition ∧ X.logPartition ≠ X'.logPartition := by
  refine ⟨(pair 0 0).shift 1, pair 0 0, defectEquiv_logPartition_shift _ 1, fun h => ?_⟩
  have h0 := congrFun h false
  rw [logPartition_shift] at h0
  linarith

end Uniqueness

end Descent
