import Descent.Reconstruction.Normalization
import Descent.Reconstruction.Restricted
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Module

/-!
# The square

`Bool × Bool` is the four-element Boolean lattice: `⊥`, `⊤`, and the
incomparable pair `left`, `right`. Its pairwise defect theory is solved
completely, and the classifications are sharp:

* the valuation law is the single relation `K left + K right = K ⊥ + K ⊤`
  (`isValuation_iff`), and for a nontrivial target it has strict failures;
* for a nontrivial target, a family of squares is observationally complete
  exactly when it observes the one nondegenerate square, in either order
  (`observationallyComplete_iff`): the singleton `{(left, right)}` is
  complete with no hypothesis on the target, and no family of degenerate
  squares is;
* for a nontrivial target, a value restriction is adequate exactly when it
  misses at most one context (`adequateOn_iff`): three values determine the
  fourth through the valuation relation, two never do;
* reconstruction is an explicit formula (`reconstruct_defect`), not only an
  injectivity statement.
-/

namespace Descent

/-- The four-element Boolean lattice of contexts. -/
abbrev Square := Bool × Bool

namespace Square

/-- One of the two incomparable contexts. -/
def left : Square := (true, false)

/-- The other incomparable context. -/
def right : Square := (false, true)

private theorem bot_def : (⊥ : Square) = (false, false) := by decide

private theorem top_def : (⊤ : Square) = (true, true) := by decide

theorem comparable_or (a b : Square) :
    Comparable a b ∨ (a = left ∧ b = right) ∨ (a = right ∧ b = left) := by
  revert a b
  decide

/-- Monotonicity on the square is the four edge inequalities. -/
theorem monotone_iff {α : Type*} [Preorder α] {f : Square → α} :
    Monotone f ↔ f ⊥ ≤ f left ∧ f ⊥ ≤ f right ∧ f left ≤ f ⊤ ∧ f right ≤ f ⊤ := by
  constructor
  · intro h
    exact ⟨h bot_le, h bot_le, h le_top, h le_top⟩
  · rintro ⟨h1, h2, h3, h4⟩ a b hab
    have hcases : a = b ∨ a = ⊥ ∧ b = left ∨ a = ⊥ ∧ b = right ∨ a = ⊥ ∧ b = ⊤ ∨
        a = left ∧ b = ⊤ ∨ a = right ∧ b = ⊤ := by
      revert a b
      decide
    rcases hcases with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_refl _
    · exact h1
    · exact h2
    · exact h1.trans h3
    · exact h3
    · exact h4

variable {A : Type*} [AddCommGroup A]

theorem defect_left_right (K : ContextField Square A) :
    defect K left right = K left + K right - K ⊥ - K ⊤ := by
  rw [defect_def, show left ⊓ right = (⊥ : Square) from by decide,
    show left ⊔ right = (⊤ : Square) from by decide]

/-- The square defect datum carrying value `d` at the nondegenerate square,
zero elsewhere. Every pairwise defect on the square is of this form. -/
def defectData (d : A) : Square → Square → A := fun a b =>
  if a = left ∧ b = right ∨ a = right ∧ b = left then d else 0

theorem defectData_left_right (d : A) : defectData d left right = d :=
  if_pos (Or.inl ⟨rfl, rfl⟩)

/-- On the square the pairwise defect observable is one number: the defect
of any field is the datum carrying its value at the nondegenerate square. -/
theorem defect_eq_defectData (K : ContextField Square A) :
    defect K = defectData (defect K left right) := by
  funext a b
  rcases comparable_or a b with hab | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hne : ¬(a = left ∧ b = right ∨ a = right ∧ b = left) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact (by decide : ¬Comparable left right) hab
      · exact (by decide : ¬Comparable right left) hab
    rw [hab.defect_eq_zero K]
    exact (if_neg hne).symm
  · exact (defectData_left_right _).symm
  · rw [defect_comm K right left]
    exact (if_pos (Or.inr ⟨rfl, rfl⟩)).symm

/-- The valuation law on the square is one relation. -/
theorem isValuation_iff {K : ContextField Square A} :
    IsValuation K ↔ K left + K right = K ⊥ + K ⊤ := by
  constructor
  · intro h
    have h0 := h left right
    rwa [defect_left_right, sub_sub, sub_eq_zero] at h0
  · intro h a b
    rcases comparable_or a b with hab | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab.defect_eq_zero K
    · rw [defect_left_right, sub_sub, sub_eq_zero]
      exact h
    · rw [defect_comm, defect_left_right, sub_sub, sub_eq_zero]
      exact h

/-- The valuation law has strict failures on the square. -/
theorem exists_not_isValuation [Nontrivial A] :
    ∃ K : ContextField Square A, ¬IsValuation K := by
  classical
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  refine ⟨Pi.single ⊤ e, fun h => he ?_⟩
  have h0 := isValuation_iff.mp h
  simpa [Pi.single_apply, left, right, bot_def, top_def, Prod.ext_iff]
    using h0.symm

/-! ### Observational completeness -/

/-- Observing the one nondegenerate square is enough. -/
theorem observationallyComplete_of_mem {S : Set (Square × Square)}
    (h : (left, right) ∈ S ∨ (right, left) ∈ S) :
    ObservationallyComplete S A := by
  refine observationallyComplete_iff_le.mpr fun K hK =>
    mem_gauge_iff.mpr (isValuation_iff.mpr ?_)
  rcases h with h | h
  · have h0 : defect K left right = 0 := mem_gaugeOn_iff.mp hK (left, right) h
    rwa [defect_left_right, sub_sub, sub_eq_zero] at h0
  · have h0 : defect K right left = 0 := mem_gaugeOn_iff.mp hK (right, left) h
    rwa [defect_comm, defect_left_right, sub_sub, sub_eq_zero] at h0

/-- One square suffices: the sparsest complete family. -/
theorem observationallyComplete_singleton :
    ObservationallyComplete ({(left, right)} : Set (Square × Square)) A :=
  observationallyComplete_of_mem (Or.inl rfl)

/-- Sharp observational completeness on the square: a family is complete
exactly when it observes the one nondegenerate square, in either order. -/
theorem observationallyComplete_iff [Nontrivial A] {S : Set (Square × Square)} :
    ObservationallyComplete S A ↔ (left, right) ∈ S ∨ (right, left) ∈ S := by
  refine ⟨fun h => ?_, observationallyComplete_of_mem⟩
  by_contra hS
  rw [not_or] at hS
  have hcomp : ∀ p ∈ S, Comparable (Prod.fst p) (Prod.snd p) := by
    intro p hp
    rcases comparable_or p.1 p.2 with hc | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hc
    · exact absurd
        (show (left, right) ∈ S from
          (Prod.ext_iff.mpr ⟨h1, h2⟩ : p = (left, right)) ▸ hp) hS.1
    · exact absurd
        (show (right, left) ∈ S from
          (Prod.ext_iff.mpr ⟨h1, h2⟩ : p = (right, left)) ▸ hp) hS.2
  obtain ⟨K, hK⟩ := exists_not_isValuation (A := A)
  refine hK (mem_gauge_iff.mp ?_)
  have h' : gaugeOn S A = gauge Square A := h
  rw [← h', gaugeOn_eq_top_of_comparable hcomp]
  exact AddSubgroup.mem_top K

/-! ### Normalization -/

/-- The sign with which a context enters the valuation relation. -/
private def sgn (p : Square) : ℤ := if p.1 = p.2 then -1 else 1

private theorem single_relation {f : ContextField Square A} {p : Square} {c : A}
    (hf : f = Pi.single p c) :
    f left + f right - f ⊥ - f ⊤ = sgn p • c := by
  subst hf
  rcases p with ⟨_ | _, _ | _⟩ <;>
    simp [sgn, left, right, bot_def, top_def, Prod.ext_iff]

/-- A nonzero valuation supported on two prescribed contexts: the obstruction
to any two-context normalization. -/
private theorem exists_valuation_pair {r s : Square} (hrs : r ≠ s) {e : A}
    (he : e ≠ 0) :
    ∃ G : ContextField Square A,
      IsValuation G ∧ G ≠ 0 ∧ ∀ t, t ≠ r → t ≠ s → G t = 0 := by
  classical
  set f : ContextField Square A := Pi.single r e with hf
  set g : ContextField Square A := Pi.single s e with hg
  refine ⟨sgn s • f - sgn r • g, ?_, ?_, ?_⟩
  · rw [isValuation_iff, ← sub_eq_zero]
    calc (sgn s • f - sgn r • g) left + (sgn s • f - sgn r • g) right
          - ((sgn s • f - sgn r • g) ⊥ + (sgn s • f - sgn r • g) ⊤)
        = sgn s • (f left + f right - f ⊥ - f ⊤)
          - sgn r • (g left + g right - g ⊥ - g ⊤) := by
          simp only [Pi.sub_apply, Pi.smul_apply]
          module
      _ = sgn s • (sgn r • e) - sgn r • (sgn s • e) := by
          rw [single_relation hf, single_relation hg]
      _ = 0 := by
          rw [smul_smul, smul_smul, mul_comm (sgn s) (sgn r), sub_self]
  · intro hG0
    have hr := congrFun hG0 r
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hf, hg, Pi.single_eq_same,
      Pi.single_eq_of_ne hrs, smul_zero, sub_zero, Pi.zero_apply] at hr
    by_cases hs : s.1 = s.2
    · rw [show sgn s = -1 from if_pos hs, neg_one_zsmul, neg_eq_zero] at hr
      exact he hr
    · rw [show sgn s = 1 from if_neg hs, one_smul] at hr
      exact he hr
  · intro t htr hts
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hf, hg,
      Pi.single_eq_of_ne htr, Pi.single_eq_of_ne hts, smul_zero, smul_zero,
      sub_zero]

/-- Missing at most one context is adequate: three values determine the
fourth through the valuation relation. -/
theorem adequateOn_of_compl_subsingleton {T : Set Square}
    (hT : Tᶜ.Subsingleton) : AdequateOn T A := by
  rw [adequateOn_iff_eq_zero]
  intro K hK hKT
  have hval := isValuation_iff.mp hK
  have hmem : ∀ q p : Square, q ≠ p → p ∉ T → K q = 0 := by
    intro q p hqp hp
    by_cases hq : q ∈ T
    · exact congrFun hKT ⟨q, hq⟩
    · exact absurd (hT hq hp) hqp
  funext p
  show K p = 0
  by_cases hp : p ∈ T
  · exact congrFun hKT ⟨p, hp⟩
  rcases p with ⟨_ | _, _ | _⟩
  · rw [hmem left _ (by decide) hp, hmem right _ (by decide) hp,
      hmem ⊤ _ (by decide) hp] at hval
    rw [← bot_def]
    simpa using hval.symm
  · show K right = 0
    rw [hmem left _ (by decide) hp, hmem ⊥ _ (by decide) hp,
      hmem ⊤ _ (by decide) hp] at hval
    simpa using hval
  · show K left = 0
    rw [hmem right _ (by decide) hp, hmem ⊥ _ (by decide) hp,
      hmem ⊤ _ (by decide) hp] at hval
    simpa using hval
  · rw [hmem left _ (by decide) hp, hmem right _ (by decide) hp,
      hmem ⊥ _ (by decide) hp] at hval
    rw [← top_def]
    simpa using hval.symm

/-- Any single context may be left unnormalized. -/
theorem adequateOn_compl_singleton (r : Square) : AdequateOn ({r}ᶜ : Set Square) A :=
  adequateOn_of_compl_subsingleton (by rw [compl_compl]; exact Set.subsingleton_singleton)

/-- Sharp normalization on the square: a value restriction is adequate exactly
when it misses at most one context. Two values never suffice. -/
theorem adequateOn_iff [Nontrivial A] {T : Set Square} :
    AdequateOn T A ↔ Tᶜ.Subsingleton := by
  refine ⟨fun h => ?_, adequateOn_of_compl_subsingleton⟩
  by_contra hT
  rw [Set.not_subsingleton_iff] at hT
  obtain ⟨r, hr, s, hs, hrs⟩ := hT
  obtain ⟨e, he⟩ := exists_ne (0 : A)
  obtain ⟨G, hGval, hGne, hGsupp⟩ := exists_valuation_pair hrs he
  refine hGne (adequateOn_iff_eq_zero.mp h G hGval ?_)
  funext t
  show G t.val = 0
  refine hGsupp t.val (fun h' => hr ?_) (fun h' => hs ?_)
  · rw [← h']; exact t.property
  · rw [← h']; exact t.property

/-! ### Explicit reconstruction -/

/-- Reconstruction on the square: normalization on `{⊥, left, right}` plus
the one essential defect value rebuild the field, by formula. -/
def reconstruct (v₀ vₗ vᵣ d : A) : ContextField Square A
  | (false, false) => v₀
  | (true, false) => vₗ
  | (false, true) => vᵣ
  | (true, true) => vₗ + vᵣ - v₀ - d

/-- Reconstruction is exact on every field. -/
theorem reconstruct_defect (K : ContextField Square A) :
    reconstruct (K ⊥) (K left) (K right) (defect K left right) = K := by
  funext p
  rcases p with ⟨_ | _, _ | _⟩
  · exact congrArg K bot_def
  · rfl
  · rfl
  · show K left + K right - K ⊥ - defect K left right = K (true, true)
    rw [defect_left_right, ← top_def]
    abel

end Square

end Descent
