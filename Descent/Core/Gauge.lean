import Descent.Core.Defect
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Gauge

A second difference does not determine its potential. The same is true here:
`defect` forgets exactly the fields it annihilates, and those fields are the
theory's first gauge freedom rather than an inconvenience.

`gauge R A` is the kernel of the defect operator --- the valuations. Two fields
are `DefectEquiv` when they differ by a gauge element, so the observable
attached to a field is not `K` but its class `[K]` in `Observable R A`.
Recovering a representative needs normalization data supplied separately, and
every inverse theorem downstream must say which.
-/

namespace Descent

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-- `K` is a valuation when its pairwise defect vanishes identically. -/
def IsValuation (K : ContextField R A) : Prop :=
  ∀ a b, defect K a b = 0

/-- The gauge group: the fields the pairwise defect cannot see. -/
def gauge (R A : Type*) [Lattice R] [AddCommGroup A] :
    AddSubgroup (ContextField R A) :=
  (defectHom : ContextField R A →+ (R → R → A)).ker

theorem mem_gauge_iff {K : ContextField R A} : K ∈ gauge R A ↔ IsValuation K := by
  constructor
  · intro h a b
    exact congrFun (congrFun (AddMonoidHom.mem_ker.mp h) a) b
  · intro h
    refine AddMonoidHom.mem_ker.mpr ?_
    funext a b
    exact h a b

theorem isValuation_iff_defect_eq_zero {K : ContextField R A} :
    IsValuation K ↔ defect K = 0 := by
  constructor
  · intro h
    funext a b
    exact h a b
  · intro h a b
    exact congrFun (congrFun h a) b

theorem ContextField.isValuation_const (c : A) : IsValuation (ContextField.const R c) := by
  intro a b
  simp

/-- Two fields are defect-equivalent when they induce the same pairwise defect. -/
def DefectEquiv (K K' : ContextField R A) : Prop :=
  defect K = defect K'

/-- The gauge statement of §5: equal defects means differing by a valuation. -/
theorem defectEquiv_iff_sub_isValuation {K K' : ContextField R A} :
    DefectEquiv K K' ↔ IsValuation (K - K') := by
  rw [isValuation_iff_defect_eq_zero]
  constructor
  · intro h
    funext a b
    rw [defect_sub, h]
    simp
  · intro h
    funext a b
    have := congrFun (congrFun h a) b
    rw [defect_sub] at this
    simpa [sub_eq_zero] using this

theorem defectEquiv_iff_sub_mem_gauge {K K' : ContextField R A} :
    DefectEquiv K K' ↔ K - K' ∈ gauge R A := by
  rw [mem_gauge_iff, defectEquiv_iff_sub_isValuation]

@[refl]
theorem DefectEquiv.refl (K : ContextField R A) : DefectEquiv K K := rfl

theorem DefectEquiv.symm {K K' : ContextField R A} (h : DefectEquiv K K') :
    DefectEquiv K' K := Eq.symm h

theorem DefectEquiv.trans {K K' K'' : ContextField R A}
    (h : DefectEquiv K K') (h' : DefectEquiv K' K'') : DefectEquiv K K'' := Eq.trans h h'

/-- Defect-equivalence as a setoid, so the observable quotient can be formed. -/
def defectSetoid (R A : Type*) [Lattice R] [AddCommGroup A] :
    Setoid (ContextField R A) where
  r := DefectEquiv
  iseqv := ⟨DefectEquiv.refl, DefectEquiv.symm, DefectEquiv.trans⟩

/-- The observable quotient `[K] = K / ker D`. This, not `K`, is what pairwise
defect data determines. -/
def Observable (R A : Type*) [Lattice R] [AddCommGroup A] : Type _ :=
  Quotient (defectSetoid R A)

namespace Observable

/-- The class of a field. -/
def mk (K : ContextField R A) : Observable R A := Quotient.mk (defectSetoid R A) K

theorem mk_eq_mk {K K' : ContextField R A} :
    mk K = mk K' ↔ DefectEquiv K K' :=
  Quotient.eq (r := defectSetoid R A)

/-- The defect descends to the observable quotient, and the class is exactly
the fibre it descends over. -/
def defect : Observable R A → (R → R → A) :=
  Quotient.lift Descent.defect fun _ _ h => h

@[simp]
theorem defect_mk (K : ContextField R A) : defect (mk K) = Descent.defect K :=
  rfl

theorem defect_injective : Function.Injective (defect : Observable R A → _) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ K =>
    induction y using Quotient.inductionOn with
    | _ K' => exact mk_eq_mk.mpr h

end Observable

end Descent
