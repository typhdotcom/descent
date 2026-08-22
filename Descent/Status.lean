import Descent.Core.Context
import Descent.Core.Cube
import Descent.Core.Defect
import Descent.Core.Gauge
import Descent.Models.Chain

/-!
# Status manifest

Every load-bearing claim `README.md` makes about the mathematics is restated
here as an `example` with an explicit type. Renaming, weakening, or deleting a
result breaks this file, which is what makes stale prose detectable.

Nothing outside this file may import it.
-/

namespace Descent.Status

variable {R A : Type*} [Lattice R] [AddCommGroup A]

/-! ## Defect (milestone M0)

The claims below correspond to the "Defect" section of `README.md`.
-/

/-- README: the defect is the exact correction to the valuation identity. -/
example (K : ContextField R A) (a b : R) :
    K a + K b = K (a ⊓ b) + K (a ⊔ b) + defect K a b := by
  rw [defect_def]
  abel

/-- README: the defect is symmetric. -/
example (K : ContextField R A) (a b : R) : defect K a b = defect K b a :=
  defect_comm K a b

/-- README: the defect vanishes on comparable contexts. -/
example (K : ContextField R A) {a b : R} (h : Comparable a b) : defect K a b = 0 :=
  Comparable.defect_eq_zero K h

/-- README: the defect is additive in the field. -/
example (K K' : ContextField R A) (a b : R) :
    defect (K + K') a b = defect K a b + defect K' a b :=
  defect_add K K' a b

/-- README: the defect commutes with scalars. -/
example {S : Type*} [Monoid S] [DistribMulAction S A]
    (s : S) (K : ContextField R A) (a b : R) :
    defect (s • K) a b = s • defect K a b :=
  defect_smul s K a b

/-- README: the defect is natural in the context system. -/
example {R' : Type*} [Lattice R'] (f : LatticeHom R R') (K : ContextField R' A) (a b : R) :
    defect (K ∘ f) a b = defect K (f a) (f b) :=
  defect_comp f K a b

/-! ## Gauge (milestone M1)

The claims below correspond to the "Gauge" section of `README.md`. M1 also
asks for normalization lemmas on concrete context lattices; those are not
built yet, so no claim here covers them.
-/

/-- README: the gauge freedom is the kernel of the defect operator, and it is
a subgroup of the fields. -/
example : AddSubgroup (ContextField R A) := gauge R A

/-- README: gauge elements are exactly the valuations. -/
example (K : ContextField R A) : K ∈ gauge R A ↔ IsValuation K :=
  mem_gauge_iff

/-- README: two fields have the same defect exactly when they differ by a
gauge element. -/
example (K K' : ContextField R A) : DefectEquiv K K' ↔ K - K' ∈ gauge R A :=
  defectEquiv_iff_sub_mem_gauge

/-- README: pairwise defect data determines the field modulo gauge, and no
more --- the induced map on the observable quotient is injective. -/
example : Function.Injective (Observable.defect : Observable R A → _) :=
  Observable.defect_injective

/-! ## Cubes (milestone M2)

The claims below correspond to the "Cubes" section of `README.md`. Until the
bridge to the pairwise defect, they are stated over `SemilatticeSup` alone:
the cube layer consumes no meet.
-/

section Cube

variable {S B : Type*} [SemilatticeSup S] [AddCommGroup B]

/-- README: the mixed difference is the iterated difference operator. -/
example (a : S) (l : List S) (K : ContextField S B) :
    mixedDiff (a :: l) K = supDiff a (mixedDiff l K) :=
  mixedDiff_cons a l K

/-- README: difference operators commute. -/
example (a b : S) (K : ContextField S B) :
    supDiff a (supDiff b K) = supDiff b (supDiff a K) :=
  supDiff_comm a b K

/-- README: the mixed difference is permutation invariant. -/
example {l l' : List S} (h : l.Perm l') (K : ContextField S B) :
    mixedDiff l K = mixedDiff l' K :=
  mixedDiff_perm h K

/-- README: comparable directions collapse the cube one order, up to sign. -/
example {a b : S} (h : a ≤ b) (l : List S) (K : ContextField S B) :
    mixedDiff (a :: b :: l) K = -mixedDiff (a :: l) K :=
  mixedDiff_cons_cons_of_le h l K

/-- README: a direction contained in the base collapses the cube there. -/
example {a c : S} {l : List S} (ha : a ∈ l) (hc : a ≤ c) (K : ContextField S B) :
    mixedDiff l K c = 0 :=
  mixedDiff_apply_eq_zero_of_le ha hc K

/-- README: a direction that moves the field nowhere kills every cube through
it. -/
example {a : S} {K : ContextField S B} (h : supDiff a K = 0) {l : List S}
    (ha : a ∈ l) : mixedDiff l K = 0 :=
  mixedDiff_eq_zero_of_supDiff_eq_zero h ha

/-- README: inclusion--exclusion over the vertices of the comparison cube. -/
example (l : List S) (K : ContextField S B) (c : S) :
    mixedDiff l K c
      = (l.sublists'.map fun t =>
          ((-1 : ℤ) ^ (l.length + t.length)) • K (t.foldr (· ⊔ ·) c)).sum :=
  mixedDiff_eq_sum_sublists' l K c

/-- README: the mixed difference is additive in the field. -/
example (l : List S) (K K' : ContextField S B) :
    mixedDiff l (K + K') = mixedDiff l K + mixedDiff l K' :=
  mixedDiff_add l K K'

/-- README: the mixed difference is natural in the context system. -/
example {S' : Type*} [SemilatticeSup S'] (f : SupHom S S') (K : ContextField S' B)
    (l : List S) : mixedDiff l (K ∘ f) = mixedDiff (l.map f) K ∘ f :=
  mixedDiff_comp f K l

end Cube

/-- README: the pairwise defect is the order-2 mixed difference based at the
meet, up to the fixed sign. -/
example (K : ContextField R A) (a b : R) :
    mixedDiff [a, b] K (a ⊓ b) = -defect K a b :=
  mixedDiff_pair_inf K a b

/-- README: at an arbitrary base the order-2 mixed difference is a translated
pairwise defect plus a modular correction. -/
example (K : ContextField R A) (a b c : R) :
    mixedDiff [a, b] K c + defect K (c ⊔ a) (c ⊔ b)
      = K c - K ((c ⊔ a) ⊓ (c ⊔ b)) :=
  mixedDiff_pair_add_defect K a b c

/-! ## Chain contexts (models)

The claims below correspond to the "Models" section of `README.md`.
-/

/-- README: on a chain every field is a valuation. -/
example {R' : Type*} [LinearOrder R'] (K : ContextField R' A) : IsValuation K :=
  isValuation_of_linearOrder K

/-- README: on a chain the observable quotient is a point. -/
example {R' : Type*} [LinearOrder R'] : Subsingleton (Observable R' A) :=
  inferInstance

/-- README: pairwise defect data does not determine the cube hierarchy ---
two defect-equivalent fields can have different mixed differences. -/
example :
    ∃ K K' : ContextField (Fin 3) ℤ, ∃ l : List (Fin 3),
      DefectEquiv K K' ∧ mixedDiff l K ≠ mixedDiff l K' :=
  exists_defectEquiv_mixedDiff_ne

end Descent.Status
