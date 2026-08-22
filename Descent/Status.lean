import Descent.Core.Context
import Descent.Core.Cube
import Descent.Core.Defect
import Descent.Core.Gauge
import Descent.Models.Chain
import Descent.Models.Square
import Descent.Reconstruction.Normalization
import Descent.Reconstruction.Restricted

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

The claims below correspond to the "Gauge" section of `README.md`. The
normalization lemmas M1 also asked for are covered by the milestone M3
sections below.
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
pairwise defect plus a base-point correction. -/
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

/-- README: the height field on the three-element chain carries no pairwise
defect data. -/
example : DefectEquiv Chain.height 0 :=
  Chain.defectEquiv_height_zero

/-- README: the `[1, 2]` cube is degenerate and its order-2 mixed difference
is a retained signed first-order difference. -/
example : mixedDiff [1, 2] Chain.height = -supDiff 1 Chain.height :=
  Chain.mixedDiff_height_pair

/-- README: mixed differences along a raw direction list do not descend
through the pairwise gauge. -/
example :
    mixedDiff [1, 2] Chain.height
      ≠ mixedDiff [1, 2] (0 : ContextField (Fin 3) ℤ) :=
  Chain.mixedDiff_height_ne

/-! ## Restricted observation (milestone M3)

The claims below correspond to the "Restricted observation" section of
`README.md`.
-/

/-- README: the restricted kernel always contains the gauge. -/
example (S : Set (R × R)) : gauge R A ≤ gaugeOn S A :=
  gauge_le_gaugeOn S

/-- README: shrinking the observed family enlarges the kernel. -/
example {S T : Set (R × R)} (h : S ⊆ T) : gaugeOn T A ≤ gaugeOn S A :=
  gaugeOn_antitone h

/-- README: on a family of comparable pairs the restriction map is zero, so
its kernel is everything. -/
example {S : Set (R × R)} (h : ∀ p ∈ S, Comparable p.1 p.2) :
    gaugeOn S A = ⊤ :=
  gaugeOn_eq_top_of_comparable h

/-- README: the defect field is carried entirely by the incomparable pairs. -/
example {S : Set (R × R)} (h : {p : R × R | ¬Comparable p.1 p.2} ⊆ S) :
    ObservationallyComplete S A :=
  observationallyComplete_of_incomparable_subset h

/-- README: a family is observationally complete exactly when its restricted
datum is injective on the observable quotient --- it recovers `[K]`, and no
family recovers more. -/
example {S : Set (R × R)} :
    ObservationallyComplete S A
      ↔ Function.Injective (Observable.defectOn S : Observable R A → S → A) :=
  observationallyComplete_iff_injective

/-- README: completeness survives enlarging the family. -/
example {S T : Set (R × R)} (hST : S ⊆ T) (h : ObservationallyComplete S A) :
    ObservationallyComplete T A :=
  h.mono hST

/-! ## Normalization (milestone M3)

The claims below correspond to the "Normalization" section of `README.md`.
-/

/-- README: `T` is adequate when class together with the values on `T`
determines the field --- adequacy is stated as injectivity of a named
datum. -/
example {T : Set R} (h : AdequateOn T A) {K K' : ContextField R A}
    (hcl : Observable.mk K = Observable.mk K')
    (hres : T.domRestrict K = T.domRestrict K') : K = K' :=
  h (Prod.ext hcl hres)

/-- README: `T` is adequate exactly when no nonzero valuation vanishes on
`T`. -/
example {T : Set R} :
    AdequateOn T A
      ↔ ∀ K : ContextField R A, IsValuation K → T.domRestrict K = 0 → K = 0 :=
  adequateOn_iff_eq_zero

/-- README: enlarging the normalization datum preserves adequacy. -/
example {T T' : Set R} (h : T ⊆ T') (hT : AdequateOn T A) : AdequateOn T' A :=
  hT.mono h

/-- README: the full value restriction is always adequate. -/
example : AdequateOn (Set.univ : Set R) A :=
  adequateOn_univ

/-! ## Chain contexts under restriction (milestone M3) -/

/-- README: on a chain every family of squares is observationally complete
--- completeness is relative to the gauge, and the chain gauge forgets
everything. -/
example {R' : Type*} [LinearOrder R'] (S : Set (R' × R')) :
    ObservationallyComplete S A :=
  observationallyComplete_of_linearOrder S

/-- README: on a chain, for a nontrivial target, only the full value
restriction is adequate. -/
example {R' : Type*} [LinearOrder R'] [Nontrivial A] {T : Set R'} :
    AdequateOn T A ↔ T = Set.univ :=
  adequateOn_iff_of_linearOrder

/-! ## The square (milestone M3)

The claims below correspond to the square paragraph of the "Models" section
of `README.md`.
-/

/-- README: on the square the valuation law is one relation. -/
example {K : ContextField Square A} :
    IsValuation K ↔ K Square.left + K Square.right = K ⊥ + K ⊤ :=
  Square.isValuation_iff

/-- README: for a nontrivial target the valuation law has strict failures on
the square. -/
example [Nontrivial A] : ∃ K : ContextField Square A, ¬IsValuation K :=
  Square.exists_not_isValuation

/-- README: one square suffices --- the singleton family is complete, with no
hypothesis on the target. -/
example :
    ObservationallyComplete
      ({(Square.left, Square.right)} : Set (Square × Square)) A :=
  Square.observationallyComplete_singleton

/-- README: sharp completeness on the square, for a nontrivial target --- a
family is complete exactly when it observes the one nondegenerate square, in
either order. -/
example [Nontrivial A] {S : Set (Square × Square)} :
    ObservationallyComplete S A
      ↔ (Square.left, Square.right) ∈ S ∨ (Square.right, Square.left) ∈ S :=
  Square.observationallyComplete_iff

/-- README: any single context may be left unnormalized. -/
example (r : Square) : AdequateOn ({r}ᶜ : Set Square) A :=
  Square.adequateOn_compl_singleton r

/-- README: sharp normalization on the square, for a nontrivial target --- a
value restriction is adequate exactly when it misses at most one context. -/
example [Nontrivial A] {T : Set Square} :
    AdequateOn T A ↔ Tᶜ.Subsingleton :=
  Square.adequateOn_iff

/-- README: reconstruction on the square is an explicit formula. -/
example (K : ContextField Square A) :
    Square.reconstruct (K ⊥) (K Square.left) (K Square.right)
      (defect K Square.left Square.right) = K :=
  Square.reconstruct_defect K

end Descent.Status
