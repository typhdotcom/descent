import Descent.Core.Context
import Descent.Core.Cube
import Descent.Core.Defect
import Descent.Core.Gauge
import Descent.Models.Chain
import Descent.Models.Square
import Descent.Realization.FiniteGibbs
import Descent.Realization.Overlap
import Descent.Core.Hierarchy
import Descent.Core.Higher
import Descent.Geometry.Chambers
import Descent.Models.Arithmetic
import Descent.Models.Diamond
import Descent.Geometry.Definiteness
import Descent.Geometry.Kernels
import Descent.Realization.Realizable
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

/-! ## Weighted realization (milestone M4)

The claims below correspond to the "Realization" section of `README.md`.
-/

variable {Ω : Type*} [DecidableEq Ω] (X : FiniteGibbs R Ω)

/-- README: the state map of a realization is a lattice homomorphism into
finite sets --- meet is intersection, join is union. -/
example (a b : R) :
    X.states (a ⊓ b) = X.states a ∩ X.states b
      ∧ X.states (a ⊔ b) = X.states a ∪ X.states b :=
  ⟨X.states_inf a b, X.states_sup a b⟩

/-- README: state spaces are nonempty, so the partition function is positive
and its logarithm is literal. -/
example (r : R) : 0 < X.partition r :=
  X.partition_pos r

/-- README: zero energy realizes the counting measure. -/
example (states : R → Finset Ω) (h : ∀ r, (states r).Nonempty)
    (hinf : ∀ a b, states (a ⊓ b) = states a ∩ states b)
    (hsup : ∀ a b, states (a ⊔ b) = states a ∪ states b) (r : R) :
    (FiniteGibbs.counting states h hinf hsup).partition r = (states r).card :=
  FiniteGibbs.partition_counting states h hinf hsup r

/-- README: the additive law --- the partition function of every realization
is in the gauge. -/
example : X.partition ∈ gauge R ℝ :=
  X.partition_mem_gauge

/-- README: the recognition identity --- the defect of the log-partition is
the logarithm of the multiplicativity ratio of the partition function. -/
example (a b : R) :
    defect X.logPartition a b =
      Real.log (X.partition a * X.partition b /
        (X.partition (a ⊓ b) * X.partition (a ⊔ b))) :=
  X.defect_logPartition a b

/-- README: the exact multiplicative correction --- the product of partition
functions across a square is the product at meet and join plus the masses of
the two state-space differences. -/
example (a b : R) :
    X.partition a * X.partition b
      = X.partition (a ⊓ b) * X.partition (a ⊔ b)
        + X.mass (X.states a \ X.states b) * X.mass (X.states b \ X.states a) :=
  X.partition_mul_partition a b

/-- README: the universal sign --- the defect of a log-partition is
nonnegative. -/
example (a b : R) : 0 ≤ defect X.logPartition a b :=
  X.defect_logPartition_nonneg a b

/-- README: the defect of the log-partition vanishes at a square exactly
when the partition function multiplies across it. -/
example {a b : R} :
    defect X.logPartition a b = 0 ↔
      X.partition a * X.partition b =
        X.partition (a ⊓ b) * X.partition (a ⊔ b) :=
  X.defect_logPartition_eq_zero_iff_mul

/-- README: the sharp vanishing law --- zero defect at a square is exactly
nested state spaces. -/
example {a b : R} :
    defect X.logPartition a b = 0 ↔
      X.states a ⊆ X.states b ∨ X.states b ⊆ X.states a :=
  X.defect_logPartition_eq_zero_iff_subset

/-- README: the log-partition is a valuation exactly when every pair of
state spaces is nested. -/
example :
    IsValuation X.logPartition ↔
      ∀ a b, X.states a ⊆ X.states b ∨ X.states b ⊆ X.states a :=
  X.isValuation_logPartition_iff

/-- README: zero defect is degenerate --- it forces the partition function
at the meet to agree with one of the sides. -/
example {a b : R} (h : defect X.logPartition a b = 0) :
    X.partition (a ⊓ b) = X.partition a ∨ X.partition (a ⊓ b) = X.partition b :=
  X.partition_inf_eq_of_defect_eq_zero h

/-- README: log-partitions are monotone fields. -/
example : Monotone X.logPartition :=
  X.logPartition_mono

/-- README: shifting the energy zero point is gauge. -/
example (c : ℝ) : DefectEquiv (X.shift c).logPartition X.logPartition :=
  X.defectEquiv_logPartition_shift c

/-- README: pulling a realization back along a lattice homomorphism pulls
the defect observable back with it. -/
example {R' : Type*} [Lattice R'] (f : LatticeHom R' R) (a b : R') :
    defect (X.comap f).logPartition a b = defect X.logPartition (f a) (f b) :=
  X.defect_logPartition_comap f a b

/-- README: the disjoint sum of realizations adds partition functions. -/
example {Ψ : Type*} [DecidableEq Ψ] (Y : FiniteGibbs R Ψ) (r : R) :
    (X.disjSum Y).partition r = X.partition r + Y.partition r :=
  X.partition_disjSum Y r

/-- README: a non-monotone field on the two-element chain is the
log-partition of no realization, over any state carrier. -/
example :
    ∃ K : ContextField Bool ℝ,
      ∀ {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Bool Ω'),
        X'.logPartition ≠ K :=
  FiniteGibbs.exists_not_logPartition

/-- README: the defect of the overlap realization's log-partition at the
nondegenerate square is exactly `log (4 / 3)`. -/
example :
    defect Square.overlap.logPartition Square.left Square.right
      = Real.log (4 / 3) :=
  Square.defect_logPartition_overlap

/-- README: so the universal sign is strict, and the overlap log-partition
is not a valuation. -/
example : 0 < defect Square.overlap.logPartition Square.left Square.right :=
  Square.defect_logPartition_overlap_pos

example : ¬IsValuation Square.overlap.logPartition :=
  Square.not_isValuation_logPartition_overlap

/-- README: a field on the square with negative defect is the log-partition
of no realization, over any state carrier. -/
example :
    ∃ K : ContextField Square ℝ,
      ∀ {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Square Ω'),
        X'.logPartition ≠ K :=
  Square.exists_not_logPartition

/-! ## Realizability (milestone M5)

The claims below correspond to the "Realizability" section of `README.md`.
-/

/-- README: realizable fields are monotone. -/
example {K : ContextField R ℝ} (h : Realizable K) : Monotone K :=
  h.monotone

/-- README: realizable fields are exponentially valuations. -/
example {K : ContextField R ℝ} (h : Realizable K) : IsValuation (Real.exp ∘ K) :=
  h.isValuation_exp

/-- README: realizable fields have nonnegative defect. -/
example {K : ContextField R ℝ} (h : Realizable K) (a b : R) : 0 ≤ defect K a b :=
  h.defect_nonneg a b

/-- README: on the minimal chain, realizability is exactly the order
condition. -/
example {K : ContextField Bool ℝ} : Realizable K ↔ K false ≤ K true :=
  realizable_bool_iff

/-- README: on the square, realizability is exactly order plus algebra ---
monotone and exponentially a valuation. -/
example {K : ContextField Square ℝ} :
    Realizable K ↔ Monotone K ∧ IsValuation (Real.exp ∘ K) :=
  Square.realizable_iff

/-- README: on the square, the defect datum of any field is its single
value at the nondegenerate square. -/
example (K : ContextField Square A) :
    defect K = Square.defectData (defect K Square.left Square.right) :=
  Square.defect_eq_defectData K

/-- README: defect realizability on the square is sharp --- exactly the
nonnegative single values. -/
example {D : Square → Square → ℝ} :
    DefectRealizable D ↔ ∃ d : ℝ, 0 ≤ d ∧ D = Square.defectData d :=
  Square.defectRealizable_iff

/-- README: every nonnegative value is realized by an explicit field with
that defect. -/
example {d : ℝ} (hd : 0 ≤ d) : Realizable (Square.defectField d) :=
  Square.realizable_defectField hd

example (d : ℝ) : defect (Square.defectField d) Square.left Square.right = d :=
  Square.defect_defectField d

/-- README: negative values are rejected over any state carrier. -/
example {d : ℝ} (hd : d < 0) {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Square Ω') :
    defect X'.logPartition ≠ Square.defectData d :=
  Square.defectData_not_defect_logPartition hd X'

/-- README: on the chain `ℝ`, the identity field is the log-partition of no
realization over any state carrier. -/
example {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs ℝ Ω') :
    X'.logPartition ≠ id :=
  id_not_logPartition X'

/-- README: monotonicity and the exponential valuation law do not
characterize realizability in general --- finiteness is a separate axis. -/
example : ∃ K : ContextField ℝ ℝ, Monotone K ∧ IsValuation (Real.exp ∘ K) ∧ ¬Realizable K :=
  exists_monotone_isValuation_not_realizable

/-- README: the field datum determines the partition function. -/
example {Ω' Ψ' : Type*} [DecidableEq Ω'] [DecidableEq Ψ']
    {X' : FiniteGibbs R Ω'} {Y' : FiniteGibbs R Ψ'}
    (h : X'.logPartition = Y'.logPartition) : X'.partition = Y'.partition :=
  partition_eq_of_logPartition_eq h

/-- README: the field datum does not determine the realization. -/
example : ∃ X X' : FiniteGibbs Bool (Fin 2), X.logPartition = X'.logPartition ∧ X ≠ X' :=
  exists_logPartition_eq_of_ne

/-- README: defect data does not determine the field, even within the
realizable class. -/
example :
    ∃ X X' : FiniteGibbs Bool (Fin 2),
      DefectEquiv X.logPartition X'.logPartition ∧ X.logPartition ≠ X'.logPartition :=
  exists_defectEquiv_logPartition_ne

/-! ## Kernel geometry (milestone M6)

The claims below correspond to the "Kernel geometry" section of `README.md`.
-/

/-- README: the chamber wall is exact --- the sign chambers meet precisely
in the gauge. -/
example {A : Type*} [AddCommGroup A] [PartialOrder A] {K : ContextField R A} :
    Submodular K ∧ Supermodular K ↔ IsValuation K :=
  submodular_and_supermodular_iff

/-- README: negation exchanges the chambers. -/
example {A : Type*} [AddCommGroup A] [PartialOrder A] [AddLeftMono A]
    {K : ContextField R A} : Submodular (-K) ↔ Supermodular K :=
  submodular_neg_iff

/-- README: each chamber is closed under addition and nonnegative
scaling. -/
example {K K' : ContextField R ℝ} (h : Submodular K) (h' : Submodular K') :
    Submodular (K + K') :=
  h.add h'

example {K : ContextField R ℝ} {c : ℝ} (hc : 0 ≤ c) (h : Submodular K) :
    Submodular (c • K) :=
  h.smul hc

/-- README: on the square the chamber map is one coordinate --- the sign of
the single defect value --- and the chambers cover every field. -/
example {K : ContextField Square ℝ} :
    Submodular K ↔ 0 ≤ defect K Square.left Square.right :=
  Square.submodular_iff

example (K : ContextField Square ℝ) : Submodular K ∨ Supermodular K :=
  Square.submodular_or_supermodular K

/-- README: no universal sign --- an explicit field with defects of both
signs. -/
example : ∃ K : ContextField (Bool × Square) ℝ, ¬Submodular K ∧ ¬Supermodular K :=
  exists_not_submodular_not_supermodular

/-- README: the sampled defect matrix is gauge-invariant --- an observable
of the defect class. -/
example {ι : Type*} {K K' : ContextField R ℝ} (h : DefectEquiv K K') (r : ι → R) :
    defectMatrix K r = defectMatrix K' r :=
  defectMatrix_eq_of_defectEquiv h r

example {ι : Type*} {K G : ContextField R ℝ} (hG : IsValuation G) (r : ι → R) :
    defectMatrix (K + G) r = defectMatrix K r :=
  defectMatrix_add_of_isValuation hG r

/-- README: the raw defect matrix is positive semidefinite exactly when it
vanishes, and likewise its negation. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ContextField R ℝ} {r : ι → R} :
    (defectMatrix K r).PosSemidef ↔ defectMatrix K r = 0 :=
  posSemidef_defectMatrix_iff

example {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ContextField R ℝ} {r : ι → R} :
    (-defectMatrix K r).PosSemidef ↔ defectMatrix K r = 0 :=
  posSemidef_neg_defectMatrix_iff

/-- README: the derived kernels differ by exactly twice the defect. -/
example (K : ContextField R ℝ) (a b : R) :
    meetKernel K a b - joinKernel K a b = 2 * defect K a b :=
  meetKernel_sub_joinKernel K a b

/-- README: the triangle slack of the join kernel decomposes exactly into a
defect value at a derived square plus two order gaps. -/
example (K : ContextField R ℝ) (a b c : R) :
    joinKernel K a b + joinKernel K b c - joinKernel K a c
      = 2 * defect K (a ⊔ b) (b ⊔ c) + 2 * (K (a ⊔ b ⊔ c) - K (a ⊔ c))
        + 2 * (K ((a ⊔ b) ⊓ (b ⊔ c)) - K b) :=
  joinKernel_triangle_decomposition K a b c

/-- README: conditional negativity is exactly positive semidefiniteness of
the centered Gram kernel, for any symmetric kernel with vanishing base
diagonal entry. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : M.IsHermitian) {i₀ : ι} (h0 : M i₀ i₀ = 0) :
    CondNegSemidef M ↔ (centeredGram M i₀).PosSemidef :=
  condNegSemidef_iff_posSemidef_centeredGram hM h0

/-- README: at the essential two-point sample, conditional negativity of
the defect matrix detects the submodular chamber exactly. -/
example {K : ContextField Square ℝ} :
    CondNegSemidef (defectMatrix K ![Square.left, Square.right]) ↔ Submodular K :=
  Square.condNegSemidef_defectMatrix_pair_iff

/-- README: at the full four-context sample it collapses to the chamber
wall --- the sampled datum decides which geometry is visible. -/
example {K : ContextField Square ℝ} :
    CondNegSemidef (defectMatrix K ![⊥, Square.left, Square.right, ⊤])
      ↔ IsValuation K :=
  Square.condNegSemidef_defectMatrix_square_iff

/-- README: the derived kernels consume the field, not its defect
observable --- shifting by a valuation moves both by exactly its span. -/
example {G : ContextField R ℝ} (hG : IsValuation G) (K : ContextField R ℝ) (a b : R) :
    joinKernel (K + G) a b = joinKernel K a b + (G (a ⊔ b) - G (a ⊓ b)) :=
  joinKernel_add_of_isValuation hG K a b

example {G : ContextField R ℝ} (hG : IsValuation G) (K : ContextField R ℝ) (a b : R) :
    meetKernel (K + G) a b = meetKernel K a b + (G (a ⊔ b) - G (a ⊓ b)) :=
  meetKernel_add_of_isValuation hG K a b

/-- README: the induced geometry is representative-dependent --- on a
chain, defect-equivalent monotone fields with different join kernels
exist. -/
example :
    ∃ K K' : ContextField Bool ℝ, DefectEquiv K K' ∧ Monotone K ∧ Monotone K' ∧
      joinKernel K ≠ joinKernel K' :=
  exists_defectEquiv_monotone_joinKernel_ne

/-- README: a monotone submodular field generates a pseudometric from the
field as datum --- its distance is the join kernel; dually for the
supermodular chamber. -/
noncomputable example {K : ContextField R ℝ} (hs : Submodular K) (hK : Monotone K) :
    PseudoMetricSpace R :=
  hs.pseudoMetricSpace hK

example {K : ContextField R ℝ} (hs : Submodular K) (hK : Monotone K) :
    (hs.pseudoMetricSpace hK).toDist.dist = joinKernel K :=
  rfl

example {K : ContextField R ℝ} (hs : Supermodular K) (hK : Monotone K) :
    (hs.pseudoMetricSpace hK).toDist.dist = meetKernel K :=
  rfl

/-- README: the sign hypothesis is necessary --- a monotone field outside
the chamber breaks the triangle inequality. -/
example :
    ∃ K : ContextField Square ℝ, Monotone K ∧
      ¬joinKernel K Square.left Square.right
        ≤ joinKernel K Square.left ⊥ + joinKernel K ⊥ Square.right :=
  exists_monotone_joinKernel_triangle_fails

/-- README: log-partitions lie in the submodular chamber, so every finite
Gibbs realization induces a pseudometric on its context lattice from its
log-partition representative. -/
example : Submodular X.logPartition :=
  X.submodular_logPartition

example : (X.pseudoMetricSpace).toDist.dist = joinKernel X.logPartition :=
  rfl

/-- README: the energy zero point is normalization enough --- shifting the
energy does not move the induced kernel. -/
example (c : ℝ) :
    joinKernel (X.shift c).logPartition = joinKernel X.logPartition :=
  X.joinKernel_logPartition_shift c

/-! ## Concrete carriers (milestone M7)

The claims below correspond to the "Concrete carriers" section of
`README.md`.
-/

/-- README: the meet side of the divisor system is exact --- divisors of
the gcd are the shared divisors. -/
example (a b : Arith) :
    Arith.divisorSet (a ⊓ b) = Arith.divisorSet a ∩ Arith.divisorSet b :=
  Arith.divisorSet_inf a b

/-- README: the join side fails exactly off comparability, the lcm itself
witnessing the gap. -/
example (a b : Arith) :
    Arith.divisorSet a ∪ Arith.divisorSet b ⊆ Arith.divisorSet (a ⊔ b) :=
  Arith.divisorSet_union_subset a b

example {a b : Arith} (h : ¬Comparable a b) :
    Arith.divisorSet a ∪ Arith.divisorSet b ⊂ Arith.divisorSet (a ⊔ b) :=
  Arith.divisorSet_sup_ssubset h

/-- README: the divisor count is monotone and supermodular, and its defect
is the measured failure of the join side. -/
example : Monotone Arith.divisorCount :=
  Arith.monotone_divisorCount

example : Supermodular Arith.divisorCount :=
  Arith.supermodular_divisorCount

example (a b : Arith) :
    defect Arith.divisorCount a b
      = ((Arith.divisorSet a ∪ Arith.divisorSet b).card : ℝ)
        - ((Arith.divisorSet (a ⊔ b)).card : ℝ) :=
  Arith.defect_divisorCount a b

/-- README: the chamber wall is hit exactly at comparability. -/
example {a b : Arith} : defect Arith.divisorCount a b = 0 ↔ Comparable a b :=
  Arith.defect_divisorCount_eq_zero_iff

example {a b : Arith} : defect Arith.divisorCount a b < 0 ↔ ¬Comparable a b :=
  Arith.defect_divisorCount_neg_iff

open scoped symmDiff in
/-- README: the M6 kernel of the supermodular chamber is the divisor
symmetric-difference distance, and separation makes it a genuine metric:
zero distance forces equal contexts. -/
example (a b : Arith) :
    meetKernel Arith.divisorCount a b
      = ((Arith.divisorSet a ∆ Arith.divisorSet b).card : ℝ) :=
  Arith.meetKernel_divisorCount a b

example {a b : Arith} (h : meetKernel Arith.divisorCount a b = 0) : a = b :=
  Arith.eq_of_meetKernel_divisorCount_eq_zero h

noncomputable example : MetricSpace Arith :=
  Arith.divisorMetric

example :
    Arith.divisorMetric.toPseudoMetricSpace.toDist.dist
      = meetKernel Arith.divisorCount :=
  Arith.dist_divisorMetric

/-- README: divisor counts factor exactly through gcd and lcm, so the log
divisor count is a monotone valuation --- in the gauge, invisible to every
defect datum. -/
example (a b : Arith) :
    Arith.divisorCount (a ⊓ b) * Arith.divisorCount (a ⊔ b)
      = Arith.divisorCount a * Arith.divisorCount b :=
  Arith.divisorCount_inf_mul_sup a b

example : Monotone Arith.logDivisorCount :=
  Arith.monotone_logDivisorCount

example : Arith.logDivisorCount ∈ gauge Arith ℝ :=
  Arith.logDivisorCount_mem_gauge

/-- README: yet it is the log-partition of no finite Gibbs realization
over any state carrier --- M5's algebraic compatibility obstruction made
concrete. -/
example {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Arith Ω') :
    X'.logPartition ≠ Arith.logDivisorCount :=
  Arith.not_logPartition_logDivisorCount X'

example : ¬Realizable Arith.logDivisorCount :=
  Arith.not_realizable_logDivisorCount

/-- README: no defect-only observation decides realizability --- the zero
field carries identical defect data and is realizable. -/
example : DefectEquiv (0 : ContextField Arith ℝ) Arith.logDivisorCount :=
  Arith.defectEquiv_zero_logDivisorCount

example : Realizable (0 : ContextField Arith ℝ) :=
  realizable_zero

example :
    ∃ K K' : ContextField Arith ℝ,
      DefectEquiv K K' ∧ Realizable K ∧ ¬Realizable K' :=
  Arith.exists_defectEquiv_realizable_not_realizable

/-! ## Order separation (Q4)

The claims below correspond to the "Order separation" section of
`README.md`.
-/

/-- README: on a degenerate triple the order-3 defect is a pairwise defect
of the surviving pair --- never raw field data. -/
example (K : ContextField R A) {a b : R} (h : a ≤ b) (c : R) :
    defect3 K a b c = defect K b c :=
  defect3_of_le K h c

example (K : ContextField R A) (a c : R) : defect3 K a a c = defect K a c :=
  defect3_self K a c

/-- README: so it vanishes identically on chains, identifying the
defect-equivalent fields that raw mixed differences separate. -/
example {C : Type*} [LinearOrder C] (K : ContextField C A) (a b c : C) :
    defect3 K a b c = 0 :=
  defect3_eq_zero_of_linearOrder K a b c

example :
    mixedDiff [1, 2] Chain.height ≠ mixedDiff [1, 2] (0 : ContextField (Fin 3) ℤ) :=
  Chain.mixedDiff_height_ne

example : defect3 Chain.height = defect3 (0 : ContextField (Fin 3) ℤ) :=
  Chain.defect3_height_eq

/-- README: isolation --- the raw order-3 mixed difference is exactly face
defects, minus the order-3 defect, plus a base-point residue that
vanishes at the meet base. -/
example (K : ContextField R A) (a b c r : R) :
    mixedDiff [a, b, c] K r + defect3 K (r ⊔ a) (r ⊔ b) (r ⊔ c)
      = defect K (r ⊔ a) (r ⊔ b) + defect K (r ⊔ a) (r ⊔ c)
        + defect K (r ⊔ b) (r ⊔ c)
        + (K ((r ⊔ a) ⊓ (r ⊔ b) ⊓ (r ⊔ c)) - K r) :=
  mixedDiff_triple_add_defect3 K a b c r

example (K : ContextField R A) (a b c : R) :
    mixedDiff [a, b, c] K (a ⊓ b ⊓ c)
      = defect K a b + defect K a c + defect K b c - defect3 K a b c :=
  mixedDiff_triple_inf K a b c

/-- README: the exact gauge law --- additive in the field, so invariant
exactly under shifts with vanishing order-3 defect. -/
example (K K' : ContextField R A) (a b c : R) :
    defect3 (K + K') a b c = defect3 K a b c + defect3 K' a b c :=
  defect3_add K K' a b c

example {G : ContextField R A} (hG : ∀ a b c, defect3 G a b c = 0)
    (K : ContextField R A) (a b c : R) :
    defect3 (K + G) a b c = defect3 K a b c :=
  defect3_add_of_eq_zero hG K a b c

/-- README: the cumulative datum through order 3 has the order-≤3 gauge
as its kernel, equal cumulative data is exactly a difference in that
gauge, and the datum descends injectively to the cumulative quotient. -/
example {K : ContextField R A} :
    K ∈ gauge3 R A ↔ IsValuation K ∧ ∀ a b c, defect3 K a b c = 0 :=
  mem_gauge3_iff

example {K K' : ContextField R A} :
    Defect3Equiv K K' ↔ K - K' ∈ gauge3 R A :=
  defect3Equiv_iff_sub_mem_gauge3

example (K : ContextField R A) :
    Observable3.datum (Observable3.mk K) = (defect K, defect3 K) :=
  Observable3.datum_mk K

example : Function.Injective (Observable3.datum : Observable3 R A → _) :=
  Observable3.datum_injective

/-- README: on a distributive lattice the order-3 defect decomposes
exactly into pairwise defects at derived squares, so pairwise valuations
have none and it descends through the pairwise gauge to the observable
quotient. -/
example {D : Type*} [DistribLattice D] (K : ContextField D A) (a b c : D) :
    defect3 K a b c
      = defect K a b + defect K (a ⊔ b) c - defect K (a ⊓ c) (b ⊓ c) :=
  defect3_decompose K a b c

example {D : Type*} [DistribLattice D] {K : ContextField D A}
    (h : IsValuation K) (a b c : D) : defect3 K a b c = 0 :=
  defect3_eq_zero_of_isValuation h a b c

example {D : Type*} [DistribLattice D] {K K' : ContextField D A}
    (h : DefectEquiv K K') : defect3 K = defect3 K' :=
  defect3_eq_of_defectEquiv h

example {D : Type*} [DistribLattice D] (K : ContextField D A) :
    Observable.defect3 (Observable.mk K) = defect3 K :=
  Observable.defect3_mk K

/-- README: on distributive contexts the order-≤3 gauge collapses to the
pairwise gauge --- order 3 adds nothing. -/
example {D : Type*} [DistribLattice D] : gauge3 D A = gauge D A :=
  gauge3_eq_gauge

example {D : Type*} [DistribLattice D] {K K' : ContextField D A} :
    Defect3Equiv K K' ↔ DefectEquiv K K' :=
  defect3Equiv_iff_defectEquiv

/-- README: off distributivity descent fails --- on the diamond the height
field is a pairwise valuation with order-3 defect one at the atom triple,
which is nondegenerate: pairwise incomparable. -/
example : IsValuation Diamond.height :=
  Diamond.isValuation_height

example : defect3 Diamond.height Diamond.x Diamond.y Diamond.z = 1 :=
  Diamond.defect3_height

example :
    ¬Comparable Diamond.x Diamond.y ∧ ¬Comparable Diamond.x Diamond.z ∧
      ¬Comparable Diamond.y Diamond.z :=
  ⟨Diamond.not_comparable_x_y, Diamond.not_comparable_x_z,
    Diamond.not_comparable_y_z⟩

example :
    ∃ K K' : ContextField Diamond ℤ, DefectEquiv K K' ∧ defect3 K ≠ defect3 K' :=
  Diamond.exists_defectEquiv_defect3_ne

/-- README: on the diamond the gauges are strictly nested, and observation
through order 3 is strictly finer --- the height field and zero share the
pairwise observable and the cumulative observable separates them. -/
example : gauge3 Diamond ℤ < gauge Diamond ℤ :=
  Diamond.gauge3_lt_gauge

example : Observable.mk Diamond.height = Observable.mk (0 : ContextField Diamond ℤ) :=
  Diamond.observable_mk_height_eq

example : Observable3.mk Diamond.height ≠ Observable3.mk (0 : ContextField Diamond ℤ) :=
  Diamond.observable3_mk_height_ne

/-- README: the arithmetic lattice is provably distributive, so complete
pairwise data reconstructs the order-3 defect --- at the antichain
`2, 3, 5` through the derived square `(6, 5)`. -/
example : DistribLattice Arith :=
  inferInstance

example (K : ContextField Arith ℝ) :
    defect3 K (Arith.of 2) (Arith.of 3) (Arith.of 5)
      = defect K (Arith.of 2) (Arith.of 3) + defect K (Arith.of 6) (Arith.of 5) :=
  Arith.defect3_two_three_five K

/-- README: the sparse-face witness --- an explicit field with all three
of the triple's own face defects zero and order-3 defect one: the
triple's boundary never determines its order-3 defect. -/
example :
    ∃ K : ContextField Arith ℝ,
      defect K (Arith.of 2) (Arith.of 3) = 0 ∧
        defect K (Arith.of 2) (Arith.of 5) = 0 ∧
        defect K (Arith.of 3) (Arith.of 5) = 0 ∧
        defect3 K (Arith.of 2) (Arith.of 3) (Arith.of 5) ≠ 0 :=
  Arith.exists_defect_eq_zero_defect3_ne_zero

/-! ## Order 4 (Q4, continued)

The claims below correspond to the order-4 paragraph of the "Order
separation" section of `README.md`.
-/

/-- README: degeneracy collapses the order-4 defect to an order-3 face. -/
example (K : ContextField R A) {a b : R} (h : a ≤ b) (c d : R) :
    defect4 K a b c d = defect3 K b c d :=
  defect4_of_le K h c d

/-- README: isolation --- the raw order-4 cube is alternating order-3 and
order-2 face data minus the order-4 defect, exactly, at the meet base. -/
example (K : ContextField R A) (a b c d : R) :
    mixedDiff [a, b, c, d] K (a ⊓ b ⊓ c ⊓ d)
      = defect3 K a b c + defect3 K a b d + defect3 K a c d + defect3 K b c d
        - (defect K a b + defect K a c + defect K a d + defect K b c
            + defect K b d + defect K c d)
        - defect4 K a b c d :=
  mixedDiff_quad_inf K a b c d

/-- README: the cumulative datum through order 4 --- gauge, equivalence,
injective quotient observation. -/
example {K : ContextField R A} :
    K ∈ gauge4 R A ↔ IsValuation K ∧ (∀ a b c, defect3 K a b c = 0) ∧
      ∀ a b c d, defect4 K a b c d = 0 :=
  mem_gauge4_iff

example {K K' : ContextField R A} :
    Defect4Equiv K K' ↔ K - K' ∈ gauge4 R A :=
  defect4Equiv_iff_sub_mem_gauge4

example (K : ContextField R A) :
    Observable4.datum (Observable4.mk K) = (defect K, defect3 K, defect4 K) :=
  Observable4.datum_mk K

example : Function.Injective (Observable4.datum : Observable4 R A → _) :=
  Observable4.datum_injective

/-- README: the exact recurrence on an arbitrary lattice --- the order-3
shape plus the field gap across the distributivity-defect interval. -/
example (K : ContextField R A) (a b c d : R) :
    defect4 K a b c d
      = defect3 K a b c + defect K (a ⊔ b ⊔ c) d
        - defect3 K (a ⊓ d) (b ⊓ d) (c ⊓ d)
        + (K ((a ⊔ b ⊔ c) ⊓ d) - K ((a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d))) :=
  defect4_recurrence K a b c d

/-- README: the search criterion --- on the order-≤3 gauge the order-4
defect is exactly the field gap across the distributivity-defect
interval. -/
example {K : ContextField R A} (hK : K ∈ gauge3 R A) (a b c d : R) :
    defect4 K a b c d
      = K ((a ⊔ b ⊔ c) ⊓ d) - K ((a ⊓ d) ⊔ (b ⊓ d) ⊔ (c ⊓ d)) :=
  defect4_eq_of_mem_gauge3 hK a b c d

/-- README: on distributive lattices the remainder vanishes, the order-4
defect decomposes through order 3 in the same shape as order 3 through
order 2, and the collapse persists. -/
example {D : Type*} [DistribLattice D] (K : ContextField D A) (a b c d : D) :
    defect4 K a b c d
      = defect3 K a b c + defect K (a ⊔ b ⊔ c) d
        - defect3 K (a ⊓ d) (b ⊓ d) (c ⊓ d) :=
  defect4_decompose K a b c d

example {D : Type*} [DistribLattice D] {K : ContextField D A}
    (h : IsValuation K) (a b c d : D) : defect4 K a b c d = 0 :=
  defect4_eq_zero_of_isValuation h a b c d

example {D : Type*} [DistribLattice D] : gauge4 D A = gauge D A :=
  gauge4_eq_gauge

example {D : Type*} [DistribLattice D] {K K' : ContextField D A} :
    Defect4Equiv K K' ↔ DefectEquiv K K' :=
  defect4Equiv_iff_defectEquiv

/-- README: the order-3 recurrence on an arbitrary lattice, and its
criterion --- on the pairwise gauge the order-3 defect is exactly the
two-variable distributivity gap. -/
example (K : ContextField R A) (a b c : R) :
    defect3 K a b c
      = defect K a b + defect K (a ⊔ b) c - defect K (a ⊓ c) (b ⊓ c)
        + (K ((a ⊔ b) ⊓ c) - K ((a ⊓ c) ⊔ (b ⊓ c))) :=
  defect3_recurrence K a b c

example {K : ContextField R A} (hK : K ∈ gauge R A) (a b c : R) :
    defect3 K a b c = K ((a ⊔ b) ⊓ c) - K ((a ⊓ c) ⊔ (b ⊓ c)) :=
  defect3_eq_of_mem_gauge hK a b c

/-- README: saturation --- order-≤3 gauge fields are blind to every
two-variable distributivity interval, the blindness propagates, and the
order-4 defect vanishes on the order-≤3 gauge, on every lattice. -/
example {K : ContextField R A} (hK : K ∈ gauge3 R A) (a b c : R) :
    K ((a ⊔ b) ⊓ c) = K ((a ⊓ c) ⊔ (b ⊓ c)) :=
  apply_eq_of_mem_gauge3 hK a b c

example {K : ContextField R A} (hK : K ∈ gauge3 R A) (a b c d : R) :
    defect4 K a b c d = 0 :=
  defect4_eq_zero_of_mem_gauge3 hK a b c d

/-- README: the saturation theorem --- the order-≤4 gauge is the order-≤3
gauge on every lattice and target: cumulative observation cannot become
strictly finer at order 4. -/
example : gauge4 R A = gauge3 R A :=
  gauge4_eq_gauge3

example {K K' : ContextField R A} : Defect4Equiv K K' ↔ Defect3Equiv K K' :=
  defect4Equiv_iff_defect3Equiv

example {K K' : ContextField R A} (h : Defect3Equiv K K') :
    defect4 K = defect4 K' :=
  defect4_eq_of_defect3Equiv h

/-- README: chains kill order 4 identically. -/
example {C : Type*} [LinearOrder C] (K : ContextField C A) (a b c d : C) :
    defect4 K a b c d = 0 :=
  defect4_eq_zero_of_linearOrder K a b c d

/-- README: the recurrence instantiated at the arithmetic antichain
`2, 3, 5, 7`. -/
example (K : ContextField Arith ℝ) :
    defect4 K (Arith.of 2) (Arith.of 3) (Arith.of 5) (Arith.of 7)
      = defect3 K (Arith.of 2) (Arith.of 3) (Arith.of 5)
        + defect K (Arith.of 30) (Arith.of 7) :=
  Arith.defect4_two_three_five_seven K

/-! ## The full hierarchy (Q4, concluded)

The claims below correspond to the closing paragraph of the "Order
separation" section of `README.md`.
-/

/-- README: one defect for every finite family, whose low arities recover
the committed definitions. -/
example (K : ContextField R A) (a d : R) : defectFam K d [a] = defect K a d :=
  defectFam_pair K a d

example (K : ContextField R A) (a b c : R) :
    defectFam K c [b, a] = defect3 K a b c :=
  defectFam_triple K a b c

example (K : ContextField R A) (a b c d : R) :
    defectFam K d [c, b, a] = defect4 K a b c d :=
  defectFam_quad K a b c d

/-- README: the exact recurrence of the hierarchy, with the finite
distributivity-gap remainder, on an arbitrary lattice. -/
example (K : ContextField R A) (d a : R) (l : List R) :
    defectFam K d (a :: l)
      = defectFam K a l + defect K (supFam a l) d
        - defectFam K (a ⊓ d) (l.map (· ⊓ d))
        + (K (supFam a l ⊓ d) - K (supFam (a ⊓ d) (l.map (· ⊓ d)))) :=
  defectFam_cons K d a l

/-- README: binary blindness extends to finite joins. -/
example {K : ContextField R A} (hK : K ∈ gauge3 R A) (l : List R) (a c : R) :
    K (supFam a l ⊓ c) = K (supFam (a ⊓ c) (l.map (· ⊓ c))) :=
  supFam_inf_apply_eq_of_mem_gauge3 hK l a c

/-- README: every field in the order-≤3 gauge has vanishing defect at
every arity. -/
example {K : ContextField R A} (hK : K ∈ gauge3 R A) (l : List R) (a : R) :
    defectFam K a l = 0 :=
  defectFam_eq_zero_of_mem_gauge3 hK l a

/-- README: one defect for one family --- any two list presentations of
the same finite family have the same defect. -/
example (K : ContextField R A) {a b : R} {l l' : List R}
    (h : (a :: l).Perm (b :: l')) : defectFam K a l = defectFam K b l' :=
  defectFam_perm K h

/-- README: degeneration --- a comparable pair anywhere collapses the
family defect one order, with repeated entries as the diagonal. -/
example (K : ContextField R A) {a b : R} (h : a ≤ b) (l : List R) :
    defectFam K a (b :: l) = defectFam K b l :=
  defectFam_of_le K h l

example (K : ContextField R A) (a : R) (l : List R) :
    defectFam K a (a :: l) = defectFam K a l :=
  defectFam_cons_self K a l

example (K : ContextField R A) {a b c : R} {m l : List R} (h : a ≤ b)
    (hp : (c :: m).Perm (a :: b :: l)) :
    defectFam K c m = defectFam K b l :=
  defectFam_of_perm_of_le K h hp

/-- README: a family dominated by its head has no defect. -/
example {K : ContextField R A} {a : R} {l : List R} (h : ∀ x ∈ l, x ≤ a) :
    defectFam K a l = 0 :=
  defectFam_of_forall_le h

/-- README: the family defect is natural in the context system. -/
example {R' : Type*} [Lattice R'] (f : LatticeHom R R') (K : ContextField R' A)
    (a : R) (l : List R) :
    defectFam (K ∘ f) a l = defectFam K (f a) (l.map f) :=
  defectFam_comp f K a l

/-- README: order 3 is the final refinement --- the gauge of the whole
hierarchy is the order-≤3 gauge, on every lattice and target. -/
example {K : ContextField R A} :
    K ∈ gaugeFam R A ↔ ∀ (a : R) (l : List R), defectFam K a l = 0 :=
  mem_gaugeFam_iff

example : gaugeFam R A = gauge3 R A :=
  gaugeFam_eq_gauge3

/-! ## The final observable on the diamond (classification)

The claims below correspond to the closing paragraph of the "Order
separation" section of `README.md`.
-/

/-- README: the order-≤3 gauge of the diamond is exactly the constant
fields, for every additive commutative group. -/
example {K : ContextField Diamond A} :
    K ∈ gauge3 Diamond A ↔ ∃ c : A, K = ContextField.const Diamond c :=
  Diamond.mem_gauge3_iff_exists_const

/-- README: two diamond fields share the final observable exactly when
they differ by a constant. -/
example {K K' : ContextField Diamond A} :
    Observable3.mk K = Observable3.mk K'
      ↔ ∃ c : A, K - K' = ContextField.const Diamond c :=
  Diamond.observable3_mk_eq_mk_iff

/-- README: the observable class and the value at any one context
determine the field. -/
example {K K' : ContextField Diamond A} (p : Diamond)
    (h : Observable3.mk K = Observable3.mk K') (hp : K p = K' p) : K = K' :=
  Diamond.eq_of_mk_eq_of_apply_eq p h hp

/-- README: every class contains exactly one field normalized to zero at
a chosen context. -/
example (p : Diamond) (K : ContextField Diamond A) :
    ∃! K₀ : ContextField Diamond A,
      Observable3.mk K₀ = Observable3.mk K ∧ K₀ p = 0 :=
  Diamond.existsUnique_mk_eq_and_apply_eq_zero p K

/-! ## Sparse reconstruction on the diamond (the canonical datum)

The claims below correspond to the sparse-reconstruction paragraph of
the "Order separation" section of `README.md`.
-/

/-- README: four coordinates are complete --- equality of the canonical
datum is equality in the final observable. -/
example {K K' : ContextField Diamond A} :
    Diamond.canonicalDatum K = Diamond.canonicalDatum K'
      ↔ Observable3.mk K = Observable3.mk K' :=
  Diamond.canonicalDatum_eq_iff

/-- README: hence the datum determines every finite-family defect. -/
example {K K' : ContextField Diamond A}
    (h : Diamond.canonicalDatum K = Diamond.canonicalDatum K')
    (a : Diamond) (l : List Diamond) : defectFam K a l = defectFam K' a l :=
  Diamond.defectFam_eq_of_canonicalDatum_eq h a l

/-- README: the normalized inverse realizes every quadruple. -/
example (p q r s : A) :
    Diamond.canonicalDatum (Diamond.reconstruct p q r s) = (p, q, r, s) :=
  Diamond.canonicalDatum_reconstruct p q r s

example (p q r s : A) : Diamond.reconstruct p q r s Diamond.bot = 0 :=
  rfl

/-- README: adjoining the bottom value reconstructs the entire field. -/
example (K : ContextField Diamond A) :
    Diamond.reconstruct (defect K Diamond.x Diamond.y)
        (defect K Diamond.x Diamond.z) (defect K Diamond.y Diamond.z)
        (defect3 K Diamond.x Diamond.y Diamond.z)
      + ContextField.const Diamond (K Diamond.bot) = K :=
  Diamond.reconstruct_canonicalDatum_add_const K

/-- README: the inverse lands in the class it reconstructs. -/
example (K : ContextField Diamond A) :
    Observable3.mk (Diamond.reconstruct (defect K Diamond.x Diamond.y)
        (defect K Diamond.x Diamond.z) (defect K Diamond.y Diamond.z)
        (defect3 K Diamond.x Diamond.y Diamond.z))
      = Observable3.mk K :=
  Diamond.observable3_mk_reconstruct K

/-- README: irredundancy --- deleting any one coordinate destroys
completeness, with explicit witnesses over every nontrivial target. -/
example [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K Diamond.x Diamond.y = defect K' Diamond.x Diamond.y ∧
        defect K Diamond.x Diamond.z = defect K' Diamond.x Diamond.z ∧
        defect K Diamond.y Diamond.z = defect K' Diamond.y Diamond.z ∧
        Observable3.mk K ≠ Observable3.mk K' :=
  Diamond.exists_pqr_eq_mk_ne

example [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K Diamond.x Diamond.z = defect K' Diamond.x Diamond.z ∧
        defect K Diamond.y Diamond.z = defect K' Diamond.y Diamond.z ∧
        defect3 K Diamond.x Diamond.y Diamond.z
          = defect3 K' Diamond.x Diamond.y Diamond.z ∧
        Observable3.mk K ≠ Observable3.mk K' :=
  Diamond.exists_qrs_eq_mk_ne

example [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K Diamond.x Diamond.y = defect K' Diamond.x Diamond.y ∧
        defect K Diamond.y Diamond.z = defect K' Diamond.y Diamond.z ∧
        defect3 K Diamond.x Diamond.y Diamond.z
          = defect3 K' Diamond.x Diamond.y Diamond.z ∧
        Observable3.mk K ≠ Observable3.mk K' :=
  Diamond.exists_prs_eq_mk_ne

example [Nontrivial A] :
    ∃ K K' : ContextField Diamond A,
      defect K Diamond.x Diamond.y = defect K' Diamond.x Diamond.y ∧
        defect K Diamond.x Diamond.z = defect K' Diamond.x Diamond.z ∧
        defect3 K Diamond.x Diamond.y Diamond.z
          = defect3 K' Diamond.x Diamond.y Diamond.z ∧
        Observable3.mk K ≠ Observable3.mk K' :=
  Diamond.exists_pqs_eq_mk_ne

/-! ## The finite Gibbs boundary on the diamond

The claims below correspond to the distributivity-obstruction paragraph
of the "Order separation" section of `README.md`.
-/

/-- README: the state map of any realization is a lattice homomorphism
into the distributive lattice of finite sets. -/
example (X : FiniteGibbs R Ω) (r : R) : X.statesHom r = X.states r :=
  X.statesHom_apply r

/-- README: every lattice homomorphism from the diamond into a
distributive lattice is constant. -/
example {D : Type*} [DistribLattice D] (f : LatticeHom Diamond D)
    (a : Diamond) : f a = f Diamond.bot :=
  Diamond.latticeHom_const f a

/-- README: so every realization on the diamond has constant state
spaces, partition function, and log-partition. -/
example {Ω' : Type*} [DecidableEq Ω'] (X : FiniteGibbs Diamond Ω')
    (a : Diamond) : X.states a = X.states Diamond.bot :=
  Diamond.states_eq_states_bot X a

example {Ω' : Type*} [DecidableEq Ω'] (X : FiniteGibbs Diamond Ω')
    (a : Diamond) : X.partition a = X.partition Diamond.bot :=
  Diamond.partition_eq_partition_bot X a

example {Ω' : Type*} [DecidableEq Ω'] (X : FiniteGibbs Diamond Ω')
    (a : Diamond) : X.logPartition a = X.logPartition Diamond.bot :=
  Diamond.logPartition_eq_logPartition_bot X a

/-- README: the exact field classification --- realizable iff constant. -/
example {K : ContextField Diamond ℝ} :
    Realizable K ↔ ∃ c : ℝ, K = ContextField.const Diamond c :=
  Diamond.realizable_iff_exists_const

/-- README: the class attains exactly the zero canonical datum. -/
example {p q r s : ℝ} :
    Diamond.CanonicalDatumRealizable p q r s
      ↔ ((p, q, r, s) : ℝ × ℝ × ℝ × ℝ) = (0, 0, 0, 0) :=
  Diamond.canonicalDatumRealizable_iff

/-- README: the witness satisfies every previously known necessary
condition --- nonconstant, monotone, exponentially a valuation,
nonnegative pairwise defects, nonzero canonical datum --- and is
realizable by nothing. -/
example : Diamond.logCountField Diamond.bot ≠ Diamond.logCountField Diamond.x :=
  Diamond.logCountField_bot_ne

example : Monotone Diamond.logCountField :=
  Diamond.monotone_logCountField

/-- README: the exact witness values `Z = (1, 2, 2, 2, 3)`. -/
example :
    Diamond.countField Diamond.bot = 1 ∧ Diamond.countField Diamond.x = 2 ∧
      Diamond.countField Diamond.y = 2 ∧ Diamond.countField Diamond.z = 2 ∧
      Diamond.countField Diamond.top = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- README: the exact bridge `exp ∘ K = Z`. -/
example : Real.exp ∘ Diamond.logCountField = Diamond.countField :=
  Diamond.exp_comp_logCountField

example : IsValuation (Real.exp ∘ Diamond.logCountField) :=
  Diamond.isValuation_exp_logCountField

example (a b : Diamond) : 0 ≤ defect Diamond.logCountField a b :=
  Diamond.defect_logCountField_nonneg a b

example : Diamond.canonicalDatum Diamond.logCountField ≠ ((0 : ℝ), 0, 0, 0) :=
  Diamond.canonicalDatum_logCountField_ne

example : ¬Realizable Diamond.logCountField :=
  Diamond.not_realizable_logCountField

/-! ## The mass-compatible realization

The claims below correspond to the mass-compatibility paragraph of the
"Order separation" section of `README.md`.
-/

/-- README: every finite Gibbs realization induces a mass-compatible one
with the same partition function and log-partition. -/
noncomputable example (X : FiniteGibbs R Ω) : MassGibbs R Ω :=
  X.toMassGibbs

example (X : FiniteGibbs R Ω) : X.toMassGibbs.partition = X.partition :=
  X.toMassGibbs_partition

example (X : FiniteGibbs R Ω) : X.toMassGibbs.logPartition = X.logPartition :=
  X.toMassGibbs_logPartition

/-- README: the realization laws survive the weaker interface ---
positive monotone valuation partition, recognition identity, exact
correction, nonnegative defect, sharp mass-degeneracy zero law. -/
example (M : MassGibbs R Ω) : IsValuation M.partition :=
  M.isValuation_partition

example (M : MassGibbs R Ω) : Monotone M.partition :=
  M.partition_mono

example (M : MassGibbs R Ω) (a b : R) :
    defect M.logPartition a b
      = Real.log (M.partition a * M.partition b
          / (M.partition (a ⊓ b) * M.partition (a ⊔ b))) :=
  M.defect_logPartition a b

example (M : MassGibbs R Ω) (a b : R) :
    M.partition a * M.partition b
      = M.partition (a ⊓ b) * M.partition (a ⊔ b)
        + (M.partition a - M.partition (a ⊓ b))
          * (M.partition b - M.partition (a ⊓ b)) :=
  M.partition_mul_partition a b

example (M : MassGibbs R Ω) (a b : R) : 0 ≤ defect M.logPartition a b :=
  M.defect_logPartition_nonneg a b

example (M : MassGibbs R Ω) {a b : R} :
    defect M.logPartition a b = 0
      ↔ M.partition (a ⊓ b) = M.partition a
        ∨ M.partition (a ⊓ b) = M.partition b :=
  M.defect_logPartition_eq_zero_iff

/-- README: the diamond overlap system --- unit weights on the shared
blocks --- is mass-compatible, and crosses the proved boundary: its
partition function is the witness values, its log-partition the excluded
field, its canonical datum nonzero. -/
example : MassGibbs Diamond (Fin 3) :=
  Diamond.overlap

example : Diamond.overlap.partition = Diamond.countField :=
  Diamond.overlap_partition

example : Diamond.overlap.logPartition = Diamond.logCountField :=
  Diamond.overlap_logPartition

example :
    Diamond.canonicalDatum Diamond.overlap.logPartition ≠ ((0 : ℝ), 0, 0, 0) :=
  Diamond.canonicalDatum_overlap_ne

end Descent.Status
