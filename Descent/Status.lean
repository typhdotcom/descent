import Descent.Core.Context
import Descent.Core.Cube
import Descent.Core.Defect
import Descent.Core.Gauge
import Descent.Models.Chain
import Descent.Models.Square
import Descent.Realization.FiniteGibbs
import Descent.Realization.Overlap
import Descent.Geometry.Chambers
import Descent.Models.Arithmetic
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
/-- README: the M6 metric of the supermodular chamber is the divisor
symmetric-difference distance. -/
example (a b : Arith) :
    meetKernel Arith.divisorCount a b
      = ((Arith.divisorSet a ∆ Arith.divisorSet b).card : ℝ) :=
  Arith.meetKernel_divisorCount a b

example : (Arith.divisorPseudoMetric).toDist.dist = meetKernel Arith.divisorCount :=
  Arith.dist_divisorPseudoMetric

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
over any state carrier. -/
example {Ω' : Type*} [DecidableEq Ω'] (X' : FiniteGibbs Arith Ω') :
    X'.logPartition ≠ Arith.logDivisorCount :=
  Arith.not_logPartition_logDivisorCount X'

example : ¬Realizable Arith.logDivisorCount :=
  Arith.not_realizable_logDivisorCount

end Descent.Status
