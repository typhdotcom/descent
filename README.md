# descent

A Lean 4 formalization of defect, reconstruction, and realizability.

The question is how much of a system can be reconstructed from the ways its
partial descriptions fail to compose exactly. `PROPOSAL.md` states the research
program; this file describes only what is built.

## The object

Contexts form a lattice `R`. A context field `K : R → A` values them in an
additive target. The ideal law is the valuation identity
`K a + K b = K (a ⊓ b) + K (a ⊔ b)`, and the pairwise defect is its exact
correction:

```text
D_K (a, b) = K a + K b - K (a ⊓ b) - K (a ⊔ b)
```

`D_K` is the theory's first observable, not an error measure.

## Defect

Milestone M0, in `Descent/Core/`:

- **Context** — the comparison square spanned by two contexts, and its
  degeneration on comparable pairs.
- **Field** — context fields and their pointwise additive structure.
- **Defect** — `D_K` is symmetric, vanishes on comparable contexts, is
  additive in `K` (so `defectHom` is a homomorphism), commutes with scalars,
  and is natural under lattice homomorphisms of the context system.

## Gauge

Milestone M1, in `Descent/Core/Gauge.lean`:

`gauge R A` is the kernel of the defect operator: exactly the valuations. Two
fields have the same defect precisely when they differ by a gauge element, so
pairwise defect data determines the class `[K]` in `Observable R A` and nothing
finer. Fixing a representative needs normalization supplied separately.

M1 also asked for normalization lemmas on concrete context lattices; that
debt is discharged by the sharp adequacy classifications on the chain and the
square (see Normalization and Models).

## Cubes

Milestone M2, in `Descent/Core/Cube.lean`:

The raw join calculus is mixed differences on comparison cubes.
`supDiff a K = K (· ⊔ a) - K ·` is the difference of `K` across one context
change, and `mixedDiff l K` iterates it over a finite list of directions. Up
to the bridge, the layer consumes only `⊔`: it is stated over
`SemilatticeSup`, and the meet enters only through the choice of base point.

- **Iterated differences** — `mixedDiff (a :: l) K = supDiff a (mixedDiff l K)`,
  and difference operators commute.
- **Permutation invariance** — a cube does not order its directions.
- **Degeneration** — comparable directions collapse the cube one order, up to
  sign; a direction contained in the base collapses it there; a direction that
  moves the field nowhere kills every cube through it.
- **Inclusion–exclusion** — the mixed difference is the signed alternating sum
  of `K` over the `2 ^ k` cube vertices, `+` on the top vertex.
- **Additivity and naturality** — in the field, and under `SupHom`s of the
  context system.
- **Bridge** — `mixedDiff [a, b] K (a ⊓ b) = -defect K a b`, and at an
  arbitrary base the order-2 mixed difference is a translated pairwise defect
  plus a base-point correction that vanishes at the meet base.

## Restricted observation

Milestone M3, in `Descent/Reconstruction/Restricted.lean`:

The gauge theorem settles complete observation, so the inverse problem starts
by restricting it. For a family `S` of comparison squares, `defectOn S K` is
the restriction of the defect field to `S`, and `gaugeOn S A` is the kernel
of the restriction map. `S` is observationally complete when
`gaugeOn S A = gauge R A`, which happens exactly when the restricted datum is
injective on the observable quotient: a complete family recovers `[K]`, and no
family recovers more. The restricted kernel always contains the gauge,
completeness survives enlarging the family, the restriction map is zero on
comparable pairs, and the incomparable pairs carry the whole defect field.

## Normalization

Milestone M3, in `Descent/Reconstruction/Normalization.lean`:

Defect data determines at most `[K]`; recovering the field needs a named
normalization datum. Here the datum is a value restriction: `T` is adequate
when `K ↦ ([K], K|_T)` is injective, which happens exactly when no nonzero
valuation vanishes on `T`. Adequacy is monotone and the full restriction is
always adequate; everything sharper is lattice-specific and lives with the
models.

## Models

`Descent/Models/Chain.lean`: on a linearly ordered context system every field
is a valuation and the observable quotient is a point. Mixed differences along
a raw direction list do not descend through that collapse: on the
three-element chain the height field and the zero field are defect-equivalent,
yet their mixed differences along `[1, 2]` differ. This is not higher
interaction — the `[1, 2]` cube is degenerate, so its order-2 mixed difference
is a retained signed first-order difference. The raw hierarchy is not
order-separated: degenerate cubes keep lower-order data, so any claim of
irreducible higher interaction must consume a nondegeneracy condition on the
directions, never a raw list.

For M3 the chain is the degenerate extreme: every family of squares is
observationally complete (completeness is relative to the gauge, and the chain
gauge forgets everything), and for a nontrivial target only the full value
restriction is adequate — normalization must supply the whole field.

`Descent/Models/Square.lean`: on the four-element Boolean lattice
`Bool × Bool` the pairwise defect theory is solved completely and the
classifications are sharp. The valuation law is the single relation
`K left + K right = K ⊥ + K ⊤`, with strict failures for a nontrivial target
`A`. For a nontrivial target, a family of squares is complete exactly when it
observes the one nondegenerate square in either order — the singleton
`{(left, right)}` is complete with no hypothesis on `A`, and no family of
degenerate squares is. For a nontrivial target, a value restriction is
adequate exactly when it misses at most one context: three values determine
the fourth through the valuation relation, two never do. Reconstruction is an
explicit formula, not only an injectivity statement.

## Realization

Milestone M4, in `Descent/Realization/`:

The first generative model behind a context field, and a genuinely
restrictive realization class. A finite Gibbs realization is a lattice
homomorphism from contexts to finite nonempty state spaces — meet is
intersection, join is union — together with an energy on states. It produces
the partition function `Z r = Σ exp (-energy x)` over the states of `r` and
the log-partition field `K = log Z`. State spaces are nonempty so `Z` is
positive and the logarithm is literal; the lattice compatibility is
structural, because without it every field is exactly realizable and the
class constrains nothing.

`FiniteGibbs.lean` proves the recognition bridge into the core calculus, and
the two readings of the same realization obey different laws:

- **Additive law** — the partition function of every realization is a
  valuation: `Z` always lands in the gauge.
- **Recognition identity** — the pairwise defect of `log Z` is the logarithm
  of the multiplicativity ratio `Z a · Z b / (Z (a ⊓ b) · Z (a ⊔ b))`.
- **Exact correction** — `Z a · Z b` exceeds `Z (a ⊓ b) · Z (a ⊔ b)` by
  exactly the product of the masses of the two state-space differences.
- **Universal sign** — hence `defect (log Z) ≥ 0` everywhere.
- **Sharp vanishing** — the defect of `log Z` vanishes at a square exactly
  when the partition function multiplies across it, which happens exactly
  when the state spaces are nested; `log Z` is a valuation exactly when
  every pair of state spaces is nested. Zero defect is degenerate: it forces
  the partition function at the meet to agree with one of the sides, so
  nothing in this class factors nontrivially.
- **Monotonicity** — log-partitions are monotone fields.
- **Gauge and naturality** — shifting the energy zero point moves `log Z` by
  a constant field, so the defect observable cannot see the zero point;
  realizations pull back along lattice homomorphisms; the disjoint sum of
  realizations adds partition functions.

The class is restrictive over any state carrier: a non-monotone field on the
two-element chain is the log-partition of no realization, and neither is a
field on the square with negative defect.

`Overlap.lean` makes the sign strict. The overlap realization — counting
measure on state spaces sharing one ground state — has its partition
function in the gauge like every realization, yet its log-partition has
defect exactly `log (4 / 3) > 0` at the nondegenerate square: its state
spaces there are not nested.

`Descent/Status.lean` restates each claim above as a typed `example`. Prose
that outruns the library stops compiling there.

## Realizability

Milestone M5, in `Descent/Realization/Realizable.lean`:

The inverse problem. `Realizable K` names the datum — a finite Gibbs
realization whose log-partition is exactly `K`. The M4 laws become the
necessary conditions, read in field coordinates: a realizable field is
monotone, its exponential is a valuation, and its defect is nonnegative.
Positivity is absorbed by the exponential. The axes of the inverse problem
then separate:

- **Order and algebra suffice on the solved models.** On the minimal chain
  `Bool`, realizability is exactly the order condition `K false ≤ K true` —
  the valuation law is vacuous on a chain. On the square, realizability is
  exactly monotone plus exponentially a valuation; the witness is a
  three-state carrier — one shared state, one state private to each side of
  the nondegenerate square, included exactly when its side strictly
  increases mass.
- **The classification descends to defect data.** `DefectRealizable D`
  names the defect datum. On the square the defect of any field is one
  number — its value at the nondegenerate square — and the class realizes
  exactly the nonnegative ones: every `d ≥ 0` is the defect of an explicit
  realizable field, and negative values are rejected over any state carrier
  by the universal sign.
- **Finiteness is a separate axis.** On the chain `ℝ` the identity field is
  monotone and exponentially a valuation, yet it is the log-partition of no
  realization over any state carrier: its partition function would be
  strictly monotone, forcing finite state spaces to grow strictly along an
  uncountable chain. This is a cardinality obstruction, not analytic
  convergence — every sum in the class is finite, so convergence is
  automatic and the analytic axis is absent here; it belongs to a future
  summable realization class.
- **Uniqueness lives at the partition function.** The field datum determines
  the partition function exactly. It does not determine the realization —
  two realizations with different energies share a log-partition — and
  defect data does not determine the field even within the realizable
  class: a realization and its shift share defect data.

## Kernel geometry

Milestone M6, in `Descent/Geometry/`:

Geometry is an output, and the defect has no universal sign. `Chambers.lean`
names the two sign conditions by their literal content — a field is
submodular when its defect is nonnegative, supermodular when nonpositive —
and maps the chambers:

- Each chamber is closed under addition and nonnegative scaling, and
  negation exchanges them.
- The chamber wall is exact: the chambers meet precisely in the gauge.
- On the square the chamber map is one coordinate — the sign of the single
  defect value — so the two chambers cover every field there.
- No universal sign: on the product of the square with a chain, an explicit
  field has defects of both signs.

`Definiteness.lean` studies the sampled defect matrix — the
gauge-invariant observable: defect-equivalent fields have equal matrices
over every sample. Ordinary definiteness is degenerate on it — symmetric
with zero diagonal, it is positive semidefinite exactly when it vanishes,
and likewise its negation. The condition it does support is conditional
negative semidefiniteness — nonpositive quadratic form on centered
vectors — which for any symmetric kernel with vanishing base diagonal is
exactly positive semidefiniteness of the centered Gram kernel. The
sampled datum decides what this observable sees: on the essential
two-point square sample, conditional negativity detects the submodular
chamber exactly; on the full four-context sample it collapses to the
chamber wall.

`Kernels.lean` derives the kernels that do carry metric geometry, and
names their datum: they consume the field, not its defect observable.
The join kernel `2·K(a ⊔ b) − K a − K b` and the meet kernel
`K a + K b − 2·K(a ⊓ b)` differ by exactly twice the defect, and the
triangle slack of each decomposes exactly into a defect value at a
derived square plus two order gaps:

- A monotone submodular field makes the join kernel a pseudometric — an
  actual `PseudoMetricSpace` whose distance is the kernel. Dually, a
  monotone supermodular field makes the meet kernel one.
- The sign hypothesis is necessary: an explicit monotone field outside the
  chamber breaks the triangle inequality.
- The geometry is representative-dependent, exactly: shifting by a
  valuation moves both kernels by precisely the span of the valuation,
  and on a chain — where all fields are defect-equivalent — monotone
  fields with different join kernels exist. Defect data determines a
  chamber; metric geometry needs either the sampled conditional-negativity
  observable or a normalized representative.
- Realizations carry their normalization: log-partitions are submodular
  and monotone, so every finite Gibbs realization induces a pseudometric
  from its log-partition, and the energy zero point — the constant gauge
  direction — does not move it.

## Working on it

```nu
nu tasks.nu build   # lake build
nu tasks.nu cache   # lake exe cache get, after a toolchain or mathlib bump
nu tasks.nu check   # nix flake check
```

`direnv allow` puts `elan` on the path; the toolchain in `lean-toolchain`
installs on first use.

## Next

`PROPOSAL.md` §20 sequences the work. M2 through M5 are built. M6 is built
at this level: the sign chambers are mapped — cones exchanged by negation,
wall exactly the gauge, one coordinate on the square, defects of both
signs on a richer lattice. Defect data determines the chamber, and the
milestone theorem separates what geometry consumes: the gauge-invariant
sampled defect matrix supports conditional negativity — equivalent to a
positive semidefinite centered Gram kernel, detecting the chamber at the
two-point square sample and collapsing to the wall at the full sample —
while the metric pseudogeometry of the derived kernels consumes a
normalized representative, moving by an exact span term under gauge.
Open: which sampled conditional-negativity observables embed in a Hilbert
space on richer lattices, and the chamber structure there. Realizability on richer finite lattices remains open,
where the pairwise valuation law need not control the higher
inclusion–exclusion the state maps impose — the same higher-observable gap
M2 exposed; so do completeness and adequacy on richer context lattices and
the order-separated higher observable — raw mixed differences are not that
object. M7 is concrete carriers.
