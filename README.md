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

The higher layers of the hierarchy are mixed differences on comparison cubes.
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
the observed datum and `gaugeOn S A` is its kernel — the fields the observer
cannot tell from `0`. `S` is observationally complete when
`gaugeOn S A = gauge R A`, which happens exactly when the restricted datum is
injective on the observable quotient: a complete family recovers `[K]`, and no
family recovers more. Restriction always observes less than the full field,
completeness survives enlarging the family, degenerate squares carry no datum,
and the incomparable pairs carry all of it.

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
gauge forgets everything), and only the full value restriction is adequate —
normalization must supply the whole field.

`Descent/Models/Square.lean`: the four-element Boolean lattice `Bool × Bool`
is the smallest context system whose defect sees anything, and on it
everything is sharp. The valuation law is the single relation
`K left + K right = K ⊥ + K ⊤`, with strict failures. A family of squares is
complete exactly when it observes the one nondegenerate square in either
order — the singleton `{(left, right)}` suffices, and no family of degenerate
squares does. A value restriction is adequate exactly when it misses at most
one context: three values determine the fourth through the valuation
relation, two never do. Reconstruction is an explicit formula, not only an
injectivity statement.

`Descent/Status.lean` restates each claim above as a typed `example`. Prose
that outruns the library stops compiling there.

## Working on it

```nu
nu tasks.nu build   # lake build
nu tasks.nu cache   # lake exe cache get, after a toolchain or mathlib bump
nu tasks.nu check   # nix flake check
```

`direnv allow` puts `elan` on the path; the toolchain in `lean-toolchain`
installs on first use.

## Next

`PROPOSAL.md` §20 sequences the work. M2 is built. M3 is built at this
level: restricted observation with its kernel criterion, value-restriction
normalization with its gauge characterization, and sharp classifications of
both on the chain and the square, with explicit reconstruction on the square.
Completeness and adequacy on richer context lattices remain open, as does the
order-separated higher observable exposed as missing by M2 — raw mixed
differences are not that object. M4 introduces the first weighted
realization.
