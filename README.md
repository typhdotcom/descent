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

M1 is partial: it also asks for normalization lemmas on concrete context
lattices, and only chains are settled (see Models below).

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
  plus a modular correction.

## Models

`Descent/Models/Chain.lean`: on a linearly ordered context system every field
is a valuation and the observable quotient is a point, while mixed differences
still separate fields — two defect-equivalent fields on the three-element
chain have different order-2 mixed differences. Cube data is a strictly finer
observable than pairwise defect data.

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

`PROPOSAL.md` §20 sequences the work. M1 still owes normalization lemmas on
context lattices richer than chains. M2 is built; M3 opens the inverse
problem: when a full pairwise defect field reconstructs `K` modulo gauge, and
which sparse data suffices.
