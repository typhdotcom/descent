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
lattices, and none are built.

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

`PROPOSAL.md` §20 sequences the work. M1 closes once the gauge is characterized
concretely enough to normalize a representative on a specific context lattice.
M2 adds higher mixed defects on comparison cubes, and M3 opens the inverse
problem.
