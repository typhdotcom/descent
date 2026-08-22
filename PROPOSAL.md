# Universe III: Descent

## Proposal for a Formal Theory of Defect, Reconstruction, and Realizability

### Status

This is a proposal for a new Lean 4 project.

It is intentionally **not** a continuation of an existing formal universe.

The project should begin from a clean repository and a clean conceptual context. Earlier projects may eventually supply isolated proofs or lemmas, but they are not dependencies of the ontology, vocabulary, module structure, or research program proposed here.

The working name **Descent** is provisional.

______________________________________________________________________

# 1. The stake

The project begins from one question:

> **How much of a system can be reconstructed from the ways its partial descriptions fail to compose exactly?**

A system may admit many resolutions, contexts, coordinate descriptions, quotients, local views, or coarse-grainings.

Some combinations behave ideally.

Others fail.

The proposal treats those failures not as noise around the real object, but as candidate **observables of the object**.

The basic program is:

\[
\\text{descriptions}
\\longrightarrow
\\text{comparison laws}
\\longrightarrow
\\text{defects}
\\longrightarrow
\\text{invariants}
\\longrightarrow
\\text{reconstruction}.
\]

The underlying carrier is deliberately not fixed in advance.

Graphs, lattices, probability spaces, constraint systems, chain complexes, finite state systems, or other structures may later instantiate the theory.

They are realizations, not foundations.

______________________________________________________________________

# 2. What is primitive

The first version of the project should assume as little as possible.

Its minimal mathematical ingredients are:

1. a structured family of **contexts** or **resolutions**;
2. a way to compare or combine them;
3. a scalar or structured quantity attached to each context;
4. operators measuring failure of an ideal composition law.

The first concrete interface should probably be a lattice-like resolution system rather than a maximally abstract category.

Let (R) carry suitable meet and join operations

\[
a\\wedge b,
\\qquad
a\\vee b.
\]

Let

\[
K:R\\to A
\]

be a field valued in an additive target such as (\\mathbb R).

The central second-order observable is

```text
D_K(a,b) = K(a) + K(b) - K(a ∧ b) - K(a ∨ b).
```

The sign convention may be reversed if another convention proves structurally cleaner. It should be fixed once and treated mechanically thereafter.

If

\[
D_K(a,b)=0
\]

for every pair, then (K) obeys the corresponding valuation law.

The project studies the nonzero case.

______________________________________________________________________

# 3. The first principle: exactness is the vacuum

The preferred mathematical shape throughout the project is:

\[
\\boxed{\\text{ideal law}+\\text{exact obstruction to that law}}
\]

rather than an isolated inequality or metaphorical interpretation.

For a proposed law, the project should seek five anchors whenever the mathematics permits:

1. **Exact law** — the identity including the correction term.
2. **Boundary** — a necessary and sufficient condition for the correction to vanish.
3. **Strict witness** — an explicit example where it does not vanish.
4. **Impossibility or counterexample** — a theorem preventing an unjustified stronger law.
5. **Inverse theorem** — a statement of what the correction determines about the system.

The fifth anchor is essential to this project.

A defect that merely detects failure is useful.

A defect from which structure can be recovered is foundationally more interesting.

______________________________________________________________________

# 4. Defects are observables, not errors

The initial interpretation of

\[
D_K
\]

should be purely mathematical:

> (D_K) measures the failure of (K) to satisfy a valuation identity on a comparison square.

No physical vocabulary belongs in this definition.

In particular, theorem and definition names in the core should not contain terms such as:

- gravity;
- matter;
- time;
- consciousness;
- observer;
- spacetime;
- mass;
- entropy,

unless the object is literally the standard mathematical object with that name.

Interpretations belong in separate recognition layers.

The project should first determine what the defect **does**.

Possible properties include:

- symmetry;
- vanishing on comparable contexts;
- sign laws;
- monotonicity;
- invariance under transformations of (K);
- functorial behavior under maps of resolution systems;
- definiteness of matrices assembled from defect values;
- recovery of (K) from a defect field;
- reconstruction of a realization from sufficiently rich defect data.

______________________________________________________________________

# 5. Gauge: what defects cannot see

A second derivative does not determine its potential without normalization data.

The same principle should be made explicit here.

Define two fields (K,K') to be **defect-equivalent** when

\[
D_K=D\_{K'}.
\]

Equivalently,

\[
D\_{K-K'}=0.
\]

Thus the kernel of the defect operator is not an inconvenience. It is the project's first natural gauge freedom.

The immediate structural problem is:

> **Characterize the kernel of the defect operator on each class of context systems.**

For lattice-valued contexts this means characterizing the valuation-like fields annihilated by (D).

The observable object is therefore initially not (K) itself but

```text
[K] = K/ker D.
```

Absolute reconstruction requires additional information.

That information may take forms such as:

- a distinguished vacuum or modal state;
- a boundary value;
- an asymptotic condition;
- normalization at one context;
- a duality condition;
- finite support;
- positivity;
- decay.

This distinction should remain explicit in every inverse theorem:

\[
\\text{defect data}
\\Rightarrow
\\text{field modulo gauge},
\]

followed separately by

\[
\\text{normalization}
\\Rightarrow
\\text{chosen representative}.
\]

A central ambition of the project is to understand how much apparent “structure” is genuine defect data and how much is gauge supplied by a presentation.

______________________________________________________________________

# 6. Higher interaction

Pairwise defect should not be presumed fundamental.

It is only the first nontrivial layer.

Given a suitable family of independent context changes, define higher mixed differences

\[
\\Delta\_{1}\\Delta\_{2}\\cdots\\Delta\_{k}K.
\]

Equivalently, on a (k)-dimensional comparison cube, take the signed alternating sum of (K) over its (2^k) vertices.

The second-order case measures irreducible pairwise coupling.

The third-order case measures information not reducible to the pairwise faces.

Higher orders measure progressively more irreducible failures of factorization.

The intended hierarchy is therefore

\[
K
\\quad\\to\\quad
D^{(2)}
\\quad\\to\\quad
D^{(3)}
\\quad\\to\\quad
D^{(4)}
\\quad\\to\\cdots
\]

with each layer defined without assuming what interpretation it will eventually receive.

Questions include:

- When does vanishing above order (k) characterize a finite interaction order?
- Which sign patterns are forced?
- Which sign patterns are impossible?
- How does the hierarchy transform under coarse-graining?
- Which higher defects are determined by lower ones?
- Which hierarchies can actually arise from concrete realizations?

The last question is the higher-order **realizability problem**.

______________________________________________________________________

# 7. Realization comes after the defect calculus

A defect field can be studied abstractly without knowing where it came from.

A **realization** supplies the missing generative structure.

A realization might consist of context-indexed state spaces

\[
X_r,
\]

comparison maps between them, and additional data such as

\[
E_r:X_r\\to\\mathbb R,
\]

probability measures, weights, actions, or counting measures.

These produce a context field.

For example, a weighted finite or summable realization may produce

\[
Z(r)=\\sum\_{x\\in X_r}e^{-E_r(x)}
\]

and

\[
K(r)=\\log Z(r).
\]

The abstract defect calculus should not depend on this construction.

Instead there should be recognition theorems of the form

\[
\\text{realization}
\\Longrightarrow
\\text{abstract field}
\\Longrightarrow
\\text{abstract defect}.
\]

This separation is deliberate.

It creates two different research directions:

### Forward problem

Given a realization, determine its defect hierarchy.

### Inverse problem

Given a defect hierarchy, determine which realizations could have produced it.

The inverse problem is at least as important as the forward one.

______________________________________________________________________

# 8. The inverse-first doctrine

Most mathematical toy universes begin by specifying a microscopic system and calculating what it does.

This project should repeatedly attempt the reverse direction.

Suppose an observer receives only

\[
D_K(a,b)
\]

for some collection of pairs.

What can be recovered?

Possible targets form a ladder:

\[
D
\\Rightarrow
[K]
\\Rightarrow
K
\\Rightarrow
\\text{spectrum}
\\Rightarrow
\\text{weighted realization}
\\Rightarrow
\\text{carrier equivalence class}.
\]

Each arrow is a separate theorem or impossibility result.

The project should be unusually strict about the **datum** consumed by an inverse theorem.

Distinguish, for example:

- the complete defect field;
- one fixed-scale defect matrix;
- one infinite row;
- a finite collection of entries;
- the full higher-order hierarchy;
- the hierarchy plus asymptotic normalization.

Two inverse results consuming different data are different results even if their conclusions match.

Sparse reconstruction should be treated as a first-class research problem.

______________________________________________________________________

# 9. Observational equivalence

A realization should not be identified with its chosen implementation.

Given an observable family (\\mathcal O), define two realizations (X,Y) to be observationally equivalent when

\[
\\mathcal O(X)=\\mathcal O(Y).
\]

Different choices of (\\mathcal O) induce different equivalence relations.

For example:

- scalar defect data may identify one quotient;
- residue-refined data may distinguish more;
- all higher mixed defects may distinguish more again.

The appropriate notion of “same system” should therefore be discovered from the inverse theory rather than imposed in advance.

A major target is a hierarchy

\[
\\text{isomorphism}
\\Rightarrow
\\text{observational equivalence}*{\\mathrm{rich}}
\\Rightarrow
\\text{observational equivalence}*{\\mathrm{coarse}},
\]

with strictness witnesses wherever the implications fail to reverse.

This makes the resolution of the observer part of the mathematics.

______________________________________________________________________

# 10. Realizability

Not every abstract defect table should be expected to come from a meaningful system.

The realizability problem asks:

> Given abstract defect data satisfying some collection of algebraic identities, does there exist a realization producing it?

This should eventually split by realization class.

Examples might include:

- finite weighted sets;
- Gibbs systems;
- positive-definite quadratic lattices;
- graph cohomology carriers;
- Markov systems;
- chain complexes;
- other structures discovered later.

Theorems should distinguish:

\[
\\text{necessary conditions},
\\qquad
\\text{sufficient conditions},
\\qquad
\\text{classification}.
\]

Possible necessary conditions may include:

- positivity;
- conditional negative definiteness;
- positive semidefiniteness of derived kernels;
- submodularity;
- reflection laws;
- moment constraints;
- data-processing inequalities;
- asymptotic decay;
- integrality.

None should be assumed universal until proved at the correct abstraction level.

______________________________________________________________________

# 11. Geometry is an output

The project must not begin by declaring a geometry.

Geometry becomes legitimate only when the defect data canonically induces geometric structure.

For example, a derived kernel might satisfy a definiteness condition strong enough to generate:

- a Hilbert-space embedding;
- a metric;
- a pseudometric;
- a convex geometry;
- a spectral geometry;
- a phase chamber.

Only then should geometric terminology appear.

The preferred theorem shape is:

\[
\\text{defect laws}
\+
\\text{definiteness hypotheses}
\\Rightarrow
\\text{canonical geometric object}.
\]

This is stronger than assigning geometric meaning to a graph simply because a graph is present.

______________________________________________________________________

# 12. Local-to-global obstruction as a realization

Cohomological obstruction remains an important model class, but it should enter downstream.

A local constraint system may admit locally valid data that fails to arise from a global potential.

Schematically,

\[
\\text{local consistency}
\\not\\Rightarrow
\\text{global exactness}.
\]

The quotient of locally admissible data by globally removable data produces an obstruction class.

This is an excellent realization of the project's philosophy:

\[
\\text{remove everything exact}
\\longrightarrow
\\text{study what survives}.
\]

But the new project should not assume that every interesting defect is cohomological.

Instead it should ask when cohomological obstruction, valuation defect, statistical factorization defect, and other failure modes admit a common formal treatment.

If they do not, they should remain separate realizations.

No unification is to be declared by analogy alone.

______________________________________________________________________

# 13. Perspective is a later problem

The project should make no foundational claim about consciousness.

If questions of subjectivity return, the first technical object should be **perspective**, not consciousness.

A perspective might eventually be modeled as:

- conditioning on internal data;
- localization to a subdiagram;
- a compatible family of partial observations;
- a fiber over a coarse description;
- a quotient defining what distinctions remain accessible.

The mathematical question would be:

> Which invariants are globally defined, which are perspective-relative, and which obstructions prevent all local perspectives from assembling into a single complete description?

This question belongs naturally to the project.

Claims about phenomenal consciousness do not, unless substantial mathematics eventually forces a useful recognition theorem.

______________________________________________________________________

# 14. Formal architecture

The repository should enforce a strict separation between strata.

A tentative structure:

```text
Descent/
  Core/
    Context.lean
    Field.lean
    Defect.lean
    Gauge.lean
    Cube.lean

  Reconstruction/
    FullField.lean
    Sparse.lean
    Boundary.lean
    Identifiability.lean

  Realization/
    FiniteWeighted.lean
    Gibbs.lean
    Partition.lean

  Geometry/
    Kernels.lean
    Definiteness.lean
    Embedding.lean

  Models/
    Arithmetic.lean
    Lattice.lean
    Graph.lean
    Cohomology.lean

  Recon/
    ...

  Status.lean
```

This is a starting hypothesis, not a commitment.

Files should split when theorem dependencies reveal a better structure.

The import graph is part of the model.

Core must never import interpretation modules.

______________________________________________________________________

# 15. Core theorem discipline

Every substantial object should accumulate a predictable theorem package.

For a defect operator:

### Algebra

- symmetry or controlled asymmetry;
- diagonal behavior;
- behavior on comparable contexts;
- additivity in the field;
- behavior under scalar multiplication;
- behavior under pullback of contexts.

### Gauge

- characterization of obvious kernel elements;
- equivalence between equal defects and a kernel statement;
- normalization theorems.

### Sign

- nonnegative/nonpositive regimes;
- exact equality conditions;
- explicit opposite-sign counterexamples if universality fails.

### Higher order

- relation between pairwise and cube defects;
- inclusion-exclusion identities;
- decomposition laws.

### Inverse

- uniqueness modulo gauge;
- recovery under boundary data;
- impossibility under insufficient data.

### Realization

- theorem showing a concrete model computes the abstract object.

No interpretation should be allowed to outrun this package.

______________________________________________________________________

# 16. Falsify first

Numerical reconnaissance is legitimate, but its purpose is to kill conjectures cheaply.

For any expensive universal claim:

1. identify the smallest nontrivial rank or dimension;
2. identify degeneration directions;
3. exploit symmetries to reduce the search domain;
4. sweep adversarial rather than aesthetically pleasing examples;
5. record near-saturation as carefully as violations;
6. turn successful numerical claims into certified inequalities before calling them evidence.

A tiny positive margin is not evidence for a proof with a uniform gap.

A sign change is not an embarrassment.

It is a phase boundary.

If a conjecture fails, its counterexample should become a theorem whenever reasonably formalizable.

______________________________________________________________________

# 17. The blank-slate LLM protocol

This document is intended to be sufficient initialization for a fresh coding model.

A model working on this repository should obey the following rules.

### Rule 1 — No inherited mythology

Do not assume knowledge of any earlier project.

Do not introduce physical narratives to motivate a definition.

Definitions are justified by mathematical use.

### Rule 2 — Abstract only after consumption

Do not begin with the most general category-theoretic object imaginable.

Implement the weakest structure currently needed.

When multiple theorems consume fewer hypotheses than their carrier provides, extract that smaller interface.

### Rule 3 — The theorem statement is the design test

A good abstraction is one on which the desired theorem can be stated naturally.

Do not retain fields merely because an earlier carrier possessed them.

### Rule 4 — Counterexamples outrank intentions

If the intended theorem is false, formalize the failure.

Change the research question rather than weakening the meaning of “proved.”

### Rule 5 — Every inverse result names its datum

Never say “the defect determines the system” without specifying exactly which defect data is supplied and what equivalence class is recovered.

### Rule 6 — Interpretation is downstream

A physical, logical, informational, or philosophical reading must appear as a theorem-backed recognition of an already-defined mathematical object.

### Rule 7 — Build truth, not prose truth

The repository should contain a manifest in which important README claims are restated as Lean examples or theorems.

If a theorem is renamed, weakened, or removed, stale factual prose should become detectable.

______________________________________________________________________

# 18. Policy for old theorem libraries

Previous repositories are not conceptual dependencies.

They are potential **proof donors**.

The default rule is:

> **Do not import an old universe merely to save work.**

An old theorem may be transplanted only after the new repository has independently reached a definition for which that theorem is exactly appropriate.

The workflow is:

1. define the new abstraction without consulting old naming or narrative;
2. state the theorem wanted in the new vocabulary;
3. determine whether an old theorem proves precisely that statement;
4. if yes, port the minimum proof and dependencies required;
5. rename everything according to the new abstraction;
6. place provenance in a non-imported audit file;
7. verify that deleting the old repository would not change the meaning of the new one.

What may be transplanted:

- generic analytic lemmas;
- generic finite-probability results;
- lattice identities;
- summability machinery;
- Poisson-summation infrastructure;
- established reconstruction lemmas;
- proof patterns whose hypotheses exactly match.

What should normally be rebuilt:

- foundational definitions;
- namespaces;
- theorem interfaces;
- conceptual decompositions;
- interpretation layers;
- project-specific terminology.

This gives old work the correct status:

\[
\\boxed{\\text{scaffolding and theorem supply, not inherited ontology}.}
\]

______________________________________________________________________

# 19. Candidate donor families

The following are signposts only.

They should not dictate the new architecture.

### Generic defect algebra

Earlier work contains four-term defect operators with generic symmetry and vanishing laws.

If the new `Defect` interface independently converges on the same object, those proofs are natural transplant candidates.

### Partition systems

Earlier work isolates a very weak weighted-system interface consisting essentially of:

- a distinguished zero-energy mode;
- positive energy elsewhere;
- summability.

Strong classification and reconstruction results already exist for that interface.

If the new realization layer independently rediscovers exactly those hypotheses, reproving the analytic tail machinery from scratch would serve little purpose.

### Reconstruction and spectral peeling

There is existing machinery showing how partition samples can reveal successive spectral layers.

If spectral reconstruction becomes a realization theorem of the new inverse framework, transplanting this machinery is preferable to disguising old work as rediscovery.

### Relative entropy and cumulant machinery

Generic finite-distribution results relating logarithmic moment generating functions, Jensen gaps, tilting, and relative entropy are likely reusable if a Gibbs realization enters.

They should be imported conceptually only through the standard mathematics they express.

### Cohomological obstruction

Existing graph Hodge machinery may later supply a concrete realization in which failure of exactness produces an invariant obstruction with a least-energy representative.

It should not be present in the initial core.

______________________________________________________________________

# 20. Initial milestones

## M0 — Empty room

Create the repository.

Define only:

- context structure;
- scalar fields;
- pairwise defect;
- elementary algebra.

No graph.

No lattice action.

No probability.

No physics words.

Build a status manifest immediately.

______________________________________________________________________

## M1 — Gauge and valuation

Characterize what the pairwise defect forgets.

Targets:

\[
D_K=0
\]

as a valuation condition,

\[
D_K=D\_{K'}
\\iff
K-K'\\in\\ker D,
\]

plus normalization lemmas for simple context lattices.

This milestone establishes the observable quotient.

______________________________________________________________________

## M2 — Cubes

Define higher mixed defects from finite comparison cubes.

Prove:

- permutation invariance;
- degeneration laws;
- reduction under constant directions;
- relationship to repeated difference operators;
- inclusion-exclusion identities;
- low-order examples.

The goal is a carrier-free interaction hierarchy.

______________________________________________________________________

## M3 — Reconstruction

Ask the generic inverse questions before introducing rich realizations.

Determine conditions under which:

- a full pairwise defect field reconstructs (K) modulo gauge;
- boundary data fixes a representative;
- sparse rows or subfamilies suffice;
- reconstruction is impossible.

The project should seek explicit algorithms as well as existential statements.

______________________________________________________________________

## M4 — Weighted realization

Introduce the first nontrivial generative model:

\[
(X_r,E_r)
\\longmapsto
Z(r)
\\longmapsto
K(r)=\\log Z(r).
\]

Prove the recognition bridge into the core defect calculus.

Only now introduce probability or Gibbs language where mathematically literal.

______________________________________________________________________

## M5 — Realizability

Begin the reverse problem.

Given abstract field or defect data, characterize whether it is induced by the chosen weighted realization class.

Separate:

- algebraic compatibility;
- positivity;
- analytic convergence;
- uniqueness.

Counterexamples are expected.

______________________________________________________________________

## M6 — Kernel geometry

Study matrices and kernels produced from the pairwise defect.

Determine when sign or definiteness conditions generate canonical geometric structures.

Do not assume a universal sign.

Map the chambers where different structures exist.

______________________________________________________________________

## M7 — Concrete carriers

Only after the generic machinery has stabilized, add demanding realizations.

Likely candidates:

- arithmetic resolution systems;
- positive-definite quadratic lattices;
- graph cohomology;
- local-to-global constraint systems.

Each model must justify its existence by producing a theorem not already visible at the abstract level.

______________________________________________________________________

# 21. Questions that should drive the project

The first edition of the research program should revolve around questions of this form.

### Q1 — Kernel

For which context systems can the complete kernel of the pairwise defect operator be classified?

### Q2 — Reconstruction

What is the weakest datum from which a field can be reconstructed modulo its defect gauge?

### Q3 — Sparse reconstruction

Which rows, rays, chains, prime-indexed subsets, or finite samples determine the same information as the complete defect field?

### Q4 — Higher interaction

When do higher mixed defects contain genuinely new information beyond pairwise data?

### Q5 — Realizability

Which abstract defect hierarchies arise from positive weighted realizations?

### Q6 — Definiteness

Under what conditions does defect data define PSD, CND, metric, or embedding structure?

### Q7 — Universality

Which theorems survive replacement of the realization while keeping only the abstract context and defect interfaces?

### Q8 — Observational equivalence

For each datum class, what is the exact equivalence relation on realizations induced by indistinguishability?

### Q9 — Local/global correspondence

When is a failure of compositional valuation equivalent to a local-to-global obstruction in an underlying realization?

### Q10 — Perspective

Can localization or conditioning be formalized as a change of accessible defect data, with rigorous limits on global reconstruction from an internal view?

Q10 is deliberately last.

______________________________________________________________________

# 22. Success criteria

This project should not be judged by the quantity of formalized mathematics.

It succeeds if it discovers a small interface with unexpectedly large deductive reach.

Strong evidence of success would include several of the following:

- the same abstract defect theorem has genuinely different realizations;
- a complete defect field reconstructs a nontrivial object modulo a precisely characterized gauge;
- sparse defect data is unexpectedly sufficient;
- higher mixed defects expose interaction invisible pairwise;
- realizability admits sharp necessary and sufficient conditions;
- an apparently carrier-specific theorem becomes inevitable from the core interface;
- geometric structure is derived canonically from defect data;
- a previous “foundational” carrier becomes merely one example.

The most desirable event is:

> A theorem first proved for one realization is discovered to consume so little structure that its true object belongs near the root of the repository.

When that happens, move the theorem.

Do not protect the old architecture.

______________________________________________________________________

# 23. Failure criteria

The project should contract or change direction if:

- all nontrivial results require a single concrete carrier;
- the abstract defect calculus produces only tautological identities;
- higher differences carry no useful invariant information;
- reconstruction requires essentially the full original model as input;
- realizability is too unconstrained to support classification;
- geometric interpretations require hand-inserted geometry;
- proposed universal signs repeatedly fragment into unrelated special cases without a useful chamber structure.

A failed attempted universe is acceptable.

An unfalsifiable one is not.

______________________________________________________________________

# 24. The modelling philosophy

The project is built around a sequence of eliminations.

Do not ask first:

> What are the fundamental things?

Ask:

> Which distinctions disappear under allowed redescription?

Then:

> What remains invariant?

Then:

> Where does an expected composition law fail?

Then:

> Is that failure itself stable under redescription?

Then:

> What can be reconstructed from it?

The intended movement is

\[
\\text{presentation}
\\to
\\text{quotient}
\\to
\\text{obstruction}
\\to
\\text{observable}
\\to
\\text{inverse problem}.
\]

The project should prefer what survives elimination over what was easy to name at the beginning.

______________________________________________________________________

# 25. Compact thesis

The entire proposal can be compressed to four claims.

### I. Description is not structure

A model should not identify an object with a preferred representation of it.

### II. Failure is data

When an otherwise natural locality, factorization, valuation, or compatibility law fails, the invariant correction may contain more structural information than the ideal law.

### III. An observable earns its status through inversion

The strongest evidence that a defect is fundamental is that the underlying system can be partially or completely reconstructed from it.

### IV. Foundations are discovered by theorem migration

A structure belongs near the root of the universe when results repeatedly shed assumptions until they depend only on that structure.

The repository should therefore be designed to permit its own foundations to move.

______________________________________________________________________

# 26. North star

The long-term question is:

\[
\\boxed{
\\text{Given only partial descriptions and their irreducible incompatibilities,
what world can be reconstructed?}
}
\]

Everything else is downstream.

Not matter.

Not gravity.

Not spacetime.

Not consciousness.

Not even a lattice or a graph.

First determine the calculus of descriptions, the gauge they cannot resolve, the defects left by failed composition, and the information recoverable from those defects.

Then see what kinds of universes realize it.
