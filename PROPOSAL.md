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

The core API should be application-neutral and follow mathlib conventions.
Definitions should use established mathematical nouns; theorem names should describe
their formal content; docstrings should state the object, hypotheses, convention, or
non-obvious design choice tersely. Realization-specific terminology belongs in the
module that defines the corresponding data.

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

# 6. Raw differences and higher interaction

Pairwise defect should not be presumed fundamental, but neither should an
iterated difference be called an irreducible interaction merely because it has
high order.

On a join-semilattice, a context change in direction (a) defines

\[
\\Delta_a K(c)=K(c\\vee a)-K(c).
\]

Iterating these operators over a finite direction list gives a raw mixed
difference

\[
\\Delta\_{a_1}\\Delta\_{a_2}\\cdots\\Delta\_{a_k}K,
\]

equivalently the signed alternating sum over the associated comparison cube.
This calculus consumes only joins.

Raw cubes are not order-separated. If directions are repeated or comparable,
the cube degenerates and its nominal order-(k) difference can reduce to
lower-order data. In particular, raw mixed differences need not descend
through pairwise defect-equivalence. The three-element chain supplies a strict
witness: pairwise defect identifies every field, while a degenerate raw
order-2 difference retains a signed first-order difference.

The formal development must therefore keep three objects distinct:

\[
\\text{iterated difference}
\\neq
\\text{irreducible higher interaction}
\\neq
\\text{pairwise observable}.
\]

On a lattice, pairwise defect is related to the raw join calculus by a
canonical base-point choice:

\[
\\operatorname{mixedDiff}[a,b]K(a\\wedge b)=-D_K(a,b).
\]

Thus pairwise defect is a meet-normalized evaluation of the generic second
mixed difference, not simply the second member of an already established
interaction hierarchy.

Order 3 now supplies the first corrected object. The triple
inclusion--exclusion defect

\[
D^{(3)}\_K(a,b,c)
=K(a)+K(b)+K(c)-K(a\\wedge b)-K(a\\wedge c)-K(b\\wedge c)
+K(a\\wedge b\\wedge c)-K(a\\vee b\\vee c)
\]

is related exactly to the raw triple mixed difference: at the common meet
base, the raw cube is the sum of its three pairwise face defects minus
(D^{(3)}); at an arbitrary base there is one additional named residue.
Comparable directions reduce (D^{(3)}) to surviving pairwise face data, so
the cumulative datum through order 3 is the pair (D,D^{(3)}), not the
third-order term in isolation.

The kernel of this cumulative datum is the order-(\\le 3) gauge, and quotienting
by equality of the pair gives an injectively observed cumulative class. On
distributive lattices (D^{(3)}) decomposes into pairwise defects at derived
squares, so the cumulative gauge equals the pairwise gauge and order 3 adds no
information. On the diamond the containment is strict: two fields with the
same complete pairwise defect can have different triple defect. Thus the first
higher observable is carrier-sensitive rather than a universal strict
extension of pairwise observation.

Order 4 supplies the next cumulative layer and exposes the obstruction to
continuing the distributive recurrence on an arbitrary lattice. Its exact law
is

\[
\\begin{aligned}
D^{(4)}(a,b,c,d)
={}&D^{(3)}(a,b,c)+D(a\\vee b\\vee c,d)
-D^{(3)}(a\\wedge d,b\\wedge d,c\\wedge d)\\\\
&+K((a\\vee b\\vee c)\\wedge d)
-K((a\\wedge d)\\vee(b\\wedge d)\\vee(c\\wedge d)).
\\end{aligned}
\]

The last line is the exact field gap across a distributivity-defect interval.
The cumulative datum through order 4 is (D,D^{(3)},D^{(4)}), with its own
kernel and injectively observed quotient. For a field in the order-(\\le 3)
gauge, every term above except the distributivity gap vanishes. But membership
in that gauge also gives blindness to every two-variable distributivity
interval, and the valuation law propagates this blindness to the
three-variable interval above. Hence the gap always vanishes:

\[
\\operatorname{gauge}_{\\le 4}=\\operatorname{gauge}_{\\le 3}
\]

on every lattice and for every target. Order 4 never refines cumulative
observation beyond order 3; its datum is already a function of the
order-(\\le 3) class.

The finite hierarchy is now closed by one general construction rather than a
sequence of named layers. For every nonempty finite family,
`inclusionExclusion` is the signed sum over meets of nonempty subfamilies and
`defectFam` is its failure to reach the family join. The construction is
presentation-independent, a comparable pair anywhere in the family collapses
the defect one order, and the defect is natural under pullback along lattice
homomorphisms. Its arity-2, arity-3, and arity-4 instances recover (D),
(D^{(3)}), and (D^{(4)}), while its arbitrary-lattice recurrence carries the
finite distributivity-defect remainder

\[
K((\\bigvee\_{x\\in F}x)\\wedge d)-K(\\bigvee\_{x\\in F}(x\\wedge d)).
\]

Binary distributivity blindness for fields in the order-(\\le 3) gauge extends
to every finite join. The recurrence therefore forces every finite-family
defect to vanish on that gauge. Conversely, the arity-2 and arity-3 instances
recover its defining data, so

\[
\\operatorname{gauge}_{\\mathrm{finite}}=
\\operatorname{gauge}_{\\le 3}
\]

on every lattice and for every target. Order 3 is the final refinement of
finite inclusion--exclusion defect observation. This closes Q4: pairwise
observation suffices on distributive contexts, order 3 can strictly refine it
off distributivity, and no higher finite order adds information beyond order
3\.

On the diamond the final kernel is classified completely, for every additive
commutative target: the order-(\\le 3) gauge consists exactly of constant
fields. Consequently two fields have the same final observable exactly when
their difference is constant, the observable class together with one context
value determines the field, and every class has a unique representative
vanishing at a chosen context. This is the full inverse cycle on the first
carrier where order 3 is genuinely new.

The final observable is also sparse and explicit on the diamond. Its canonical
datum is the quadruple consisting of the three pairwise defects at the
incomparable atom pairs and the order-3 defect at the atom triple. Equality of
these four coordinates is exactly equality of final observable classes, every
quadruple occurs, and adjoining the bottom value reconstructs the field by an
explicit inverse. For every nontrivial additive commutative target, deleting
any one coordinate destroys completeness. Thus the final observable is four
irredundant measurements, not the full table in disguise.

The closure removes the question whether this hierarchy keeps producing new
observables. Questions about the completed datum still include:

- When does vanishing above order (k) characterize a finite interaction order?
- Which sign patterns are forced or impossible after order separation?
- How does an order-separated construction transform under coarse-graining?
- Which finite-family defect profiles arise from concrete realizations?

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

Given a realization, determine its observable defect data.

### Inverse problem

Given observable defect data, determine which realizations could have produced it.

The inverse problem is at least as important as the forward one.

______________________________________________________________________

# 8. The inverse-first doctrine

Most mathematical toy universes begin by specifying a microscopic system and calculating what it does.

This project should repeatedly attempt the reverse direction.

Suppose the available datum consists only of

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
- the raw mixed-difference table;
- the complete finite-family inclusion--exclusion datum, whose gauge is
  exactly the order-(\\le 3) gauge;
- either observable datum plus explicit normalization.

Two inverse results consuming different data are different results even if their conclusions match.

Sparse reconstruction should be treated as a first-class research problem.

At the abstract pairwise level, complete observation is already understood:

\[
D_K=D\_{K'}
\\quad\\Longleftrightarrow\\quad
K-K'\\in\\ker D.
\]

The complete defect field therefore determines exactly ([K]) in the observable
quotient. This is the gauge theorem, not a future reconstruction theorem.
Restating it does not count as progress on the inverse problem.

The generic inverse problem begins by restricting the observation. For
(S\\subseteq R\\times R), let

\[
D_S(K)=D_K|\_S.
\]

The family (S) is **observationally complete** when

\[
\\ker D_S=\\ker D.
\]

This equality says precisely that observation on (S) distinguishes the same
field classes as the complete pairwise defect. Rows, rays, chains, finite
subfamilies, and structured index sets should be compared through this kernel
criterion.

Absolute reconstruction is a separate map. A normalization datum (N) is
adequate when

\[
K\\longmapsto([K],N(K))
\]

is injective. Every normalization theorem must name (N), prove injectivity, and
show by counterexample when a weaker datum fails.

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
- a restricted defect family may or may not induce the full pairwise quotient.

Raw mixed differences are not automatically observables for an existing
quotient. In particular, the raw cube calculus does not descend through
pairwise defect-equivalence: degenerate cubes can retain lower-order
information that pairwise defect forgets. A cube construction may be called an
observable only after its datum map and exact kernel are stated.

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

This makes the resolution of the observable family part of the mathematics.

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

# 13. Names and documentation

The core should read like a small mathlib development.

Names should be concise, compositional, and determined by mathematical type and
behavior. Prefer standard terminology over project-specific synonyms. A docstring
should explain a definition's formal role or a theorem's non-obvious convention,
not supply a narrative that the API does not need.

Introduce terminology only when it shortens theorem statements or distinguishes
objects that the formal development actually treats differently. When several
modules consume the same structure, move the shared mathematical name toward the
root; keep realization-specific names local to their realization.

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

Core must never import application or realization modules.

The current mathematics exposes a conceptual stratification inside the core:

\[
\\text{raw join calculus}
\\xrightarrow{\\text{evaluate at the meet base}}
\\text{pairwise lattice defect}
\\xrightarrow{\\text{quotient by its kernel}}
\\text{pairwise observable}.
\]

The mixed-difference calculus belongs to the first layer and consumes a
join-semilattice; pairwise defect belongs to the second and consumes a lattice.
The order-separated lattice layer begins with the cumulative data
(D,D^{(3)}). Its kernel is the order-(\\le 3) gauge. On distributive lattices
this collapses to the pairwise observable; on the diamond it is strictly
finer. The general finite-family inclusion--exclusion defect then replaces a
ladder of further interfaces. It is symmetric in the family, degenerates
under comparable entries, is natural under lattice homomorphisms, and obeys
an exact arbitrary-lattice recurrence with a finite distributivity-defect
remainder. Finite-join blindness proves that its complete gauge is exactly the
order-(\\le 3) gauge on every lattice. Thus order 3 is the final refinement of
this observation architecture rather than merely the first unresolved step
of an indefinite tower.

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
- decomposition laws;
- exact degeneration into lower-order data;
- a stated nondegeneracy or order-separation datum;
- gauge characterization and descent before observable terminology;
- strict witnesses that do not use degenerate cubes as higher interaction.

### Inverse

- uniqueness modulo gauge;
- recovery under boundary data;
- impossibility under insufficient data.

### Realization

- theorem showing a concrete model computes the abstract object.

No README or overview claim should be allowed to outrun this package.

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

### Rule 1 — Self-contained foundations

Do not assume knowledge of any earlier project.

Introduce a definition when it is consumed by a stated theorem or construction.

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

### Rule 6 — Application terms stay local

Keep core names application-neutral. Specialized terminology belongs in the module
where the corresponding structure is defined and connected to the core by a theorem.

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
- application layers;
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

Use only standard mathematical names.

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

Define raw mixed differences from finite comparison cubes.

Prove:

- permutation invariance;
- degeneration laws;
- reduction under constant directions;
- relationship to repeated difference operators;
- inclusion-exclusion identities;
- low-order examples.

Relate the raw join calculus to pairwise lattice defect by evaluating the
second mixed difference at the meet base.

The goal is a carrier-free calculus of finite changes together with an exact
account of its degeneracies. It is not yet an irreducible interaction
hierarchy. A degenerate raw cube may retain lower-order data and raw mixed
differences need not descend through the pairwise gauge.

______________________________________________________________________

## M3 — Restricted observation and normalization

The complete pairwise defect already determines ([K]) by the gauge theorem of
M1. Do not count that tautological quotient statement as reconstruction.

M3 is responsible for closing the concrete normalization debt left by M1.
M1 remains partial until at least one context lattice has a sharp theorem
identifying adequate normalization data.

For a family of observed comparison squares (S), define the restricted defect
map (D_S) and characterize its kernel.

Prove:

- observational completeness criteria (\\ker D_S=\\ker D);
- complete and incomplete sparse families, with strict witnesses;
- minimal normalization data for concrete context lattices;
- injectivity of (K\\mapsto([K],N(K))) for each adequate normalization (N);
- impossibility under weaker observation or normalization data.

M3 preserved the order-separated higher observable exposed as missing by M2
without manufacturing a quotient. The later finite-family development
identifies the complete datum and its gauge exactly: order 3 is the final
refinement, and all higher inclusion--exclusion defects vanish on its gauge.

The project should seek explicit reconstruction algorithms as well as
existential statements.

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

For which context systems can the complete kernel of an established defect datum be classified?

On the diamond the final kernel is solved: `gauge3 Diamond A` consists exactly
of constant fields for every additive commutative group (A). Equality of final
observable classes is therefore equality up to a constant, and one context
value determines a unique representative.

### Q2 — Reconstruction

What is the weakest restricted pairwise datum with the same kernel as complete
defect observation, and what additional normalization reconstructs the field
itself?

### Q3 — Sparse reconstruction

Which rows, rays, chains, prime-indexed subsets, or finite samples (S) satisfy
(\\ker D_S=\\ker D)?

The diamond case is solved. The three pairwise defects at the incomparable
atom pairs together with the order-3 defect at the atom triple determine the
complete observable datum and every higher finite-family defect. Every
quadruple occurs, adjoining one normalization reconstructs the field, and for
every nontrivial additive commutative target each of the four measurements is
essential.

Concretely, with

\[
p=D_K(x,y),\\quad q=D_K(x,z),\\quad r=D_K(y,z),\\quad
s=D^{(3)}\_K(x,y,z),
\]

the normalized coordinates must satisfy

\[
\\begin{aligned}
K(x)-K(\\bot)&=s-r, & K(y)-K(\\bot)&=s-q,\\
K(z)-K(\\bot)&=s-p, & K(\\top)-K(\\bot)&=2s-p-q-r.
\\end{aligned}
\]

These identities are packaged as a reconstruction map with both round-trip
laws. Minimality is witnessed strictly after deleting each one of (p), (q),
(r), and (s), rather than inferred from a dimension count.

### Q4 — Higher interaction

Resolved. At order 3 the cumulative gauge collapses to the pairwise gauge on
distributive lattices and is strictly finer on the diamond. The general
finite-family inclusion--exclusion defect is presentation-independent,
degenerating, and natural; its arbitrary-lattice recurrence carries exactly a
finite distributivity-defect remainder. Binary blindness extends to finite
joins, forcing every higher finite-family defect to vanish on the
order-(\\le 3) gauge. The complete hierarchy gauge therefore equals the
order-(\\le 3) gauge on every lattice and for every additive commutative target.

### Q5 — Realizability

Which finite-family defect profiles arise from positive weighted realizations?

The first boundary is settled exactly. Every lattice homomorphism from the
diamond into a distributive lattice is constant, so every finite Gibbs
realization on the diamond has constant state spaces, partition function, and
log-partition. Consequently

\[
\\operatorname{Realizable}(K)
\\quad\\Longleftrightarrow\\quad
K \\text{ is constant}
\]

and

\[
\\operatorname{CanonicalDatumRealizable}(p,q,r,s)
\\quad\\Longleftrightarrow\\quad
(p,q,r,s)=(0,0,0,0),
\]

where realizability of the canonical datum is named directly rather than
routed through pairwise `DefectRealizable`. The explicit positive field

\[
Z(\\bot)=1,\\qquad Z(x)=Z(y)=Z(z)=2,\\qquad Z(\\top)=3,
\\qquad K=\\log\\circ Z.
\]

is nonconstant and monotone, (\\exp\\circ K=Z) is a valuation, all pairwise
defects of (K) are nonnegative, and its canonical datum is nonzero, yet (K) is
not realizable. Thus the finite witness isolates distributive structure in the
state map as the obstruction, rather than convergence, cardinality, or energy.

The realization laws have also migrated to their weakest established home.
`IsPositiveValuation Z` is the field-level conjunction of positivity,
monotonicity, and the valuation law; it alone implies the recognition identity,
the exact multiplicative correction, nonnegative logarithmic defect, and the
sharp zero law. Every finite Gibbs partition lies in this algebraic envelope.
Conversely, over a decidable carrier every positive valuation has the trivial
singleton presentation `states r = {r}`, `weight = Z`. Finite sums over named
state sets therefore supply no geometry by themselves. Do not introduce
another realization whose axioms observe only aggregate masses: any future
state-space structure must make restriction, identification, or gluing data
appear in its theorems.

### Q6 — Definiteness

Under what conditions does defect data define PSD, CND, metric, or embedding structure?

### Q7 — Universality

Which theorems survive replacement of the realization while keeping only the abstract context and defect interfaces?

### Q8 — Observational equivalence

For each datum class, what is the exact equivalence relation on realizations induced by indistinguishability?

### Q9 — Local/global correspondence

When is a failure of compositional valuation equivalent to a local-to-global obstruction in an underlying realization?

The first model is complete. `FiniteRestriction` assigns nonempty finite state
types to a preorder with functorial restriction toward coarser contexts.
Lattice structure enters only to form compatible local states as a fiber
product over the meet and the canonical comparison from global states over the
join. On the diamond, bottom is (\\mathbf 1), the atoms are (\\mathbf 2), and
the top consists of the three codewords (\\{000,011,101\\}). Every atom
restriction is surjective; each atom-pair comparison embeds three global states
into four compatible pairs and misses one; the triple comparison embeds three
into eight and misses five. The logarithmic cardinality field is exactly
`Diamond.logCountField`, and one bridge theorem identifies its complete
canonical datum with the four comparison-cardinality ratios

\[
\\left(\\log\\frac 43,\\log\\frac 43,\\log\\frac 43,
\\log\\frac 83\\right).
\]

The pairwise recognition theorem is complete. For every finite restriction
system, the `logCard` defect is exactly the comparison-cardinality term plus
a fiber-balance residue. Under injectivity, the first term counts missed
compatible states, is nonnegative, and vanishes exactly at surjectivity. The
residue vanishes exactly under the cardinal balance

\[
|\\operatorname{Compat}(a,b)|\\,|X\_{a\\wedge b}|
=|X_a|\\,|X_b|,
\]

which constant finite fiber cardinality of either restriction leg forces. The
three diamond pair coordinates now derive from this generic result.

The immediate continuation is the order-3 recognition theorem. This is the
final realization layer demanded by the abstract hierarchy: order 3 is the
last refinement of defect observation, so do not build recognition terms
above it. Define the triple comparison-cardinality term, missed compatible
triples, and the exact triple residue, then prove

\[
\\begin{aligned}
D^{(3)}\_{\\log |X|}(a,b,c)
&=\\log\\frac{|\\operatorname{Compat3}(a,b,c)|}
{|X\_{a\\vee b\\vee c}|}\\\\
&\\quad+
\\log\\frac{|X_a|\\,|X_b|\\,|X_c|\\,|X\_{a\\wedge b\\wedge c}|}
{|X\_{a\\wedge b}|\\,|X\_{a\\wedge c}|\\,|X\_{b\\wedge c}|
\\,|\\operatorname{Compat3}(a,b,c)|}.
\\end{aligned}
\]

Under injectivity of the triple comparison, identify its first term with

\[
\\log\\left(1+
\\frac{|\\operatorname{Missed3}(a,b,c)|}
{|X\_{a\\vee b\\vee c}|}\\right),
\]

prove nonnegativity, and prove that it vanishes exactly at surjectivity. Prove
that the triple residue vanishes exactly under

\[
\\begin{aligned}
|\\operatorname{Compat3}(a,b,c)|
&\\,|X\_{a\\wedge b}|\\,|X\_{a\\wedge c}|\\,|X\_{b\\wedge c}|\\\\
&=|X_a|\\,|X_b|\\,|X_c|\\,|X\_{a\\wedge b\\wedge c}|.
\\end{aligned}
\]

Give this balance structural content: when all three pairwise meets coincide,
constant finite fiber cardinality for any two of the three restriction legs to
that common meet must imply the triple balance. Instantiate the theorem on the
diamond atom triple, derive its order-3 coordinate as
(\\log(1+5/3)=\\log(8/3)), and make the complete canonical-datum bridge follow
from the generic pairwise and triple recognition theorems.

Do not add weights, a sheaf layer, or a general finite-family recognition
tower. The abstract hierarchy already proves there is no new observable above
order 3.

### Q10 — Restricted data

How do localization or conditioning change the available defect data, and what are
the exact reconstruction limits under those restrictions?

Q10 is deliberately last.

______________________________________________________________________

# 22. Success criteria

This project should not be judged by the quantity of formalized mathematics.

It succeeds if it discovers a small interface with unexpectedly large deductive reach.

Strong evidence of success would include several of the following:

- the same abstract defect theorem has genuinely different realizations;
- a proper restriction of defect data is observationally complete;
- a sharp normalization theorem recovers a representative from its gauge class;
- order-separated higher observables expose information invisible pairwise;
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
- no order-separation of raw differences yields useful invariant information;
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
what structure can be reconstructed?}
}
\]

Everything else is downstream.

First determine the calculus of descriptions, the gauge they cannot resolve, the defects left by failed composition, and the information recoverable from those defects.

Operationally:

\[
\\boxed{
\\text{Which measurements survive gauge, which restricted families are complete,
and when do genuinely new orders of information emerge?}
}
\]

Then see what kinds of universes realize it.
