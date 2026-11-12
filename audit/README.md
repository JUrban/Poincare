# Statement audit

A formal proof is only as good as its statement. The files here, together with three sanity files of `src/`,
test whether the statements in `src/poincare_statement.ml` mean what they should. They build on the main
development; load them with `loadt "audit/make.ml";;`, or with `loadt "audit/check.ml";;` to also print the
results. Both are run from the repository root.

## `poincare_blind.ml`, `pc_audit_equiv.ml`, `pc_audit_blind_proved.ml`: an independent formalization

`poincare_blind.ml` formalizes the conjecture in a topological and in a smooth form, as `BLIND_POINCARE_TOP` and
`BLIND_POINCARE_SMOOTH`. It was written from two texts alone, without access to `src/`: the introduction of
Morgan-Tian (pp. ix-x, with Corollary 0.2(a) and its footnote on smoothing 3-manifolds) and J. Milnor's official
Clay problem description "The Poincare Conjecture". It uses its own definitions throughout: closed topological
and smooth 3-manifolds (charts onto open subsets of R^3, second countability), simple connectivity in the based
form (nonempty, path connected, every loop null-homotopic with its base point fixed), C^k maps by partial
derivatives, and diffeomorphism with the 3-sphere in its stereographic atlas.

`pc_audit_equiv.ml` proves that the two formalizations are logically equivalent, for every carrier type:

    POINCARE_TOP_BLIND_EQUIV    : |- !u:A->bool. POINCARE_STATEMENT u <=> BLIND_POINCARE_TOP u
    POINCARE_SMOOTH_BLIND_EQUIV : |- !u:A->bool. POINCARE_SMOOTH_STATEMENT u <=> BLIND_POINCARE_SMOOTH u

Both are proved hypothesis by hypothesis, for every topology (and atlas) on the type, so neither uses the
conjecture itself. The differences that had to be bridged:
- charts onto all of R^3 against charts onto open subsets of R^3;
- second countability, which the blind form requires and ours does not: it is automatic for compact, locally
  Euclidean spaces (`AUDEQ_COMPACT_LOCALLY_SECOND_COUNTABLE`);
- simple connectivity: ours asks that any two loops be freely homotopic as loops, with nonemptiness stated
  separately; the blind form is the based one. The step with mathematical content turns a free homotopy of a loop
  to a constant loop into a based null-homotopy, by an explicit reparametrization of the square
  (`AUDEQ_LOOP_STAGE1`, `AUDEQ_LOOP_STAGE2`);
- smoothness by partial derivatives at points against Frechet derivatives within the set (the same on open sets);
- the smooth conclusion: ours asks for a smooth immersion into R^4 that is a homeomorphism onto the unit sphere,
  the blind form for a diffeomorphism with the sphere in its stereographic atlas. They are equivalent by the
  inverse function theorem (`AUDEQ_SMOOTH_CONCLUSION_EQ`).

`pc_audit_blind_proved.ml` then proves the independent statements outright, from the headline theorems:

    BLIND_POINCARE_TOP_PROVED    : |- BLIND_POINCARE_TOP (:A)
    BLIND_POINCARE_SMOOTH_PROVED : |- BLIND_POINCARE_SMOOTH (:A)

## Sanity theorems

The following 30 theorems, in `src/poincare_statement_sanity.ml`, `src/pc_mfd_examples.ml` and
`src/pc_audit_sanity.ml`, test the statement definitions on examples. Each would catch a typical formalization
error: a vacuous or contradictory clause, a missing hypothesis, or a definition that means something else. All are
proved without hypotheses.

- **The hypotheses can be met, and the conclusion is the standard sphere.**
  - `POINCARE_HYPOTHESES_SPHERE_3`: the unit sphere of R^4 satisfies all hypotheses of `POINCARE_STATEMENT`;
    `POINCARE_CONVERSE`: so does every space homeomorphic to it.
  - `SPHERE3_ATLAS`, `SPHERE3_INCLUSION_IMMERSION`, `POINCARE_SMOOTH_HYPOTHESES_SPHERE_3` and
    `POINCARE_SMOOTH_CONCLUSION_SPHERE_3`: the 3-sphere with its stereographic atlas satisfies the hypotheses of
    `POINCARE_SMOOTH_STATEMENT`, and its inclusion into R^4 satisfies the conclusion. `SPHERE2_ATLAS`,
    `SPHERE2_INCLUSION_IMMERSION` and `OPEN_SET_ATLAS`: the same notions in dimension 2 and on open sets.
- **The definitions mean what they should.**
  - `SIMPLY_CONNECTED_SPACE_EUCLIDEAN`: for subsets of R^N, `simply_connected_space` agrees with the library's
    `simply_connected`; `SIMPLY_CONNECTED_SPACE_SPHERE_3`: the 3-sphere is simply connected;
    `NOT_SIMPLY_CONNECTED_SPACE_CIRCLE`: the circle is not; `NOT_SIMPLY_CONNECTED_SPACE_TWO_SPHERES`:
    nor is the union of two disjoint 3-spheres; `SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE`: simple
    connectivity implies path connectedness.
  - `LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN`: for subsets of R^N, `locally_euclidean_space (:M)` means that every
    point has an open neighbourhood homeomorphic to R^M; `LOCALLY_EUCLIDEAN_SPACE_SPHERE_3`: the 3-sphere is
    locally Euclidean of dimension 3; `NOT_LOCALLY_EUCLIDEAN_SPACE_SPHERE_2`: the 2-sphere is not;
    `LOCALLY_EUCLIDEAN_SPACE_DIMENSION_UNIQUE`: a nonempty space is not locally Euclidean in two dimensions 3
    and 4.
  - `LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC` and `SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC`: both notions are invariant
    under homeomorphism.
  - `SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN` and `SMOOTH_MANIFOLD_ATLAS_OPEN_OVERLAP`: a smooth atlas makes
    the space locally Euclidean, and its overlaps are open; `SMOOTH_IMMERSION_DERIVATIVE_WORKS`: the derivative
    in the immersion condition is the derivative of the map in the chart; `NOT_SMOOTH_IMMERSION_CONST`: a
    constant map on a nonempty manifold is not an immersion.
- **Each hypothesis matters.**
  - `POINCARE_NEEDS_NONEMPTY`: the empty space satisfies every other hypothesis and is not homeomorphic to the
    sphere.
  - `POINCARE_NEEDS_NO_BOUNDARY`: the closed 3-ball is compact, Hausdorff, nonempty and simply connected, but not
    locally Euclidean of dimension 3, so manifolds with boundary are excluded.
- **Why the headline theorems are stated for a type variable.**
  - `POINCARE_STATEMENT_NUM`, `POINCARE_SMOOTH_STATEMENT_NUM` and `POINCARE_EMBEDDED_STATEMENT_3`: on the
    countable type num, and for subsets of R^3, the statements hold vacuously (no space there satisfies the
    hypotheses). This is why
    `check.ml` accepts only conclusions `POINCARE_STATEMENT (:A)` for a type variable `A`, which hold at every type.
- `POINCARE_STATEMENT_IMP_EMBEDDED`: the topological form at the type real^N implies the form for subsets of R^N,
  in the library's notions.
