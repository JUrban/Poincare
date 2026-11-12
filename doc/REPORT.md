# The Poincare conjecture in HOL Light: comparison of the sources, the Lean formalizations and the HOL Light formalization

This report compares three kinds of objects.

- **The sources.**
  - J. Morgan and G. Tian, *Ricci Flow and the Poincare Conjecture*, Clay Mathematics Monographs 3, American
    Mathematical Society and Clay Mathematics Institute, 2007 ("MT" below): the blueprint of the smooth proof. It
    is cited by chapter, numbered result and printed page ("MT Theorem 15.9, p. 363"); the Introduction has roman
    page numbers (pp. ix-xlii).
  - E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Graduate Texts in Mathematics 47, Springer, 1977: the
    source of the triangulation theorem. Moise numbers theorems within sections, so "Theorem 35.2" is Theorem 2 of
    Section 35.
  - J. Milnor, *The Poincare Conjecture*, the problem description of the Clay Mathematics Institute (8 pages),
    cited by page.
  - The further sources of Section 5.
- **The Lean formalizations**, two independent complete proofs of both the smooth and the topological form:
  - **Q**: qinz1yang/differential-geometry (Z. Qin, Y. Liao, A. Khaitan, B. Chow and others; Apache-2.0), release
    v0.1.3, commit 7a48598d35109aa99d1cc678e2724c213cdf4ff3 (Lean v4.33.1, Mathlib v4.33.1). Paths are relative
    to DifferentialGeometry/; RF abbreviates Geometry/Flow/RicciFlow and ST abbreviates RF/Surgery/Topology.
  - **F**: frenzymath/PoincareConjecture (FrenzyMath, Peking University), commit
    62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Lean v4.33.1, Mathlib v4.33.1). Paths are relative to the
    repository root. The repository has no license; it was read for comparison only.

  Lean citations are file:line at these commits. Lean notation is transliterated to ASCII: Real for the real
  numbers, I3 for the model with corners `modelWithCornersSelf Real (EuclideanSpace Real (Fin 3))`,
  `Homeomorph M N` and `Diffeomorph I3 I3 M N inf` for the infix notations, and inf for the smoothness index
  written with the infinity symbol (C^infinity, not analytic).
- **The HOL Light formalization**: this repository. The development is in src/, the statement audit in audit/,
  the HOLTrace scripts in holtrace/ and the documentation in doc/.

## 0. Summary

**Headline results.** Each theorem below has no hypotheses and is proved using only HOL Light's three standard
axioms (ETA_AX, SELECT_AX, INFINITY_AX). The development contains no unproved steps.

| result | HOL theorem | file |
|---|---|---|
| The Poincare conjecture, topological form: every compact, Hausdorff, nonempty, simply connected space that is locally Euclidean of dimension 3 is homeomorphic to the unit sphere of R^4 | POINCARE_TOP : `\|- POINCARE_STATEMENT (:A)` | src/pc_poincare_top.ml |
| The smooth form, MT Corollary 0.2(a): every closed, nonempty, simply connected smooth 3-manifold is diffeomorphic to S^3, stated as the existence of a smooth immersion into R^4 that is a homeomorphism onto the unit sphere | POINCARE_SMOOTH : `\|- POINCARE_SMOOTH_STATEMENT (:A)` | src/pc_smt_smooth.ml |
| The topological form for compact subsets of R^N, stated with notions of the HOL Light library only | POINCARE_EMBEDDED : `\|- POINCARE_EMBEDDED_STATEMENT (:N)` | src/pc_poincare_top.ml |
| Moise's theorem in the compact case: every compact Hausdorff space that is locally Euclidean of dimension 3 has a smooth atlas compatible with its topology | MOI_SST_HEADLINE : `\|- !u:A->bool. MOISE_SMOOTHING_STATEMENT u` | src/pc_moi_status.ml |

The three Poincare statements are defined in src/poincare_statement.ml and MOISE_SMOOTHING_STATEMENT in
src/pc_interfaces.ml. A and N are type variables, and a HOL theorem holds at every instance of its type
variables, so the theorems hold for spaces on every carrier type; the instance A = real^4 already covers every
closed 3-manifold up to homeomorphism (Section 1.8). POINCARE_TOP is POINCARE_FROM_SMOOTH_AND_MOISE
(src/pc_interfaces.ml) applied to POINCARE_SMOOTH and MOI_SST_HEADLINE; POINCARE_EMBEDDED is
POINCARE_STATEMENT_IMP_EMBEDDED (src/poincare_statement_sanity.ml) applied to POINCARE_TOP at A = real^N.

**What was checked, and how.**
- *Proofs.* check.ml loads the development (the 1,090 files of src/, on top of HOL Light's Multivariate library)
  in a fresh session. For each headline theorem it prints the number of hypotheses (0) and checks that the
  conclusion is exactly the statement constant applied to the universe of a type variable; then it prints the
  axioms: only the three standard ones. A scan of every loaded file for unproved-theorem constructs found none
  (Section 6.2).
- *Independent re-checking* (Section 6.3). The whole development, from HOL Light's core on, was recorded as
  HOLTrace proof traces in 11 parts (666.6 million inferences, 20.1 GB). HOLTrace's C checker accepted every part,
  and a replay through HOL Light's kernel in one session, after the statement files had been loaded, re-derived
  the four headline theorems with no hypotheses and only the three standard axioms.
- *Statements* (Sections 1 and 2). A clause-by-clause comparison with MT, Milnor, Moise and the Lean statements;
  the definitional dependency cone (six definitions, all in src/poincare_statement.ml); 30 sanity theorems; an
  independent formalization written from the texts of MT and Milnor alone and proved equivalent to ours; an
  adversarial review, which found no defect.
- *The sources* (Sections 3.5 and 5): where the HOL proof follows MT or Moise and where it takes another route.
  The errors and gaps found in the sources are listed in doc/SOURCE_NOTES.md.

**The one caveat on the human side.** No proof checker can decide whether a formal statement means what the
informal one says. That the statements are the Poincare conjecture is for readers to confirm. Section 2.1 lists
what to read (about 130 lines of definitions and statements, and 36 more for Moise's theorem), and Section 1
compares the statements clause by clause.

## 1. The statements

### 1.1 How to read the comparison

All statements have the shape `!M. HYP(M) ==> CONC(M)`: fewer hypotheses or a stronger conclusion make a statement
stronger. In the tables, "=" means equivalent, by the argument given (most of these arguments are HOL theorems,
Section 2.4). No clause makes the HOL statement stronger or weaker than the sources: every difference found is an
equivalent reformulation or a redundant hypothesis.

### 1.2 The texts

**MT, Introduction.** p. ix: "In this book we present a complete and detailed proof of The Poincare Conjecture:
every closed, smooth, simply connected 3-manifold is diffeomorphic to S^3." Its footnote 1 (p. ix): "Every
topological 3-manifold admits a differentiable structure and every homeomorphism between smooth 3-manifolds can
be approximated by a diffeomorphism. Thus, classification results about topological 3-manifolds up to
homeomorphism and about smooth 3-manifolds up to diffeomorphism are equivalent. In this book 'manifold' means
'smooth manifold.'" p. x, after Theorem 0.1: "Corollary 0.2. (a) A closed, simply connected 3-manifold is
diffeomorphic to S^3." The proof of Theorem 0.1 (p. 415) combines Theorem 15.9 (Ricci flow with surgery for all
time), Theorem 18.1 (finite-time extinction) and Corollary 15.4 (the topology of the surgeries).

**Milnor.** p. 1: the three-dimensional unit sphere is "the locus of all points (x, y, z, w) in four-dimensional
Euclidean space which have distance exactly 1 from the origin"; "Question. If a compact three-dimensional
manifold M^3 has the property that every simple closed curve within the manifold can be deformed continuously to
a point, does it follow that M^3 is homeomorphic to the sphere S^3?"; and "the hypothesis that every simply
connected closed 3-manifold is homeomorphic to the 3-sphere has been known as the Poincare Conjecture".
Footnote 2 (p. 1): "To Poincare, manifolds were always smooth or polyhedral, so that his term 'homeomorphism'
referred to a smooth or piecewise linear homeomorphism." p. 5: "In dimension 3, the discrepancies between
topological, piecewise linear, and differentiable theories disappear", with references to Hirsch, Munkres and
Moise's book.

**Moise.** Introduction, p. 4: "An n-manifold is a separable metric space M^n in which every point has a
neighborhood homeomorphic to R^n." Theorem 35.3 (p. 252), the triangulation theorem for 3-manifolds: "Let M be a
3-manifold. Then there is a complex K such that M and |K| are homeomorphic." The book does not treat smooth
structures; the passage from a triangulation to a smooth structure is the smoothing of combinatorial
3-manifolds (Section 3.2).

The texts thus give two forms: the classical topological one (Milnor) and the smooth one (MT), equivalent by
MT's footnote 1. The HOL development proves both, as do both Lean formalizations.

### 1.3 The HOL statements

src/poincare_statement.ml has no `needs` line: it is loaded after HOL Light's Multivariate library (make.ml) and
consists of six definitions and the three statements. The statements, verbatim:

```
let POINCARE_STATEMENT = new_definition
 `POINCARE_STATEMENT (u:A->bool) <=>
    !top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:3) top /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top
        ==> top homeomorphic_space
            subtopology euclidean (sphere(vec 0:real^4,&1))`;;

let POINCARE_SMOOTH_STATEMENT = new_definition
 `POINCARE_SMOOTH_STATEMENT (u:A->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top
        ==> ?f:A->real^4.
              smooth_immersion_into atlas f /\
              homeomorphic_map (top,subtopology euclidean (sphere(vec 0,&1))) f`;;

let POINCARE_EMBEDDED_STATEMENT = new_definition
 `POINCARE_EMBEDDED_STATEMENT (u:N->bool) <=>
    !M:real^N->bool.
        compact M /\ ~(M = {}) /\ simply_connected M /\
        (!x. x IN M
             ==> ?U. open_in (subtopology euclidean M) U /\ x IN U /\
                     U homeomorphic (:real^3))
        ==> M homeomorphic sphere(vec 0:real^4,&1)`;;
```

From src/pc_interfaces.ml, verbatim:

```
let MOISE_SMOOTHING_STATEMENT = new_definition
 `MOISE_SMOOTHING_STATEMENT (u:A->bool) <=>
    !top:A topology.
        hausdorff_space top /\ compact_space top /\
        locally_euclidean_space (:3) top
        ==> ?atlas:((A->bool)#(A->real^3))->bool.
                smooth_manifold_atlas top atlas`;;
```

The six definitions, verbatim without their comments:

```
let continuously_differentiable = define
 `(continuously_differentiable 0 s (f:real^M->real^N) <=>
   f continuous_on s) /\
  (!n. continuously_differentiable (SUC n) s f <=>
       ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
            !h. continuously_differentiable n s (\x. f' x h))`;;

let smooth_map_on = new_definition
 `smooth_map_on M (f:real^M->real^N) <=>
    !n. continuously_differentiable n M f`;;

let simply_connected_space = new_definition
 `simply_connected_space (top:A topology) <=>
    !p q. path_in top p /\ p(&1) = p(&0) /\
          path_in top q /\ q(&1) = q(&0)
          ==> homotopic_with (\r. r(&1) = r(&0))
                (subtopology euclideanreal (real_interval[&0,&1]),top) p q`;;

let locally_euclidean_space = new_definition
 `locally_euclidean_space (s:N->bool) (top:A topology) <=>
    !x. x IN topspace top
        ==> ?U. open_in top U /\ x IN U /\
                subtopology top U homeomorphic_space (euclidean:(real^N)topology)`;;

let smooth_manifold_atlas = new_definition
 `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) <=>
    (!U phi. (U,phi) IN atlas
             ==> open_in top U /\ open (IMAGE phi U) /\
                 homeomorphic_map (subtopology top U,
                                   subtopology euclidean (IMAGE phi U)) phi) /\
    (!x. x IN topspace top ==> ?U phi. (U,phi) IN atlas /\ x IN U) /\
    (!U phi V psi.
         (U,phi) IN atlas /\ (V,psi) IN atlas
         ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
                 !x. x IN U INTER V ==> g(phi x) = psi x)`;;

let smooth_immersion_into = new_definition
 `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^M) <=>
    !U phi. (U,phi) IN atlas
            ==> ?g. smooth_map_on (IMAGE phi U) g /\
                    (!x. x IN U ==> g(phi x) = f x) /\
                    (!y h. y IN IMAGE phi U /\ frechet_derivative g (at y) h = vec 0
                           ==> h = vec 0)`;;
```

Reading notes:
- The argument u, like `(:3)`, only fixes a type (Section 1.8). A space is a topology `top` on a type A, with
  points `topspace top`; hausdorff_space, compact_space, homeomorphic_space, homeomorphic_map, subtopology,
  path_in and homotopic_with are HOL Light's general topology (Multivariate/metric.ml), and euclidean is the
  topology of real^N (Multivariate/topology.ml).
- simply_connected_space has the form of the library's simply_connected for subsets of real^N
  (Multivariate/paths.ml); as there, the empty space is simply connected, hence `~(topspace top = {})`.
- continuously_differentiable is the C^k predicate of the Navier-Stokes HOL Light development, with the same text
  as src/ns_smooth.ml (HOL Light accepts an identical redefinition and rejects a different one): C^(n+1) means
  differentiable within s at every point of s with every directional derivative `\x. f' x h` of class C^n.
- In smooth_manifold_atlas the transition condition is written without inverse functions (a smooth g with
  `g(phi x) = psi x` on U INTER V), in both orders; the atlas need not be maximal. In smooth_immersion_into the
  derivative is frechet_derivative, a choice term, which is the derivative of g because g is smooth on the open
  set phi U (SMOOTH_IMMERSION_DERIVATIVE_WORKS, Section 2.3).

### 1.4 The Lean statements

**Q.** Topology/ThreeManifold/Poincare.lean:12-16 (transliterated):

```
theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (Homeomorph M (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1))
```

This is, up to the order of the arguments, the statement that Mathlib v4.33.1 records as
`proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three`. Its proof (lines 17-21) chooses a new smooth
atlas on M (Moise), applies the smooth theorem and keeps the underlying homeomorphism. The smooth theorem,
RF/Surgery/Skeleton/PoincareEndgame.lean:103-107:

```
theorem smoothPoincareConjecture_holds
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold I3 inf M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] :
    Nonempty (Diffeomorph I3 I3 M (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) inf)
```

Q's Moise theorem, exists_isManifold_three (Topology/PiecewiseLinear/Moise352Producer.lean:33-37), assumes
T2Space, CompactSpace and a ChartedSpace structure over EuclideanSpace Real (Fin 3) on M, and concludes
`exists C : ChartedSpace (EuclideanSpace Real (Fin 3)) M, IsManifold I3 inf M` (with C as the instance).

**F.** Comparator/Challenge.lean:11-22:

```
abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1

def SmoothPoincare : Prop :=
  forall (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold I3 inf M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph I3 I3 M ThreeSphere inf)

def TopologicalPoincare : Prop :=
  forall (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (Homeomorph M ThreeSphere)
```

The challenge theorems (Challenge.lean:26-30) are proved in Comparator/Solution.lean:12-16 from
PoincareMT.smoothPoincareSkeleton and PoincareMT.topologicalPoincareSkeleton
(PoincareLib/Topology/Manifold/Poincare.lean:23-32); Comparator/config.json names them, permits only the axioms
propext, Classical.choice and Quot.sound, and enables the independent nanoda checker. F's smoothing step,
M76SmoothingStatement (PoincareLib/Topology/Manifold/Poincare/Smoothing/Service.lean:25-30), gives every compact,
Hausdorff, second countable topological 3-manifold that is connected and nonempty
(PoincareLib/Topology/Manifold/Poincare/Smoothing/Basic.lean:17-19) a homeomorphic smooth model: another type with
a smooth structure.

Both formalizations state their headline theorems with Mathlib notions only (ChartedSpace, IsManifold, T2Space,
CompactSpace, SecondCountableTopology, SimplyConnectedSpace, which includes nonemptiness and path-connectedness,
Homeomorph, Diffeomorph, and Metric.sphere in EuclideanSpace with Mathlib's stereographic smooth structure).

### 1.5 The topological form, clause by clause

| clause | Milnor (p. 1), MT (p. ix) | Q (Poincare.lean:12-16) | F (Challenge.lean:19-22) | HOL POINCARE_STATEMENT | dir |
|---|---|---|---|---|---|
| the space | "a compact three-dimensional manifold M^3" | a type M with a topology | the same | a topology `top` on a type A; the points are `topspace top` | = |
| Hausdorff | part of "manifold" | `T2Space M` | `T2Space M` | `hausdorff_space top` | = |
| second countable | part of the usual definition of a manifold (Moise: separable metric) | not assumed | `SecondCountableTopology M` | not assumed | = (implied, 1.8) |
| locally Euclidean of dimension 3, no boundary | "three-dimensional manifold", "closed" | `ChartedSpace (EuclideanSpace Real (Fin 3)) M` | the same | `locally_euclidean_space (:3) top` | = |
| compact | "compact", "closed" | `CompactSpace M` | `CompactSpace M` | `compact_space top` | = |
| nonempty | implicit | part of `SimplyConnectedSpace M` | the same | `~(topspace top = {})` | = |
| simply connected | "every simple closed curve ... can be deformed continuously to a point" | `SimplyConnectedSpace M` | the same | `simply_connected_space top` | = (1.8) |
| conclusion | homeomorphic to the unit sphere of R^4 | `Nonempty (Homeomorph M (Metric.sphere 0 1))` in `EuclideanSpace Real (Fin 4)` | `Nonempty (Homeomorph M ThreeSphere)` | `top homeomorphic_space subtopology euclidean (sphere(vec 0:real^4,&1))` | = |
| carrier | | `M : Type u`, every universe | the same | A a type variable, every type | = (1.8) |

### 1.6 The smooth form, clause by clause

| clause | MT (p. ix; Corollary 0.2(a), p. x) | Q (PoincareEndgame.lean:103-107) | F (Challenge.lean:13-17) | HOL POINCARE_SMOOTH_STATEMENT | dir |
|---|---|---|---|---|---|
| smooth structure | "smooth"; "In this book 'manifold' means 'smooth manifold'" | `ChartedSpace ...` and `IsManifold I3 inf M` | the same | `smooth_manifold_atlas top atlas`: a C^infinity atlas, not necessarily maximal | = |
| Hausdorff, compact, nonempty, simply connected | "closed", "simply connected" | `T2Space`, `CompactSpace`, `SimplyConnectedSpace` | the same | `hausdorff_space`, `compact_space`, `~(topspace top = {})`, `simply_connected_space` | = |
| connected | implied | `ConnectedSpace M` (redundant) | not assumed | not assumed (implied) | = |
| second countable | | not assumed | `SecondCountableTopology M` (redundant) | not assumed | = |
| conclusion | "diffeomorphic to S^3" | `Nonempty (Diffeomorph I3 I3 M S^3 inf)`, S^3 with Mathlib's smooth structure | the same with ThreeSphere | `?f:A->real^4. smooth_immersion_into atlas f /\ homeomorphic_map (top,S^3) f` | = (1.8) |

### 1.7 Moise's theorem, clause by clause

| clause | MT footnote 1 (p. ix); Moise (p. 4, Theorem 35.3) | Q exists_isManifold_three | F M76SmoothingStatement | HOL MOISE_SMOOTHING_STATEMENT |
|---|---|---|---|---|
| hypotheses | "every topological 3-manifold"; Moise: separable metric, locally homeomorphic to R^3 | `T2Space`, `CompactSpace`, `ChartedSpace (EuclideanSpace Real (Fin 3)) M` | the same, `SecondCountableTopology`, M connected and nonempty | `hausdorff_space`, `compact_space`, `locally_euclidean_space (:3)` |
| conclusion | "admits a differentiable structure"; Moise 35.3: homeomorphic to a polyhedron | a new `ChartedSpace` on M with `IsManifold I3 inf` | a smooth model: another type with a smooth structure, homeomorphic to M | a `smooth_manifold_atlas` on `top` |

All three are stated for compact spaces, which is all the topological form needs. In HOL and Q the smooth
structure lives on the given space, with charts that are homeomorphisms for its topology; F's model gives one by
transport. The second half of MT's footnote 1 (approximation of homeomorphisms by diffeomorphisms) is not
needed, since the smooth form already concludes a homeomorphism (POINCARE_FROM_SMOOTH_AND_MOISE).

### 1.8 The differences

**Hausdorff.** The hypothesis is needed: S^3 with one point doubled is compact, locally Euclidean and simply
connected (van Kampen for its two open copies of S^3, which meet in S^3 minus a point), but it is not Hausdorff
and so not homeomorphic to S^3. This standard example is not formalized here. All versions assume Hausdorff.

**Second countability.** A compact space that is locally Euclidean is covered by finitely many chart domains,
each second countable, so it is second countable; Hausdorff is not needed for this
(AUDEQ_COMPACT_LOCALLY_SECOND_COUNTABLE and AUDEQ_BLIND_LOCALLY_EUCLIDEAN_SECOND_COUNTABLE, audit/pc_audit_equiv.ml).
With Hausdorff it is moreover metrizable, which matches Moise's separable metric spaces. HOL and Q do not assume
second countability; F and the independent formalization of Section 2.4 do. The versions are equivalent.

**Nonemptiness.** HOL's simply_connected_space, like the library's simply_connected, holds for the empty space, so
POINCARE_STATEMENT states nonemptiness separately. The empty space satisfies every other hypothesis and is not
homeomorphic to S^3 (POINCARE_NEEDS_NONEMPTY). Mathlib's SimplyConnectedSpace contains nonemptiness, and so does
the independent blind_simply_connected_space; AUDEQ_SIMPLY_CONNECTED_EQ proves
`~(topspace top = {}) /\ simply_connected_space top <=> blind_simply_connected_space top` for every space.

**Simple connectivity.** HOL asks that any two loops be freely homotopic through loops; the textbook definition,
used by Mathlib and by the independent formalization, is path connected with every loop null-homotopic with its
base point fixed. The two are equivalent for every topological space (AUDEQ_SIMPLY_CONNECTED_EQ; the harder
direction turns a free homotopy into a based one by an explicit reparametrization of the square,
AUDEQ_LOOP_STAGE1 and AUDEQ_LOOP_STAGE2). The HOL notion implies path connectedness
(SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE), so two disjoint 3-spheres are excluded
(NOT_SIMPLY_CONNECTED_SPACE_TWO_SPHERES), and on subspaces of real^N it is the library's notion
(SIMPLY_CONNECTED_SPACE_EUCLIDEAN). Milnor's phrasing with simple closed curves is the classical one; in a
3-manifold every loop is homotopic to a simple closed curve, so it is the same condition.

**Local Euclideanity and boundary.** HOL asks for neighbourhoods homeomorphic to all of real^3, the Lean charts
and the independent formalization for open subsets of R^3; a ball is homeomorphic to R^3, so the two agree
(AUDEQ_LOCALLY_EUCLIDEAN_EQ). Neither allows boundary: the closed 3-ball satisfies every other hypothesis
(POINCARE_NEEDS_NO_BOUNDARY). The dimension is 3: no nonempty space is locally Euclidean of dimensions 3 and 4 at
once (LOCALLY_EUCLIDEAN_SPACE_DIMENSION_UNIQUE), and the 2-sphere is not locally Euclidean of dimension 3
(NOT_LOCALLY_EUCLIDEAN_SPACE_SPHERE_2). `(:3)` is the universe of HOL Light's numeral type 3.

**The smooth conclusion.** The statement file defines no diffeomorphisms between manifolds. Its conclusion is a
map f into real^4 that is a homeomorphism onto the unit sphere S^3 and, in every chart of the given atlas, agrees
with a smooth map with injective derivative. Followed by a stereographic chart of S^3 it is, in charts, a smooth
map between open sets of R^3 with invertible derivative, so by the inverse function theorem its inverse is smooth
and f is a diffeomorphism onto S^3 with its structure as a submanifold of R^4, the structure of the two
stereographic charts. Conversely, a diffeomorphism onto S^3 followed by the inclusion into R^4 is such a map.
AUDEQ_SMOOTH_CONCLUSION_EQ proves the equivalence, for every smooth atlas, with the independent notion
blind_diffeomorphic_3 (Section 2.4). The Lean statements use Mathlib's Diffeomorph and smooth sphere.

**Atlases and smoothness classes.** An atlas determines its maximal atlas and the same smooth maps, so
quantifying over atlases is quantifying over smooth structures. continuously_differentiable takes derivatives
within the set; on open sets, where the statements use it (SMOOTH_MANIFOLD_ATLAS_OPEN_OVERLAP), it is the
ordinary C^n and agrees with the independent definition by partial derivatives (AUDEQ_BLIND_CK_EQ). Mathlib's
index inf means C^infinity.

**Carrier types.** The statements take a dummy argument that fixes a type A, and the theorems are proved at a type
variable: `|- POINCARE_STATEMENT (:A)` holds at every type by type instantiation. Every nonempty closed 3-manifold
has the cardinality of the reals (it is a finite union of open sets homeomorphic to R^3), so it is homeomorphic to
a space whose points lie in real^4, and the instance A = real^4 is the whole conjecture. At types of smaller
cardinality the hypotheses cannot be met and the statements hold vacuously (POINCARE_STATEMENT_NUM,
POINCARE_SMOOTH_STATEMENT_NUM, POINCARE_EMBEDDED_STATEMENT_3). check.ml therefore accepts a headline theorem only
if its conclusion is the statement constant at a type variable. The Lean statements quantify over `M : Type u` in
every universe u, and the space is the whole type M, while in HOL it is the subset `topspace top` of A. Both
conventions cover all spaces up to homeomorphism.

**The embedded form.** POINCARE_EMBEDDED_STATEMENT (:N) uses only notions of the HOL Light library (compact,
simply_connected, homeomorphic and the relative topology of a subset of real^N), so it needs no trust in the new
definitions. It is weaker than POINCARE_STATEMENT: for each N it is a special case of POINCARE_STATEMENT
(:real^N) (POINCARE_STATEMENT_IMP_EMBEDDED), and for dimindex(:N) <= 3 it holds vacuously, since a compact
3-manifold in R^3 would be open by invariance of domain (POINCARE_EMBEDDED_STATEMENT_3). Every closed 3-manifold
embeds in some R^N, but that embedding theorem is not part of the statement.

### 1.9 Summary of differences

| item | sources | Q | F | HOL | assessment |
|---|---|---|---|---|---|
| Hausdorff | part of "manifold" | assumed | assumed | assumed | = |
| second countable | part of "manifold" | not assumed | assumed | not assumed | = (compactness) |
| nonempty | implicit | in SimplyConnectedSpace | in SimplyConnectedSpace | separate hypothesis | = |
| simple connectivity | curves deformed to a point | based loops, path connected | the same | any two loops homotopic as loops | = (AUDEQ_SIMPLY_CONNECTED_EQ) |
| charts | | onto open subsets of R^3 | the same | neighbourhoods homeomorphic to R^3 | = (AUDEQ_LOCALLY_EUCLIDEAN_EQ) |
| smooth structure | C^infinity | IsManifold I3 inf | the same | atlas with C^infinity transition maps | = |
| connected (smooth form) | implied | assumed (redundant) | not assumed | not assumed | = |
| smooth conclusion | diffeomorphic to S^3 | Diffeomorph | Diffeomorph | smooth immersion that is a homeomorphism onto S^3 | = (AUDEQ_SMOOTH_CONCLUSION_EQ) |
| Moise | a differentiable structure exists | new atlas on M | homeomorphic smooth model, M connected | smooth atlas on top | = for closed manifolds |

## 2. Auditing the statements

### 2.1 What a reader must check

Only the statement files need to be read; everything else is proof, checked by HOL Light's kernel.

| file | content |
|---|---|
| src/poincare_statement.ml | the six definitions and the three statements of Section 1.3; about 130 lines with comments; no `needs` line |
| src/pc_interfaces.ml | MOISE_SMOOTHING_STATEMENT and the reduction POINCARE_FROM_SMOOTH_AND_MOISE; 36 lines |
| check.ml | the check of the four headline theorems (Section 6.2) |

The library notions they use are defined in Multivariate/metric.ml (topologies, open_in, topspace, subtopology,
homeomorphic_map, homeomorphic_space, compact_space, hausdorff_space, euclideanreal, path_in, homotopic_with),
Multivariate/topology.ml (euclidean, open, sphere, compact, continuous_on, homeomorphic), Multivariate/paths.ml
(simply_connected), Multivariate/derivatives.ml (has_derivative, frechet_derivative) and Multivariate/misc.ml
(real_interval).

### 2.2 The dependency cone

The cone of a statement constant is the set of constants of the development that occur in its definition,
recursively. Read from the two files:

| statement | definitions of the development in its cone, besides the statement itself |
|---|---|
| POINCARE_STATEMENT | 2: locally_euclidean_space, simply_connected_space |
| POINCARE_SMOOTH_STATEMENT | 5: smooth_manifold_atlas, smooth_immersion_into, smooth_map_on, continuously_differentiable, simply_connected_space |
| POINCARE_EMBEDDED_STATEMENT | none: library notions only |
| MOISE_SMOOTHING_STATEMENT | 4: locally_euclidean_space, smooth_manifold_atlas, smooth_map_on, continuously_differentiable |

Everything else is the HOL Light library: topological spaces and their maps, paths and homotopies, the Euclidean
topology, derivatives. No inverse function and no matrix inverse occurs in a statement. The only choice-defined
notion is frechet_derivative (has_derivative also contains a choice term, netlimit, but unfolds to the usual
limit), and it is read only where the map is smooth on an open set.

### 2.3 Sanity theorems

Thirty theorems test the statement definitions on examples. They are in src/poincare_statement_sanity.ml (7),
src/pc_mfd_examples.ml (7) and src/pc_audit_sanity.ml (16); audit/check.ml prints each with its number of
hypotheses (0 for all) and the axioms (the three standard ones).

| kind | theorems | what it rules out |
|---|---|---|
| agreement with the library on subspaces of real^N | SIMPLY_CONNECTED_SPACE_EUCLIDEAN, LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN | new notions that differ from the library's simply_connected or from "locally homeomorphic to R^3" |
| S^3 satisfies all hypotheses, of both forms | SIMPLY_CONNECTED_SPACE_SPHERE_3, LOCALLY_EUCLIDEAN_SPACE_SPHERE_3, POINCARE_HYPOTHESES_SPHERE_3, SPHERE3_ATLAS (the two stereographic charts), SPHERE3_INCLUSION_IMMERSION, POINCARE_SMOOTH_HYPOTHESES_SPHERE_3, POINCARE_SMOOTH_CONCLUSION_SPHERE_3 | a hypothesis class that is empty for a definitional reason, which would make a statement trivially true; a conclusion that S^3 itself fails |
| other smooth structures | SPHERE2_ATLAS, SPHERE2_INCLUSION_IMMERSION, OPEN_SET_ATLAS (open subsets of real^N with the identity chart) | an atlas notion that only spheres of one dimension meet |
| invariance and converse | LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC, SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC, POINCARE_CONVERSE (every space homeomorphic to S^3, on any carrier type, meets all hypotheses) | hypotheses that are not invariant under homeomorphism, or that a copy of S^3 fails |
| relations between the notions | SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN, SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE, POINCARE_STATEMENT_IMP_EMBEDDED | smooth hypotheses that do not imply the topological ones; simple connectivity without connectedness |
| teeth | NOT_SIMPLY_CONNECTED_SPACE_CIRCLE, NOT_SIMPLY_CONNECTED_SPACE_TWO_SPHERES, POINCARE_NEEDS_NONEMPTY, POINCARE_NEEDS_NO_BOUNDARY (the closed 3-ball), NOT_LOCALLY_EUCLIDEAN_SPACE_SPHERE_2, LOCALLY_EUCLIDEAN_SPACE_DIMENSION_UNIQUE | a simple connectivity that the circle or two disjoint 3-spheres satisfy; a missing nonemptiness hypothesis; manifolds with boundary; the wrong dimension |
| the immersion clause | SMOOTH_MANIFOLD_ATLAS_OPEN_OVERLAP, SMOOTH_IMMERSION_DERIVATIVE_WORKS, NOT_SMOOTH_IMMERSION_CONST | a Hilbert-choice derivative read where it is not the derivative; an immersion clause without force (a constant map) |
| negative controls | POINCARE_STATEMENT_NUM, POINCARE_SMOOTH_STATEMENT_NUM, POINCARE_EMBEDDED_STATEMENT_3 | a check that would accept a vacuous instance at a small type as the headline theorem |

### 2.4 An independent formalization

audit/poincare_blind.ml (20 definitions, 249 lines, no `needs` line) was written independently, from MT pp. ix-x,
Milnor's problem description and the HOL Light library alone, without access to the files of src/. It defines
BLIND_POINCARE_TOP and BLIND_POINCARE_SMOOTH from its own notions: topological 3-manifolds as Hausdorff, second
countable spaces with charts onto open subsets of real^3; simple connectivity as nonempty, path connected and
every loop null-homotopic with its base point fixed; C^k by first partial derivatives; smooth atlases, smooth
maps between atlases and diffeomorphisms; and S^3 with the atlas of the stereographic projections from the two
poles. audit/pc_audit_equiv.ml (about 1,250 lines, 44 theorems), whose load closure is eight files of src/ (the
statement file, the sanity file, src/pc_mfd_examples.ml, src/pc_mfd_base.ml and the smooth calculus) and the
independent file, proves

```
POINCARE_TOP_BLIND_EQUIV    : |- !u:A->bool. POINCARE_STATEMENT u <=> BLIND_POINCARE_TOP u
POINCARE_SMOOTH_BLIND_EQUIV : |- !u:A->bool. POINCARE_SMOOTH_STATEMENT u <=> BLIND_POINCARE_SMOOTH u
```

one hypothesis at a time, for every topology and every atlas on A; neither proof uses the Poincare conjecture.
audit/pc_audit_blind_proved.ml then gives BLIND_POINCARE_TOP_PROVED : `|- BLIND_POINCARE_TOP (:A)` and
BLIND_POINCARE_SMOOTH_PROVED : `|- BLIND_POINCARE_SMOOTH (:A)` from the headline theorems. The differences that the
equivalence proof bridges:

| difference | independent version | ours | bridge in audit/pc_audit_equiv.ml |
|---|---|---|---|
| the 3-sphere | blind_sphere3_topology | `subtopology euclidean (sphere(vec 0,&1))` | AUDEQ_SPHERE3_TOPOLOGY (the same term) |
| charts | neighbourhoods homeomorphic to open subsets of real^3 | neighbourhoods homeomorphic to real^3 | AUDEQ_LOCALLY_EUCLIDEAN_EQ |
| second countability | assumed | not assumed | AUDEQ_COMPACT_LOCALLY_SECOND_COUNTABLE, AUDEQ_BLIND_LOCALLY_EUCLIDEAN_SECOND_COUNTABLE |
| simple connectivity | nonempty, path connected, based null-homotopies | free loop homotopies; nonemptiness separate | AUDEQ_SIMPLY_CONNECTED_EQ, through AUDEQ_LOOP_STAGE1, AUDEQ_LOOP_STAGE2 |
| C^k | first partial derivatives at points | Frechet derivatives within the set | AUDEQ_BLIND_CK_EQ, AUDEQ_BLIND_SMOOTH_EQ (on open sets) |
| atlases | blind_smooth_atlas_3 | smooth_manifold_atlas | AUDEQ_ATLAS_EQ |
| smooth structure of S^3 | the two stereographic charts | the same atlas, sphere3_atlas of src/pc_mfd_examples.ml | AUDEQ_BLIND_SPHERE3_ATLAS: `blind_sphere3_atlas = sphere3_atlas` |
| smooth conclusion | a homeomorphism, smooth with smooth inverse in all charts (blind_diffeomorphic_3) | a smooth immersion that is a homeomorphism onto S^3 | AUDEQ_SMOOTH_CONCLUSION_EQ, with AUDEQ_SMOOTH_GLOBAL_INVERSE (the inverse function theorem) |

There is no genuine discrepancy. Agreement between our statements and the Lean ones could not, by itself, exclude
a mistake common to both; an equivalence with a version written from the texts alone addresses exactly that.

### 2.5 Adversarial review

An adversarial review read only the statement files (src/poincare_statement.ml, src/poincare_statement_sanity.ml
and src/pc_interfaces.ml), the HOL Light library definitions they use, and MT pp. ix-x, without running HOL. Its
verdict: no defect in the four statements or in the definitions they use. Every clause says what the standard
notion says, and every operator parses as intended (it checked the precedences of `==>`, `/\`, `IN`, `INTER`,
`=`, `homeomorphic` and `homeomorphic_space`). It found three formal oddities, all harmless in the statements:
homotopic_with fixes the ends of a homotopy for every real argument, not only on [0,1] (the library's convention;
continuity constrains a homotopy only on the square); the C^(n+1) clause chooses its derivative afresh at each
order (derivatives on open sets are unique); and frechet_derivative is a choice term (read only where the map is
smooth on an open set). It noted two hazards for anyone reusing the definitions elsewhere: on non-open sets the
"within" derivative is not unique (on a single point every map is smooth), and smooth_immersion_into would read a
choice value if the chart images were not open, which smooth_manifold_atlas excludes.

Its requests for further evidence are all theorems of the release (Section 2.3): non-vacuity of the smooth form,
its most important point (SPHERE3_ATLAS and the three theorems after it); the smooth hypotheses imply the
topological ones; negative controls at small types, with a check that rejects them (the type-variable test of
check.ml); path connectedness, invariance under homeomorphism and the converse at every carrier type; teeth for
each hypothesis; no junk in the immersion clause; and an independent notion of diffeomorphism for the smooth
conclusion (Section 2.4). It also pointed out that the topological form needs Moise's theorem, which is not in
MT; that is MOI_SST_HEADLINE. Two optional cross-checks it suggested are not part of the release: a restatement
with metric.ml's own `euclidean_space 3` and `nsphere 3`, and teeth tests for smoothness (for instance that
x |-> abs(x) is not smooth). The review could not inspect the parser state of the sessions in which the
development was built. The HOLTrace replay of Section 6.3 settles this: it re-derives the headline theorems from
primitive inferences in a fresh session in which only the library and the statement files were parsed, and the
kernel checks there that the traces define the statement constants exactly as those files do.

## 3. Architecture

### 3.1 Morgan-Tian's chain

- Corollary 0.2(a) (p. x) follows from Theorem 0.1, whose proof (p. 415) runs: scale a metric to be normalized
  (proof of Corollary 15.10, p. 363); Theorem 15.9 (p. 363) gives a Ricci flow with surgery for all time,
  satisfying Assumptions (1)-(7), pinched toward positive curvature, with strong canonical neighbourhoods and
  kappa-noncollapsed; by Theorem 18.1 (p. 415) it becomes extinct when pi_1 is a free product of finite and
  infinite cyclic groups; Corollary 15.4 (p. 358), from Proposition 15.3 (p. 357), then makes M a connected sum of
  spherical space forms and S^2-bundles over S^1, and its part (2) gives S^3 when M is simply connected. Remark
  0.6(ii) (p. xiv) adds that for a simply connected initial manifold every component of every time slice is
  simply connected.
- Part 1 (Chapters 1-5): Riemannian geometry, nonnegative curvature (Proposition 2.19, p. 31), basics of Ricci
  flow (Theorem 3.11, p. 39, short-time existence and uniqueness, cited from Hamilton and DeTurck; Shi's
  estimates, Theorems 3.28-3.29, p. 51), the maximum principle (Hamilton-Ivey pinching, Theorem 4.32, p. 79),
  convergence (Theorems 5.11 and 5.15).
- Part 2 (Chapters 6-12, from p. 103): reduced length and reduced volume (Chapters 6-7), noncollapsing (Theorem
  8.1, p. 169), kappa-solutions (Chapter 9), bounded curvature at bounded distance (Theorem 10.2, p. 245),
  geometric limits of generalized Ricci flows (Theorems 11.8, p. 272, and 11.19, p. 279), the standard solution
  (Theorem 12.5, p. 296).
- Part 3 (Chapters 13-17, from p. 329): surgery on a delta-neck (Theorem 13.2, p. 332), the definition (Chapter
  14), controlled flows (Chapter 15: Claim 15.1, p. 353, Propositions 15.2 and 15.3, Theorem 15.9, Lemma 15.11,
  Proposition 15.12, p. 365), noncollapsing (Proposition 16.1, p. 367), canonical neighbourhoods (Proposition
  17.1, p. 395), finiteness of surgery times (Lemma 17.12, p. 410).
- Part 4 (Chapters 18-19, from p. 413): finite-time extinction (Theorem 18.1) through the width of families of
  loops and Proposition 18.24, proved in Chapter 19 by curve shrinking and minimal annuli; Section 19.2 has a
  published correction by Morgan and Tian (arXiv:1512.00699). The Appendix (pp. 497-514: Propositions A.19,
  p. 507, A.21 and A.25, p. 514) serves Proposition 15.3.
- On this route MT cite rather than prove, among others: Theorem 3.11; that a simply connected spherical space form
  is S^3; that every diffeomorphism of S^2 is isotopic to the identity or the antipodal map (Smale's theorem, used
  in Corollary 15.4, p. 358) and the other connected-sum facts there; Proposition A.25 (stated without proof,
  p. 514); and the smoothing of topological 3-manifolds (footnote 1, p. ix).

### 3.2 Moise's chain

Theorem 35.3 (p. 252) is proved "by a straightforward analogy" with the 2-dimensional case of Section 8, from
Theorem 35.2 (p. 251): a homeomorphism h from a polyhedral 3-manifold with boundary K in a PL 3-manifold into a PL
3-manifold is approximated, within any strongly positive function on K, by a PL homeomorphism. Moise's own map of
the proof (end of Section 30, pp. 218-219): Section 31 sets up the apparatus for the pseudo-cells of Section 32,
which serve as barriers to "tame oscillations of a surface" in Theorem 33.1, a PL approximation theorem for small
regular neighbourhoods of finite linear graphs in R^3; Theorem 34.1 (polyhedral 3-cells) builds on it; Theorem
35.1, using 34.1, extends 33.1 to the noncompact case; and Theorem 35.2 follows. The tools come from Sections
25-30, among them Stallings' proof of the loop theorem (Section 25, p. 182), bicollar neighbourhoods and an
extension of the loop theorem (Section 26, p. 191), polygons in the boundary of a combinatorial solid torus
(Section 28) and polyhedral interpolation theorems (Section 30), with the PL Schoenflies theorem in R^3 (Section
17, p. 117). The smoothing of the PL structure is not in Moise; Milnor (p. 5) refers to Hirsch and Munkres for it.

### 3.3 The HOL chain

Each layer's statement is a HOL definition (a statement constant), the layers are joined by proved implications
between these definitions, and the headline theorems follow by modus ponens. doc/LAYOUT.md describes the file
families of src/ in detail.

**The top.**

| layer | statement | theorem | file |
|---|---|---|---|
| topological form | POINCARE_STATEMENT | POINCARE_TOP | src/pc_poincare_top.ml |
| embedded form | POINCARE_EMBEDDED_STATEMENT | POINCARE_EMBEDDED, by POINCARE_STATEMENT_IMP_EMBEDDED (src/poincare_statement_sanity.ml) | src/pc_poincare_top.ml |
| topological from smooth | `POINCARE_SMOOTH_STATEMENT u /\ MOISE_SMOOTHING_STATEMENT u ==> POINCARE_STATEMENT u` | POINCARE_FROM_SMOOTH_AND_MOISE | src/pc_interfaces.ml |
| smooth form | POINCARE_SMOOTH_STATEMENT | POINCARE_SMOOTH | src/pc_smt_smooth.ml |
| smooth assembly | the seven statements below imply POINCARE_SMOOTH_STATEMENT | RFS_POINCARE_SMOOTH | src/pc_rfs_assembly.ml |
| Moise | MOISE_SMOOTHING_STATEMENT | MOI_SST_HEADLINE | src/pc_moi_status.ml |

**The seven inputs of the smooth form.** Six statement constants are defined in src/pc_rfs_top.ml, the seventh in
src/pc_smt_defs.ml; POINCARE_SMOOTH is RFS_POINCARE_SMOOTH applied to the seven theorems.

| statement | content | MT | theorem | file |
|---|---|---|---|---|
| METRIC_EXISTENCE_STATEMENT | every compact Hausdorff smooth manifold carries a Riemannian metric | used for Corollary 15.10 | METRIC_EXISTENCE: the metric induced by an embedding into R^(2N+1) (MFD_EMBEDDING_EXISTS, src/pc_mfd_embed.ml) | src/pc_mfd_metric_exists.ml |
| RFS_EXTINCTION_STATEMENT | after scaling to a normalized metric, every closed simply connected Riemannian 3-manifold starts a controlled Ricci flow with surgery that becomes extinct | Theorem 15.9, Corollary 15.10 and Theorem 18.1, simply connected case | RFS_EXTINCTION | src/pc_smt_extinct.ml |
| EVENT_TOPOLOGY_STATEMENT | if the components of the old stage are simply connected, every component discarded at a surgery is S^3, a space form, an S^2-bundle over S^1 or contains RP^3 minus a point | Proposition 15.3 with the Appendix | EVENT_TOPOLOGY, from APX_EVENT_TOPOLOGY_FROM_LEAVES (src/pc_apx_event.ml) | src/pc_smt_evtop.ml |
| RFS_CUTCAP_SC_STATEMENT | cutting along neck spheres and capping keeps every component simply connected | Remark 0.6(ii) | RFS_CUTCAP_SC | src/pc_rfs_ccsc.ml |
| RFS_LISTED_SC_S3_STATEMENT | a simply connected piece of a listed type is diffeomorphic to S^3 | Corollary 15.4(2) | RFS_LISTED_SC_S3, with KILLING_HOPF_COMPONENT (src/pc_geo_kh.ml) for space forms | src/pc_smt_listed.ml |
| RFS_SPHERE_SYSTEM_STATEMENT | if every component of the capped manifold is S^3, so is every component of the manifold before the cut | Corollary 15.4(2) | RFS_SPHERE_SYSTEM | src/pc_smt_system.ml |
| SMT_POINCARE_CONVERSION_STATEMENT | a manifold diffeomorphic to S^3 with its stereographic atlas has a map of the headline form | | SMT_POINCARE_CONVERSION | src/pc_smt_glue.ml |

**Ricci flow with surgery.** RFS_EXTINCTION is P3_FULL_CHAIN_2 (src/pc_p3_route2.ml) at w = (:real^3). That
theorem derives RFS_EXTINCTION_STATEMENT from 65 hypotheses, instances of 62 statement constants, one for each
result of MT and of the background that Part 3 uses; RFS_EXTINCTION discharges all of them. The main ones:
- Part 3 (MT Chapters 13-17): P3E_START_ROUTE (MT Claim 15.1, src/pc_p3e_start.ml), P3_THM_13_2_ROUTE
  (src/pc_p3_s13thm.ml), P3_LEMMA_14_11_ROUTE (src/pc_p3_s14glue.ml), P3E_LEMMA_15_11_ROUTE (src/pc_p3e_15_11.ml),
  P3E_PROP_15_2_ROUTE (src/pc_p3e_152h.ml), P3L_PROP_16_1_ROUTE (src/pc_p3_s161.ml) with the Chapter 16 results of
  `src/pc_p3_s16*.ml`, P3_LEMMA_17_2_ROUTE (src/pc_p3_c172f.ml), P3_LEMMA_17_7_ROUTE (src/pc_p3_c177e.ml),
  P3_PROP_17_1_ROUTE_2 (src/pc_p3_c171e.ml) and P3_LEMMA_17_12_ROUTE (src/pc_p3_c1712r.ml).
- Part 2 (MT Chapters 5-12): P2CFN_P2_ALL (src/pc_p2c_final.ml) proves the statements of Theorems 5.11, 5.15,
  10.2, 11.8, 11.19, 11.31, 12.5 and 12.32, Lemmas 11.2, 11.30, 12.3 and 12.37, Propositions 9.79, 12.7 and 12.31
  and Corollary 9.95; P2AT_THM_8_1 (Theorem 8.1, src/pc_p2a_t81u.ml), P2AY_LEMMA_7_2 (src/pc_p2a_l72w.ml),
  P2AY_COR_7_12 (src/pc_p2a_c712w.ml) and P2AS_PROP_2_19_SEP (src/pc_p2a_219.ml) prove further ones.
- Ricci flow foundations (MT Chapters 3-4): PDEF_CURVATURE_TIME and PDEF_MAXIMAL_FLOW (src/pc_pde_final.ml),
  PDE_UNIQUENESS (src/pc_rf_unique.ml), PDE_GLUE (MT Proposition 3.12, src/pc_rf_glue.ml), RFA_P2_THM_3_28 and
  RFA_P2_THM_3_29 (Shi's estimates, src/pc_rfa_shi328.ml, src/pc_rfa_shi329.ml) and RFA_P2_THM_4_32
  (Hamilton-Ivey pinching, src/pc_rfa_pinch.ml).
- Part 4: P4_EXTINCTION_ALL (src/pc_p4_final.ml), below; topology: RFS_CUTCAP_SC, SMT_SC_SPHERE_SEP (neck spheres
  separate when the components are simply connected, src/pc_smt_sep.ml) and SMT_ORIENTABLE (src/pc_smt_orient.ml).

**Finite extinction.** P4_EXTINCTION_ALL is P4_EXTINCTION_FROM_CUTCAP (src/pc_p4_wire.ml) with RFS_CUTCAP_SC. It
rests on FINITE_EXTINCTION : `|- FINITE_EXTINCTION_STATEMENT (:A)` (src/pc_p4_wire.ml): for a closed simply
connected Riemannian 3-manifold there is a time T such that every controlled history from it that has the pinch
maps of MT Proposition 15.12 and lives beyond T is extinct. FINITE_EXTINCTION is P4_FINITE_EXTINCTION_CM2
(src/pc_p4_align.ml) applied to P4W_GOOD_SWEEPOUT (src/pc_p4_wire.ml, from CM_CHAIN_CM_WIDTH of src/pc_cm_width.ml:
Colding-Minicozzi's Theorem 1.14 with Proposition 1.5), CML_HARMONIC_SPHERE (src/pc_cm_lemma122.ml, their Lemma
1.22) and three topological theorems of src/pc_top_p4.ml (ATOP_P4_DEGREE_ONE_PROVED, ATOP_P4_SC_DEGREE_ONE_PROVED,
ATOP_P4_SMOOTHING_PROVED: degree-one pinch maps keep a map of S^3 essential, i.e. nonzero on H_3; a closed simply
connected 3-manifold has an essential map from S^3; an essential map gives an essential sweepout). Below these lie
their Theorem 2.1 (CM_CHAIN_CM_REPLACEMENT, src/pc_cm_replacement.ml), their Proposition 2.2
(CM_CHAIN_CM_COMPACTNESS, src/pc_cm_compactness.ml), harmonic-map regularity (CM_CHAIN_HM_REGULARITY,
src/pc_hm_regularity.ml), their Theorem 1.7 (P4_CM_DINI_FROM_C1, P4_CM_SLAB_FROM_DINI, src/pc_p4_cm.ml) and the
argument across surgeries (P4_FINITE_EXTINCTION_FROM_WIDTH, src/pc_p4_top.ml).

**Moise.** MOI_SST_HEADLINE is MOI_MOISE_SMOOTHING_FROM_CORES (src/pc_moi_chain.ml) applied to two cores:
- MOI_CORE_STATUS : `|- MOISE_352_COMPLEX_STATEMENT (:7)` (src/pc_moi_core_status.ml), the PL core: a topological
  embedding into R^3 of the polyhedron of a combinatorial 3-manifold (a locally finite complex in R^7) is
  approximated by PL embeddings within any positive continuous function, the rectilinear form of Moise's Theorem
  35.2. It is assembled from HOL forms of results of Moise's Sections 26-35 (among them Theorems 26.6, 28.6,
  30.2-30.4, 31.1, 32.3, 33.1, 34.1 and 35.1), the loop theorem of Section 25 and the PL Schoenflies theorem of
  Section 17.
- MOI_SST_SMOOTH : `|- !u:N->bool. COMBINATORIAL_SMOOTHING_STATEMENT u` (src/pc_moi_status.ml), the smoothing core:
  the polyhedron of a finite combinatorial 3-manifold has a smooth atlas.

From the PL core, src/pc_moi_chain.ml derives a PL atlas on every compact topological 3-manifold (charts whose
transition maps are made PL by the approximation theorem; MOI_PL_ATLAS_FROM_PL_CORE), a finite combinatorial
triangulation by a complex in R^7 (MOI_PL_TRIANGULATION_THM and MOI_TRIANGULATION_FROM_PL_CORE: the compact case
of Theorem 35.3) and, with the smoothing core, the smooth atlas.

**Representations.** HOL Light's library has general topology, homotopy, singular homology, invariance of domain,
real analysis and integration, but no manifolds. The development builds them: a manifold is a topology on a type
with an atlas, a Riemannian metric a matrix field in the coordinates of a preferred chart at each point
(src/pc_mfd_riem.ml). A Ricci flow with surgery is a finite history (src/pc_rfs_history.ml): stages k = 0..n,
closed 3-manifolds (possibly empty) on one carrier type A + num#num#real^3, slabs of Ricci flow between surgery
times, and events that cut along neck spheres, cap with balls and discard components; retained points are the
same points in consecutive stages, so MT's space-time is the view t |-> (stage, atlas, metric at t). Geometric
limits of flows live on the carrier real^3.

### 3.4 The Lean chains

**Q.**
- poincare_conjecture (Topology/ThreeManifold/Poincare.lean:12) combines exists_isManifold_three
  (Topology/PiecewiseLinear/Moise352Producer.lean:33) with smoothPoincareConjecture_holds
  (RF/Surgery/Skeleton/PoincareEndgame.lean:103) and keeps the underlying homeomorphism.
- smoothPoincareConjecture_holds uses smoothPoincareConjecture_of_controlledExtinction (RF/Surgery/Poincare.lean:80):
  it chooses a metric and an orientation, then applies isPoincareStandard_of_controlledExtinction
  (ST/ExtinctionReconstruction.lean:39; MT Proposition 15.3 and Corollary 15.4 iterated backwards over the
  history) and exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
  (Topology/ThreeManifold/PoincareStandardClassification.lean:19), which uses van Kampen for finite connected sums
  (Topology/VanKampen/FiniteConnectedSumFreeProduct.lean:277).
- The extinct history comes from exists_poincare_controlled_extinction (PoincareEndgame.lean:91) through
  exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong
  (ST/CanonicalNeighborhoodsThroughSurgeryStrong.lean:192): finitely many surgery events up to an explicit horizon
  (ST/SingularEventExtinction.lean:33), and extinction by the width of families of loops
  (RF/Extinction/Families/ExtinctionTimeBound.lean:38; MT Chapters 18-19). Smale's theorem in the needed form is
  sphere_isotopy_iff_positive_radial_derivative (Topology/Manifold/SphereOrientationIsotopy.lean:13).
- Moise: exists_isManifold_of_plApproximation_of_plSmoothingCompact
  (Topology/PiecewiseLinear/PLSmoothingCompact.lean:59) builds a PL atlas by approximating the transition maps
  (Moise's Theorem 35.2, through statements named after Moise's numbers) and smooths it handle by handle.

**F.** The proof follows MT through numbered milestones (M01-M90, with gaps).
- topologicalPoincareSkeleton (PoincareLib/Topology/Manifold/Poincare.lean:30) projects the final package
  m90FinalAssemblyFromMilestones (PoincareLib/Topology/Manifold/Poincare/Final/Main.lean:32), which combines the
  smoothing m76CompatibleSmoothing (PoincareLib/Topology/Manifold/Smoothing/Compatible.lean:40; A. J. S. Hamilton
  1976 and Cairns 1940 in place of Moise) with the smooth theorem (m79TopologicalPoincare,
  PoincareLib/Topology/Manifold/Poincare/Topological.lean:29).
- smoothPoincareSkeleton (Poincare.lean:23) is m75SmoothPoincare
  (PoincareLib/Topology/Manifold/Poincare/Smooth.lean:30) applied to m90SmoothEndpointInputs
  (PoincareLib/Topology/Manifold/Poincare/Final/Providers.lean:73): the global flow with surgery
  (repairedGlobalFlow, PoincareLib/Geometry/RicciFlow/Surgery/Global/Existence.lean:51; MT Theorem 15.9 and
  Corollary 15.10), finite extinction (m71GlobalFiniteExtinction,
  PoincareLib/Geometry/RicciFlow/Extinction/Global/Main.lean:35; MT Theorem 18.1 with Chapter 19 and the 2015
  correction), the reconstruction (m72FiniteReconstruction,
  PoincareLib/Topology/Manifold/Surgery/Reconstruction/Main.lean:30), the sphere factors (m73SphereFactors,
  PoincareLib/Topology/Manifold/Surgery/SphereFactors/Main.lean:31) and the connected-sum reduction
  (m74ConnectedSumReduction, PoincareLib/Topology/Manifold/Surgery/Reduction/Main.lean:28), which uses a smooth
  Schoenflies theorem and Smale's theorem.

### 3.5 Route differences, HOL against the sources

- **Surgery histories.** The HOL Ricci flow with surgery is the finite history of Section 3.3, in place of MT's
  space-time of Chapter 14; Q uses the same kind of encoding. The surgery parameters may depend on the initial
  manifold (RFS_EXTINCTION_STATEMENT), as in Q; MT's Theorem 15.9 fixes universal parameter sequences, and only the
  weaker form is needed. Parts 3 and 4 are carried out for simply connected initial manifolds only, as in both Lean
  formalizations.
- **Finite extinction.** HOL replaces MT Chapters 18-19 (widths of loop families, curve shrinking, minimal annuli,
  Section 19.2 with its correction) by the width of sweepouts by 2-spheres of T. H. Colding and W. P. Minicozzi,
  "Width and finite extinction time of Ricci flow" (Geom. Topol. 12 (2008); arXiv:0707.0108), whose Theorem 1.7
  (p. 4) bounds the derivative of the width W by -4 pi + 3W/(4(t+C)). The top layer (ancestor components across
  surgeries, the pinch maps of Proposition 15.12, the comparison argument) follows MT Chapter 18. Both Lean
  formalizations follow MT Chapters 18-19.
- **The endgame without connected sums.** MT (Corollary 15.4) and both Lean formalizations reconstruct the initial
  manifold as a connected sum and use van Kampen. HOL propagates simple connectivity forward instead, as in MT
  Remark 0.6(ii): cutting and capping keeps components simply connected (RFS_CUTCAP_SC, by general position and
  pinch maps, using that every neck sphere separates, SMT_SC_SPHERE_SEP); a simply connected discarded piece is
  S^3 (RFS_LISTED_SC_S3: Killing-Hopf for space forms, KILLING_HOPF_COMPONENT; S^2-bundles over S^1 and pieces
  containing RP^3 minus a point are not simply connected); and a backward induction over the necks shows that a
  leaf side of a neck is a ball (RFS_SPHERE_SYSTEM, src/pc_smt_system.ml).
- **Smale and the disc theorem**, cited by MT, are proved: every diffeomorphism of S^2 is smoothly isotopic to an
  orthogonal map (src/pc_smt_sphere.ml, through a normalization at a pole and isotopies of compactly supported
  planar diffeomorphisms), hence extends radially to R^3 (SMT_SMALE_RADIAL, src/pc_smt_straight.ml); two ball
  charts of a connected manifold agree after a compactly supported diffeomorphism and an orthogonal map
  (SMT_DISC, src/pc_smt_disc.ml).
- **The Appendix** is formalized for the separating case, which the simply connected route needs. MT's
  Proposition A.25 (stated without proof, p. 514) is APX_A25 (src/pc_apx_a25top.ml), proved from the smooth
  Schoenflies theorem in R^3 (SCH_SCHOENFLIES_REQ, src/pc_sch_main.ml) by the Morse-theoretic proof of Alexander's
  theorem in Hatcher's notes.
- **Short-time existence and uniqueness** (MT Theorem 3.11, cited there) are proved: the Ricci-DeTurck flow is
  solved by linear theory on tori with chart-wise Sobolev energies (`src/pc_pde_*.ml`) and turned into a Ricci flow
  by the DeTurck gauge (src/pc_pde_gauge.ml); uniqueness is Kotschwar's energy method (src/pc_rf_unique.ml).
- **The standard solution** (MT Theorem 12.5): uniqueness comes from that of complete Ricci flows of bounded
  curvature, by Kotschwar's weighted energy (src/pc_rf_unique_complete.ml), and the SO(3)-invariance from the
  uniqueness (src/pc_p2c_stdsym.ml). MT prove the symmetry first (Section 12.5, p. 300) and the uniqueness through
  the harmonic map flow and the Ricci-DeTurck flow (Sections 12.6-12.8, pp. 306-325). F also uses an energy method.
- **Part 2.** Proposition 2.19, in a form with separating neck spheres, by Toponogov's theorem and Gromov's
  critical point lemma (src/pc_p2a_219.ml); Theorem 8.1 through the set of initial vectors of minimizing
  L-geodesics, without the injectivity domain (src/pc_p2a_t81.ml); Theorem 9.59 and Lemma 9.65 by Tao's arguments
  (src/pc_p2a_asv.ml, src/pc_p2a_l965.ml); the cone step of Theorem 10.2 on the smooth limit, with MT Proposition
  4.22, in place of Gromov-Hausdorff cones (`src/pc_p2b_cone*.ml`); Chapter 11 for generalized flows ("views").
- **Part 3.** The small-scale part of Proposition 16.1 follows Kleiner-Lott's Sublemma 79.23 (P3N_SMALL_SCALE,
  src/pc_p3_s16small.ml); Claim 17.3 is proved with a margin that the printed argument lacks (P3H_CLAIM_17_3_CORE,
  src/pc_p3_c172d.ml; Section 5.2). Metric existence, which MT take for granted, uses an embedding into R^(2N+1).
- **Moise.** The PL part follows Moise, with Q's chain of statements as a map. The smoothing of a combinatorial
  3-manifold is a direct construction (`src/pc_moi_smo_*.ml`, `src/pc_moi_pd2_*.ml`): each tetrahedron gets the
  metric of a regular Euclidean tetrahedron, edges are smoothed by an angular rescaling of the tetrahedra around
  them, vertices by cones over their links, with a 2-dimensional smoothing theorem for the links. Q smooths the
  triangulation handle by handle; F uses A. J. S. Hamilton's and Cairns's theorems instead of Moise.
- Many intermediate results are proved in stronger forms than needed, for instance in every dimension N or at
  every carrier type.

## 4. Per-result overview

The full table is doc/results.tsv. It has one row for each numbered result of MT and of Moise that the
development formalizes or replaces, with its source location, the Lean declarations of Q and F where there are
counterparts, the HOL theorems and files, and a status saying how the HOL theorem relates to the printed
statement. It has 124 rows: the 4 headline theorems; 28 results of MT Part 1 (Chapters 1-4), 47 of Part 2
(Chapters 5-12), 19 of Part 3 (Chapters 13-17), 3 of Part 4 (Chapters 18-19) and 6 of the Appendix; 16 of Moise;
and the smoothing of topological 3-manifolds (MT p. ix, footnote 1). By status, 29 are proved as stated, 92 in
another form and 3 are replaced by another route.

In most rows the HOL theorem is the printed statement in HOL form. Where it differs, it is stated for simply
connected initial manifolds and for the finite histories of Section 3.3; it states hypotheses that the source
leaves implicit (domains, parameter ranges, uniformity); it is a corrected form of a printed statement that is
false or incomplete as written (doc/SOURCE_NOTES.md); or the result is replaced by another route (Section 3.5),
as Chapter 19 and most of Chapter 18 are replaced by Colding-Minicozzi's width.

## 5. The sources

### 5.1 Which source for which part

| part of the development | source followed | further sources |
|---|---|---|
| statements | MT Introduction, pp. ix-x; Milnor pp. 1 and 5 | Mathlib's statements, through Q and F |
| manifolds, embeddings, metrics, orientations, flows of vector fields | J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed. (GTM 218): Theorem 6.15 (Whitney embedding, p. 134), Chapter 9, Chapter 13, Theorem 15.41 (orientation covering, p. 395) | A. Hatcher, *Algebraic Topology*, Section 3.3 (orientable double cover) |
| Riemannian and comparison geometry (MT Chapters 1-2) | MT Chapters 1-2 | P. Petersen, *Riemannian Geometry*, 3rd ed. (GTM 171): Sections 6.4, 7.1, 12.1, 12.2 and 12.4 |
| Ricci flow, maximum principles, Shi's estimates, pinching, Harnack (MT Chapters 3-4) | MT Chapters 3-4 | B. Chow, P. Lu, L. Ni, *Hamilton's Ricci Flow* (GSM 77): Chapters 2, 3, 6 and 10; P. Topping, *Lectures on the Ricci Flow* |
| short-time existence, uniqueness | DeTurck's method (Chow-Lu-Ni, Chapter 2); B. Kotschwar, "An energy approach to the problem of uniqueness for the Ricci flow" (Comm. Anal. Geom. 22 (2014); arXiv:1206.3225), Sections 1-2 | |
| Perelman's length function, kappa-solutions, limits, the standard solution (MT Chapters 5-12) | MT Part 2 | T. Tao, *Poincare's Legacies* (Chapter 3, Section 3.18: Proposition 3.18.3, p. 587; Corollary 3.18.6, p. 588; Proposition 3.18.7, p. 589) for Theorem 9.59 and Lemma 9.65; Kleiner-Lott |
| Ricci flow with surgery (MT Chapters 13-17) | MT Part 3 | B. Kleiner and J. Lott, "Notes on Perelman's papers" (arXiv:math/0605667), Sublemma 79.23 |
| the topology of a surgery event, Appendix | MT Proposition 15.3 and Appendix | A. Hatcher, *Notes on Basic 3-Manifold Topology*: Theorem 1.1 (Alexander's theorem, p. 1, proof pp. 2-3) for smooth Schoenflies |
| smooth topology of the endgame | MT Remark 0.6(ii) and Corollary 15.4(2) | J. Milnor, *Morse Theory* (product structures from functions without critical points); Milnor's homogeneity lemma and Palais's disc theorem |
| finite extinction | Colding-Minicozzi 2008 (arXiv:0707.0108): Proposition 1.5 and Theorem 1.7 (p. 4), Theorem 1.14 (p. 6), Lemma 1.22 (p. 7), Theorem 2.1 (p. 8), Proposition 2.2 (p. 9), Appendices A-D; MT Chapter 18 for the top layer | J. Sacks and K. Uhlenbeck (Ann. of Math. 113 (1981)); R. Schoen and K. Uhlenbeck (J. Differential Geom. 17 (1982)); L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, Chapter V (for Colding-Minicozzi's Lemma D.7); L. C. Evans, *Partial Differential Equations*, 2nd ed., Chapter 5; A. Hatcher, *Algebraic Topology*, Section 3.3 (local homology) |
| Moise | Moise, Section 17 and Sections 22-35 | Q's chain of statements as a map; the smoothing is a direct construction |

The smooth calculus (continuously_differentiable, smooth_map_on, the smooth inverse function theorem, cutoff
functions) is taken from the Navier-Stokes HOL Light development: src/ns_smooth.ml, src/ns_smooth_elem.ml,
src/ns_cutoff.ml, src/ns_statement.ml and src/ns_spacetime.ml are copies of its files, with the code unchanged
except for the paths in the `needs` lines.

### 5.2 Errors and gaps in the sources

doc/SOURCE_NOTES.md lists the errors, gaps, imprecisions and typos found in the sources, with how the
formalization handles each. A few examples that shape the HOL proof:
- **MT Proposition A.25** (p. 514) is stated without proof; the book ends there. HOL proves it in the separating
  case from the smooth Schoenflies theorem (APX_A25).
- **MT Claim 17.3** (p. 399): the pulled-back metric is only "within a factor of 2" of the standard solution, so
  the scalar curvature along the flow line limits to at least 4D, not "at least 8D" as printed, which does not
  contradict the bound 6D. The HOL form chooses theta_1 for a larger constant, which Proposition 12.31 allows
  (P3H_CLAIM_17_3_CORE).
- **MT Lemma 17.12** (p. 410): a surgery removes volume of order delta^-1 h^3 (half of a delta-neck of scale h),
  printed as delta^-1 h^2; the argument is unaffected.
- **MT Proposition 12.25** (p. 320) states a decay |nabla^i rho~| <= C_14/(1 + |x|)^2 that the uniqueness proof of
  the standard solution uses; since dr/dt tends to a constant at infinity (Claim 12.23(4), p. 315), the correction
  term decays in general only like 1/|x|. HOL proves the uniqueness by another route (Section 3.5).
- **MT Definition 1.7** (p. 7) leaves the normalization of the eigenvalues of the curvature operator open (a
  factor depending on the convention for 2-forms). Theorem 4.26 (p. 76) and Definition 4.34 (p. 80) hold when the
  eigenvalues are the sectional curvatures of the eigenplanes; the HOL definitions use that normalization
  (src/pc_rfs_geom.ml).
- **MT Section 19.2** was corrected by Morgan and Tian (arXiv:1512.00699). The HOL route does not use Chapter 19.

## 6. Trust and checking

### 6.1 The trust base

- HOL Light's kernel and its three standard axioms, ETA_AX, SELECT_AX and INFINITY_AX (HOL Light commit e5236a58
  of 2026-11-10, OCaml 4.14.1 with camlp5 8.02.01; the checks of Section 6.2 were also run with the earlier commits
  2828953e and 924faf0c, and the HOLTrace re-check of Section 6.3 with 2828953e, the parent of e5236a58).
- The statement files of Section 2.1, read by a human, and the library definitions they use.

The tactics, the libraries built here and all other files do not have to be trusted, since every theorem passes
through the kernel. For the four headline theorems the HOLTrace replay of Section 6.3 also takes the development's
own OCaml code out of the trust base: they are rebuilt from the traces' primitive inferences by HOL Light's kernel,
in a session that loads only the library and the statement files, together with HOLTrace's restore code, which
builds theorems only through the kernel.

### 6.2 Checking the proofs

check.ml loads the development into a fresh HOL Light session. For each of POINCARE_TOP, POINCARE_SMOOTH and
POINCARE_EMBEDDED it prints the theorem, its number of hypotheses and whether its conclusion is the statement
constant applied to `UNIV` at a type variable; for MOI_SST_HEADLINE, whether its conclusion is
`!u:A->bool. MOISE_SMOOTHING_STATEMENT u` with A a type variable; then it prints the list of axioms. Every
hypothesis count is 0, every conclusion has the required form, and the axioms are exactly ETA_AX, SELECT_AX and
INFINITY_AX. In HOL Light, admitting a goal without proof goes through the creation of a new axiom, so the
printed list is itself a check that nothing was assumed. A scan of every file of src/ and audit/ for
unproved-theorem constructs, a second and syntactic check, found none. Each headline theorem was also loaded with
its own load closure in fresh sessions, with the same results. audit/check.ml prints the two equivalences of
Section 2.4, BLIND_POINCARE_TOP_PROVED, BLIND_POINCARE_SMOOTH_PROVED and the 30 sanity theorems, each with 0
hypotheses, and the same three axioms.

### 6.3 HOLTrace

HOLTrace 20250714 (D. J. Bernstein, holtrace.cr.yp.to) records every primitive inference of a HOL Light session in
a trace; its C checker, holtrace-verify, checks a trace independently of HOL Light, and HOL Light can restore a
trace through its own kernel. The re-check used HOL Light commit 2828953e, the parent of e5236a58 (which only adds
coinductive definitions, not used here). holtrace/README.md describes it in full; in short:

- *What was traced.* A trace of the whole development in one session would be about 16 GB and would need about
  300 GiB of memory to record, so the development was traced in 11 parts. Part 0 is HOL Light's core with the base
  library (Multivariate up to cauchy.ml, lpspaces.ml and 100/green.ml), proved in full; parts 1 to 10 are
  consecutive pieces of the load order of make.ml (337, 203, 121, 113, 87, 39, 65, 47, 55 and 23 files). The trace
  of part k proves the files of part k in full; the base library and the earlier files come before them in stub
  mode, in which each theorem is introduced as an axiom of its statement. Only statements that a full load of the
  same files proved are stubbed (recorded beforehand); the others are proved in full. Every theorem proved at the
  top level is named HTLINK_k in its trace, and the headline theorems by their names.
- *The traces.* 20.09 GB and 666,601,455 inferences in all, from 39.9 to 86.7 million per part, with 194,000 to
  349,000 types and 80 to 163 million terms per part, and 25 type definitions in part 0 and 29 in each of the
  others; 16.0 GB of it is the proofs of part 0 and of the files of each part, the rest the stub-mode loads of the
  earlier files. holtrace-verify accepted all eleven traces, in 25 to 48 s and with 9 to 17 GiB each.
- *The replay.* One fresh session of a copy of HOL Light with HOLTrace's plain install (the kernel files unchanged)
  and a 9-line patch to its restore function that lets it match a stub axiom with the theorem of the same
  statement, up to the names of bound variables, restored from an earlier part. The session loaded the base
  library and src/poincare_statement.ml and src/pc_interfaces.ml, then restored the eleven traces in order, with
  new axioms disallowed; it was checkpointed once with DMTCP and restored after a reboot of the machine. It matched
  34,873 constant definitions with the session's (among them POINCARE_STATEMENT, POINCARE_SMOOTH_STATEMENT,
  POINCARE_EMBEDDED_STATEMENT and MOISE_SMOOTHING_STATEMENT, in each of parts 1 to 10, with the definitions of the
  statement files) and created 3,810; it matched 311 type definitions and created 4; it linked 485,894 stub axioms;
  it created no axiom. At the end POINCARE_TOP, POINCARE_SMOOTH and POINCARE_EMBEDDED had no hypotheses and
  conclusions POINCARE_STATEMENT, POINCARE_SMOOTH_STATEMENT and POINCARE_EMBEDDED_STATEMENT applied to `UNIV` at
  a type variable, MOI_SST_HEADLINE had no hypotheses and conclusion `!u. MOISE_SMOOTHING_STATEMENT u`, and the
  session's axioms were ETA_AX, SELECT_AX and INFINITY_AX. It took about 16 h of CPU, with a peak of 46 GiB up to
  the checkpoint.

### 6.4 The Lean side

Nothing was built or run from the Lean repositories; the following comes from reading them at the pinned commits
and from their authors' reports. Both use Lean v4.33.1 and Mathlib v4.33.1 (rev 0df444a3); their trust base is
Lean's kernel, the Mathlib definitions in the statements and the axioms propext, Quot.sound and Classical.choice.
- Q: a keyword scan finds no axiom declaration and no `sorry` outside comments. The authors report
  `#print axioms` with only those three axioms for poincare_conjecture, exists_isManifold_three,
  smoothPoincareConjecture_holds and exists_poincare_controlled_extinction; an adaptation of a later commit was
  accepted by the LeanEval pipeline (comparator, nanoda and the Lean kernel) for both problems.
- F: Comparator/config.json permits only the three axioms and enables nanoda; the only `sorry` tokens in code are
  the two of the challenge file. The authors report a comparator run with both kernels on an earlier commit
  (1876d7dc) of their blueprint repository, whose Lean library differs from the pinned one only in comments.

## 7. Sizes and timings

**HOL, by part.** The development consists of the 1,090 files of src/, all loaded by make.ml. Theorems are counted
as `let NAME = prove` bindings with an upper-case NAME; lines are raw lines, comments and blank lines included.
doc/LAYOUT.md gives the file families in detail and doc/timing.tsv the load time of each file.

| part (file prefixes) | files | lines | theorems | load time (s) |
|---|---|---|---|---|
| statements, sanity theorems, top files | 5 | 927 | 37 | 2 |
| smooth calculus from the Navier-Stokes development (`ns_*`) | 5 | 3,583 | 179 | 11 |
| manifolds, Riemannian and comparison geometry (`pc_mfd_*`, `pc_lrg*`, `pc_grg_*`, `pc_geo_*`, `pc_cmp_*`, `pc_lck_*`) | 106 | 108,967 | 2,435 | 608 |
| ODE flows (`pc_ode_*`) | 7 | 8,396 | 170 | 21 |
| general and algebraic topology (`pc_top_*`) | 12 | 14,229 | 433 | 164 |
| Ricci flow foundations, MT Chapters 3-4, PDE (`pc_rf_*`, `pc_rfa_*`, `pc_pde_*`, pc_vshi, pc_pv411) | 106 | 154,921 | 3,641 | 1,288 |
| MT Part 2, Chapters 5-12 (`pc_p2a_*`, `pc_p2b_*`, `pc_p2c_*`, `pc_lim_*`, `pc_canon_*`, `pc_s2ent_*`, `pc_soul_*`, `pc_z2x_*`) | 320 | 403,406 | 7,381 | 3,592 |
| weak analysis (`pc_wan_*`) | 29 | 48,618 | 1,218 | 556 |
| MT Part 3, Chapters 13-17, and the surgery histories (`pc_p3_*`, `pc_p3e_*`, `pc_rfs_*`) | 86 | 99,254 | 1,822 | 1,488 |
| MT Proposition 15.3, Appendix, smooth Schoenflies (`pc_apx_*`, `pc_sch_*`) | 52 | 115,056 | 2,125 | 1,846 |
| smooth topology of the endgame (`pc_smt_*`) | 22 | 21,468 | 463 | 115 |
| finite extinction: Colding-Minicozzi, harmonic maps (`pc_p4_*`, `pc_cm_*`, `pc_cmc_*`, `pc_cmr_*`, `pc_cmw_*`, `pc_hm_*`, `pc_an_*`) | 65 | 116,802 | 2,922 | 1,270 |
| Moise: triangulation and smoothing (`pc_moi_*`) | 275 | 603,594 | 12,452 | 12,451 |
| **total** | **1,090** | **1,699,221** | **35,278** | **23,412** |

**Per headline theorem** (the load closure of its file, through `needs`):

| file | headline | files | lines | theorems |
|---|---|---|---|---|
| src/pc_smt_smooth.ml | POINCARE_SMOOTH | 819 | 1,102,231 | 22,987 |
| src/pc_moi_status.ml | MOI_SST_HEADLINE | 289 | 616,939 | 12,976 |
| src/pc_poincare_top.ml | POINCARE_TOP, POINCARE_EMBEDDED | 1,090 | 1,699,221 | 35,278 |

**Fresh session, end to end** (doc/timing.tsv; HOL Light e5236a58; CPU time of the standard bytecode toplevel on
one core, measured on a shared machine with several such sessions running at once): the HOL Light core 1.1 min,
the library prerequisites 27.0 min, the development 390.2 min (6.5 h), in all 418.3 min (7.0 h); peak memory about
17.5 GiB with the garbage-collector setting at the top of make.ml (space_overhead 40; a load without it took
416.2 min and 23.3 GiB). The slowest files are src/pc_moi_s35_minc.ml (541 s), src/pc_moi_lt_seam.ml (453 s),
src/pc_moi_pd2_glob.ml (304 s), src/pc_moi_fnd_tubep.ml (284 s) and src/pc_moi_lt_gpb2.ml (269 s); the Moise files
take 12,451 s, about half of the development. HOLTrace (holtrace/README.md, with HOL Light 2828953e): the record,
the spine and the eleven traces took 9.1 h of wall-clock time running side by side (the record 7.6 h and 23 GiB,
each trace of a part up to 59 GiB); the C checker 25 to 48 s and 9 to 17 GiB per part; the replay about 16 h of
CPU (46 GiB up to the checkpoint).

**The audit files**: audit/poincare_blind.ml 249 lines (20 definitions); audit/pc_audit_equiv.ml about 1,250 lines
(44 theorems); audit/pc_audit_blind_proved.ml 19 lines (2 theorems). **The sources**: MT has xlii + 521 pages
(Introduction pp. ix-xlii, Parts 1-4 pp. 1-496, Appendix pp. 497-514); the parts of Moise used are Section 17
(from p. 117) and Sections 22-35 (pp. 155-252); Colding-Minicozzi's paper has 34 pages (arXiv version).

**Lean** (counted on the pinned commits; nothing was built):

| | files | lines |
|---|---|---|
| Q, whole release | 17,556 | 4,722,013 |
| Q, import cone of poincare_conjecture | 14,197 | about 4.02 million |
| F, whole repository | 23,560 | 3,061,775 (2,788,501 without comment-only lines) |

A declaration-level estimate puts Q's dependency cone of poincare_conjecture at about 2.24 million lines, of which
about 0.45 million are the Moise part; F's smoothing (milestone M76, PoincareLib/Topology/Manifold/Smoothing) has
615,197 non-blank lines without comments. The HOL development has about 1.70 million lines in all: about 1.10
million in the load closure of the smooth form and about 0.60 million in the Moise files.

## 8. How to reproduce

The README explains how to load the development and the audit files and how to run the check of Section 6.2. In
short, with a built HOL Light (tested with commit e5236a58 and OCaml 4.14.1), started in the root directory of
this repository:

```
loadt "make.ml";;          (* load the development *)
loadt "check.ml";;         (* load it and print the headline theorems, their hypotheses and the axioms *)
loadt "audit/check.ml";;   (* load it with the statement audit and print the audit results *)
```

or, non-interactively, `echo 'loadt "check.ml";;' | LINE_EDITOR=env /path/to/hol-light/hol.sh`. make.ml loads
HOL Light's Multivariate/cauchy.ml, Multivariate/lpspaces.ml and 100/green.ml and then the files of src/ in
dependency order; the files load the further library files they need (Multivariate/homology.ml,
Multivariate/cross.ml, 100/circle.ml, 100/isoperimetric.ml, 100/polyhedron.ml) with `needs`. holtrace/README.md
explains the HOLTrace re-check: from the repository root, `holtrace/run_holtrace.sh HOL_LIGHT_DIR WORK_DIR` downloads
HOLTrace, traces the parts, checks each trace with the C checker and replays them all; it prints a PART_DONE line
and a `verified ...` line for each part, then from the replay a RESTORED line for each part, RESTORED_CHECK lines
with hyps=0 and true for the four headline theorems, and AXIOM lines for exactly the three standard axioms.
