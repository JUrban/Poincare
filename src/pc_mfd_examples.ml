(* ========================================================================= *)
(* pc_mfd_examples: standard smooth structures.  Open subsets of real^N with *)
(* the identity chart; the spheres S^3 in real^4 and S^2 in real^3 with      *)
(* their stereographic atlases (two charts each, from the north and the     *)
(* south pole); the inclusion of each sphere is a smooth immersion; the     *)
(* 3-sphere satisfies the hypotheses of POINCARE_SMOOTH_STATEMENT and its   *)
(* conclusion holds for it with the inclusion map.                          *)
(*                                                                           *)
(* First: the definitions, the explicit inverse stereographic maps, and      *)
(* generic lemmas about charts with a smooth inverse defined on the whole of *)
(* real^N (homeomorphism, transition maps, atlas, immersion).                *)
(* ========================================================================= *)

needs "src/pc_mfd_base.ml";;
needs "src/poincare_statement_sanity.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Stereographic projections and the standard atlases.                       *)
(* ------------------------------------------------------------------------- *)

let stereo3_n = new_definition
 `stereo3_n (x:real^4) = (lambda i. x$i / (&1 - x$4)):real^3`;;

let stereo3_s = new_definition
 `stereo3_s (x:real^4) = (lambda i. x$i / (&1 + x$4)):real^3`;;

let sphere3_atlas = new_definition
 `sphere3_atlas =
    {(sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n),
     (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s)}`;;

let stereo2_n = new_definition
 `stereo2_n (x:real^3) = (lambda i. x$i / (&1 - x$3)):real^2`;;

let stereo2_s = new_definition
 `stereo2_s (x:real^3) = (lambda i. x$i / (&1 + x$3)):real^2`;;

let sphere2_atlas = new_definition
 `sphere2_atlas =
    {(sphere(vec 0:real^3,&1) DELETE basis 3,stereo2_n),
     (sphere(vec 0:real^3,&1) DELETE --(basis 3),stereo2_s)}`;;

(* Open subsets of real^N with the identity chart. *)

let open_set_atlas = new_definition
 `open_set_atlas (U:real^N->bool) = {(U,(\x:real^N. x))}`;;

(* ------------------------------------------------------------------------- *)
(* The inverse stereographic maps (defined on the whole of real^3, real^2).  *)
(* ------------------------------------------------------------------------- *)

let stereo3_n_inv = new_definition
 `stereo3_n_inv (y:real^3) =
    (lambda i. if i = 4 then (norm y pow 2 - &1) / (norm y pow 2 + &1)
               else &2 * y$i / (norm y pow 2 + &1)):real^4`;;

let stereo3_s_inv = new_definition
 `stereo3_s_inv (y:real^3) =
    (lambda i. if i = 4 then (&1 - norm y pow 2) / (norm y pow 2 + &1)
               else &2 * y$i / (norm y pow 2 + &1)):real^4`;;

let stereo2_n_inv = new_definition
 `stereo2_n_inv (y:real^2) =
    (lambda i. if i = 3 then (norm y pow 2 - &1) / (norm y pow 2 + &1)
               else &2 * y$i / (norm y pow 2 + &1)):real^3`;;

let stereo2_s_inv = new_definition
 `stereo2_s_inv (y:real^2) =
    (lambda i. if i = 3 then (&1 - norm y pow 2) / (norm y pow 2 + &1)
               else &2 * y$i / (norm y pow 2 + &1)):real^3`;;

(* ------------------------------------------------------------------------- *)
(* A smooth map phi on an open set W with a smooth left inverse psi defined  *)
(* on the whole of real^N, mapping into W, has an injective derivative at    *)
(* every point (chain rule on phi o psi = id).                               *)
(* ------------------------------------------------------------------------- *)

let STEX_LEFT_INVERSE_DERIVATIVE_INJ = prove
 (`!W (phi:real^M->real^N) (psi:real^N->real^M) y h.
        open W /\ smooth_map_on W phi /\ smooth_map_on (:real^N) psi /\
        (!z. psi z IN W /\ phi(psi z) = z) /\
        frechet_derivative psi (at y) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((psi:real^N->real^M) has_derivative frechet_derivative psi (at y)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `psi:real^N->real^M`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(phi:real^M->real^N) differentiable (at ((psi:real^N->real^M) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (phi:real^M->real^N) (at ((psi:real^N->real^M) y)) o
    frechet_derivative psi (at y) = (\h:real^N. h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC
     [`(phi:real^M->real^N) o (psi:real^N->real^M)`; `y:real^N`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      SUBGOAL_THEN `(phi:real^M->real^N) o (psi:real^N->real^M) = (\z. z)`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[HAS_DERIVATIVE_ID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (phi:real^M->real^N)
                              (at ((psi:real^N->real^M) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `h:real^N` o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `frechet_derivative (phi:real^M->real^N)
                  (at ((psi:real^N->real^M) y))` LINEAR_0) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Charts with a smooth inverse defined on the whole of real^N: the image is *)
(* the whole of real^N and the chart is a homeomorphism onto it.             *)
(* ------------------------------------------------------------------------- *)

let STEX_GLOBAL_INVERSE_HOMEOMORPHISM = prove
 (`!U W (phi:real^M->real^N) (psi:real^N->real^M).
        open W /\ U SUBSET W /\ smooth_map_on W phi /\
        smooth_map_on (:real^N) psi /\
        (!x. x IN U ==> psi(phi x) = x) /\ (!y. psi y IN U /\ phi(psi y) = y)
        ==> IMAGE phi U = (:real^N) /\ homeomorphism (U,(:real^N)) (phi,psi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (phi:real^M->real^N) U = (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^N->real^M) (:real^N) = U` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^M->real^N) continuous_on U` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^N->real^M) continuous_on (:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV]);;

let STEX_GLOBAL_INVERSE_CHART = prove
 (`!S U W (phi:real^M->real^N) (psi:real^N->real^M).
        open_in (subtopology euclidean S) U /\
        open W /\ U SUBSET W /\ smooth_map_on W phi /\
        smooth_map_on (:real^N) psi /\
        (!x. x IN U ==> psi(phi x) = x) /\ (!y. psi y IN U /\ phi(psi y) = y)
        ==> open_in (subtopology euclidean S) U /\ open (IMAGE phi U) /\
            homeomorphic_map (subtopology (subtopology euclidean S) U,
                              subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `W:real^M->bool`; `phi:real^M->real^N`;
                 `psi:real^N->real^M`] STEX_GLOBAL_INVERSE_HOMEOMORPHISM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(S:real^M->bool) INTER U = U` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN EXISTS_TAC `psi:real^N->real^M` THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY]);;

(* The transition from such a chart (U,phi) to any chart (V,phi') that is    *)
(* smooth on an open W containing V is phi' o psi, smooth on phi(U INTER V). *)

let STEX_GLOBAL_INVERSE_TRANSITION = prove
 (`!U V W (phi:real^M->real^N) (phi':real^M->real^N) (psi:real^N->real^M).
        open W /\ V SUBSET W /\ smooth_map_on W phi' /\
        smooth_map_on (:real^N) psi /\ (!x. x IN U ==> psi(phi x) = x)
        ==> smooth_map_on (IMAGE phi (U INTER V)) (phi' o psi) /\
            !x. x IN U INTER V ==> (phi' o psi) (phi x) = phi' x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[IN_INTER; o_THM] THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `{y:real^N | (psi:real^N->real^M) y IN W}` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `W:real^M->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* An atlas of such charts on a subset S of real^M is a smooth atlas of the  *)
(* subspace topology.                                                        *)

let STEX_GLOBAL_INVERSE_ATLAS = prove
 (`!S (atlas:((real^M->bool)#(real^M->real^N))->bool).
        (!U phi. (U,phi) IN atlas
                 ==> open_in (subtopology euclidean S) U /\
                     ?W psi. open W /\ U SUBSET W /\ smooth_map_on W phi /\
                             smooth_map_on (:real^N) psi /\
                             (!x. x IN U ==> psi(phi x) = x) /\
                             (!y. psi y IN U /\ phi(psi y) = y)) /\
        (!x. x IN S ==> ?U phi. (U,phi) IN atlas /\ x IN U)
        ==> smooth_manifold_atlas (subtopology euclidean S) atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "charts") ASSUME_TAC) THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^M->bool`; `phi:real^M->real^N`] THEN
    DISCH_TAC THEN
    USE_THEN "charts" (MP_TAC o SPECL [`U:real^M->bool`; `phi:real^M->real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`W:real^M->bool`; `psi:real^N->real^M`] THEN
    STRIP_TAC THEN MATCH_MP_TAC STEX_GLOBAL_INVERSE_CHART THEN
    MAP_EVERY EXISTS_TAC [`W:real^M->bool`; `psi:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:real^M->bool`; `phi:real^M->real^N`;
                         `V:real^M->bool`; `phi':real^M->real^N`] THEN
    STRIP_TAC THEN
    USE_THEN "charts" (MP_TAC o SPECL [`U:real^M->bool`; `phi:real^M->real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W1:real^M->bool`
     (X_CHOOSE_THEN `psi1:real^N->real^M` STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    USE_THEN "charts" (MP_TAC o SPECL [`V:real^M->bool`; `phi':real^M->real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W2:real^M->bool`
     (X_CHOOSE_THEN `psi2:real^N->real^M` STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    EXISTS_TAC `(phi':real^M->real^N) o (psi1:real^N->real^M)` THEN
    MATCH_MP_TAC STEX_GLOBAL_INVERSE_TRANSITION THEN
    EXISTS_TAC `W2:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

(* The inclusion of S is a smooth immersion for an atlas of such charts. *)

let STEX_GLOBAL_INVERSE_IMMERSION = prove
 (`!(atlas:((real^M->bool)#(real^M->real^N))->bool).
        (!U phi. (U,phi) IN atlas
                 ==> ?W psi. open W /\ U SUBSET W /\ smooth_map_on W phi /\
                             smooth_map_on (:real^N) psi /\
                             (!x. x IN U ==> psi(phi x) = x) /\
                             (!y. psi y IN U /\ phi(psi y) = y))
        ==> smooth_immersion_into atlas (\x:real^M. x)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "charts") THEN
  REWRITE_TAC[smooth_immersion_into] THEN
  MAP_EVERY X_GEN_TAC [`U:real^M->bool`; `phi:real^M->real^N`] THEN
  DISCH_TAC THEN
  USE_THEN "charts" (MP_TAC o SPECL [`U:real^M->bool`; `phi:real^M->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:real^M->bool`; `psi:real^N->real^M`] THEN
  STRIP_TAC THEN EXISTS_TAC `psi:real^N->real^M` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^N`; `h:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC STEX_LEFT_INVERSE_DERIVATIVE_INJ THEN
    MAP_EVERY EXISTS_TAC [`W:real^M->bool`; `phi:real^M->real^N`;
                          `psi:real^N->real^M`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Points of the unit sphere with k-th coordinate 1 or -1 are the poles.     *)
(* ------------------------------------------------------------------------- *)

let STEX_SPHERE_COMPONENT_POLE = prove
 (`!x:real^N k.
        1 <= k /\ k <= dimindex(:N) /\ norm x = &1
        ==> (x$k = &1 <=> x = basis k) /\ (x$k = -- &1 <=> x = --(basis k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) dot x = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_1]; ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_NEG_COMPONENT] THENL
   [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
    ASM_SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_BASIS; BASIS_COMPONENT;
                 VECTOR_SUB_COMPONENT] THEN
    REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --y <=> x + y = vec 0`] THEN
    REWRITE_TAC[GSYM DOT_EQ_0] THEN
    ASM_SIMP_TAC[DOT_LADD; DOT_RADD; DOT_BASIS; BASIS_COMPONENT;
                 VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the components of the inverse stereographic maps.           *)
(* ------------------------------------------------------------------------- *)

let STEX_INV_STEREO_DENOM = prove
 (`!y:real^N. &0 < norm y pow 2 + &1`,
  GEN_TAC THEN MP_TAC(SPEC `norm(y:real^N)` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let STEX_SMOOTH_NORM2_PLUS1 = prove
 (`!s. open s
       ==> smooth_map_on s (\y:real^N. lift(norm y pow 2 + &1)) /\
           smooth_map_on s (\y:real^N. lift(norm y pow 2 - &1)) /\
           smooth_map_on s (\y:real^N. lift(&1 - norm y pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\y:real^N. lift(norm y pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. y`]
      SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(norm y pow 2)`;
                   `\y:real^N. lift(&1)`] SMOOTH_MAP_ON_LIFT_ADD);
    MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(norm y pow 2)`;
                   `\y:real^N. lift(&1)`] SMOOTH_MAP_ON_LIFT_SUB);
    MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(&1)`;
                   `\y:real^N. lift(norm y pow 2)`] SMOOTH_MAP_ON_LIFT_SUB)] THEN
  ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST]);;

let STEX_SMOOTH_INV_STEREO_COORD = prove
 (`!k. smooth_map_on (:real^N)
         (\y:real^N. lift(&2 * y$k / (norm y pow 2 + &1)))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `&2`;
                 `\y:real^N. lift(y$k / (norm y pow 2 + &1))`]
    SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(y$k)`;
                 `\y:real^N. lift(norm y pow 2 + &1)`]
    SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; STEX_SMOOTH_NORM2_PLUS1; OPEN_UNIV;
           IN_UNIV; STEX_INV_STEREO_DENOM; REAL_LT_IMP_NZ]);;

let STEX_SMOOTH_INV_STEREO_HEIGHT = prove
 (`smooth_map_on (:real^N)
     (\y:real^N. lift((norm y pow 2 - &1) / (norm y pow 2 + &1))) /\
   smooth_map_on (:real^N)
     (\y:real^N. lift((&1 - norm y pow 2) / (norm y pow 2 + &1)))`,
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(norm y pow 2 - &1)`;
                   `\y:real^N. lift(norm y pow 2 + &1)`]
      SMOOTH_MAP_ON_LIFT_DIV);
    MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(&1 - norm y pow 2)`;
                   `\y:real^N. lift(norm y pow 2 + &1)`]
      SMOOTH_MAP_ON_LIFT_DIV)] THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[STEX_SMOOTH_NORM2_PLUS1; OPEN_UNIV; IN_UNIV;
           STEX_INV_STEREO_DENOM; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* The stereographic charts of S^3 in real^4 (north and south).              *)
(* ------------------------------------------------------------------------- *)

let STEX_BASIS_NEG_NEQ = prove
 (`!k. 1 <= k /\ k <= dimindex(:N) ==> ~(basis k:real^N = --(basis k))`,
  REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`] THEN
  MATCH_ACCEPT_TAC BASIS_NONZERO);;

(* North chart: projection from basis 4 onto real^3. *)

let STEX_STEREO3_N_COMPONENTS = prove
 (`!x:real^4. stereo3_n x$1 = x$1 / (&1 - x$4) /\
              stereo3_n x$2 = x$2 / (&1 - x$4) /\
              stereo3_n x$3 = x$3 / (&1 - x$4)`,
  SIMP_TAC[stereo3_n; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let STEX_STEREO3_N_INV_COMPONENTS = prove
 (`!y:real^3.
        stereo3_n_inv y$1 = &2 * y$1 / (norm y pow 2 + &1) /\
        stereo3_n_inv y$2 = &2 * y$2 / (norm y pow 2 + &1) /\
        stereo3_n_inv y$3 = &2 * y$3 / (norm y pow 2 + &1) /\
        stereo3_n_inv y$4 = (norm y pow 2 - &1) / (norm y pow 2 + &1)`,
  SIMP_TAC[stereo3_n_inv; LAMBDA_BETA; DIMINDEX_4; ARITH]);;

let STEX_STEREO3_N_DOMAIN = prove
 (`sphere(vec 0:real^4,&1) DELETE basis 4 SUBSET {x:real^4 | x$4 < &1}`,
  REWRITE_TAC[SUBSET; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^4` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^4`; `4`] STEX_SPHERE_COMPONENT_POLE) THEN
  ASM_REWRITE_TAC[DIMINDEX_4; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^4`; `4`] COMPONENT_LE_NORM) THEN
  UNDISCH_TAC `~((x:real^4)$4 = &1)` THEN
  UNDISCH_TAC `norm(x:real^4) = &1` THEN REAL_ARITH_TAC);;

let STEX_STEREO3_N_SMOOTH = prove
 (`smooth_map_on {x:real^4 | x$4 < &1} stereo3_n`,
  MP_TAC(ISPECL [`{x:real^4 | x$4 < &1}`; `stereo3_n`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^4. lift(stereo3_n x$k)) = (\x. lift(x$k / (&1 - x$4)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo3_n; LAMBDA_BETA; DIMINDEX_3];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^4 | x$4 < &1}`; `\x:real^4. lift(x$k)`;
                 `\x:real^4. lift(&1 - x$4)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    MP_TAC(ISPECL [`{x:real^4 | x$4 < &1}`; `\x:real^4. lift(&1)`;
                   `\x:real^4. lift(x$4)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_LT; SMOOTH_MAP_ON_CONST;
             SMOOTH_MAP_ON_LIFT_COORDINATE];
    REAL_ARITH_TAC]);;

let STEX_STEREO3_N_INV_SMOOTH = prove
 (`smooth_map_on (:real^3) stereo3_n_inv`,
  MP_TAC(ISPECL [`(:real^3)`; `stereo3_n_inv`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_4] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:real^3. lift(stereo3_n_inv y$k)) =
    (\y. lift(if k = 4 then (norm y pow 2 - &1) / (norm y pow 2 + &1)
              else &2 * y$k / (norm y pow 2 + &1)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo3_n_inv; LAMBDA_BETA; DIMINDEX_4];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:num) = 4` THEN
  ASM_REWRITE_TAC[STEX_SMOOTH_INV_STEREO_HEIGHT;
                  STEX_SMOOTH_INV_STEREO_COORD]);;

let STEX_STEREO3_N_NORM2 = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE basis 4
       ==> ~(&1 - x$4 = &0) /\
           norm(stereo3_n x) pow 2 = (&1 + x$4) / (&1 - x$4)`,
  X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 - (x:real^4)$4 = &0)` ASSUME_TAC THENL
   [MP_TAC STEX_STEREO3_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(x:real^4)$1 * x$1 + x$2 * x$2 + x$3 * x$3 + x$4 * x$4 = &1`
  MP_TAC THENL
   [UNDISCH_TAC `(x:real^4) IN sphere(vec 0,&1) DELETE basis 4` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; NORM_EQ_1; DOT_4];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3; STEX_STEREO3_N_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 - (x:real^4)$4 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO3_N_LEFT = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE basis 4
       ==> stereo3_n_inv(stereo3_n x) = x`,
  X_GEN_TAC `x:real^4` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO3_N_NORM2) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; STEX_STEREO3_N_INV_COMPONENTS] THEN
  ASM_REWRITE_TAC[STEX_STEREO3_N_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 - (x:real^4)$4 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO3_N_RIGHT = prove
 (`!y. stereo3_n(stereo3_n_inv y) = y`,
  X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_N_COMPONENTS;
              STEX_STEREO3_N_INV_COMPONENTS] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let STEX_STEREO3_N_INV_IN = prove
 (`!y. stereo3_n_inv y IN sphere(vec 0:real^4,&1) DELETE basis 4`,
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; DOT_4; STEX_STEREO3_N_INV_COMPONENTS] THEN
    REWRITE_TAC[NORM_POW_2; DOT_3] THEN
    SUBGOAL_THEN
     `~((y:real^3)$1 * y$1 + y$2 * y$2 + y$3 * y$3 + &1 = &0)`
    MP_TAC THENL
     [MP_TAC(SPEC `(y:real^3)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^3)$2` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^4. v$4`) THEN
    SIMP_TAC[STEX_STEREO3_N_INV_COMPONENTS; BASIS_COMPONENT; DIMINDEX_4;
             ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let STEX_STEREO3_N_CHART = prove
 (`open {x:real^4 | x$4 < &1} /\
   sphere(vec 0:real^4,&1) DELETE basis 4 SUBSET {x:real^4 | x$4 < &1} /\
   smooth_map_on {x:real^4 | x$4 < &1} stereo3_n /\
   smooth_map_on (:real^3) stereo3_n_inv /\
   (!x. x IN sphere(vec 0:real^4,&1) DELETE basis 4
        ==> stereo3_n_inv(stereo3_n x) = x) /\
   (!y. stereo3_n_inv y IN sphere(vec 0:real^4,&1) DELETE basis 4 /\
        stereo3_n(stereo3_n_inv y) = y)`,
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; STEX_STEREO3_N_DOMAIN;
              STEX_STEREO3_N_SMOOTH; STEX_STEREO3_N_INV_SMOOTH;
              STEX_STEREO3_N_LEFT; STEX_STEREO3_N_RIGHT;
              STEX_STEREO3_N_INV_IN]);;

(* South chart: projection from --(basis 4) onto real^3. *)

let STEX_STEREO3_S_COMPONENTS = prove
 (`!x:real^4. stereo3_s x$1 = x$1 / (&1 + x$4) /\
              stereo3_s x$2 = x$2 / (&1 + x$4) /\
              stereo3_s x$3 = x$3 / (&1 + x$4)`,
  SIMP_TAC[stereo3_s; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let STEX_STEREO3_S_INV_COMPONENTS = prove
 (`!y:real^3.
        stereo3_s_inv y$1 = &2 * y$1 / (norm y pow 2 + &1) /\
        stereo3_s_inv y$2 = &2 * y$2 / (norm y pow 2 + &1) /\
        stereo3_s_inv y$3 = &2 * y$3 / (norm y pow 2 + &1) /\
        stereo3_s_inv y$4 = (&1 - norm y pow 2) / (norm y pow 2 + &1)`,
  SIMP_TAC[stereo3_s_inv; LAMBDA_BETA; DIMINDEX_4; ARITH]);;

let STEX_STEREO3_S_DOMAIN = prove
 (`sphere(vec 0:real^4,&1) DELETE --(basis 4) SUBSET {x:real^4 | x$4 > -- &1}`,
  REWRITE_TAC[SUBSET; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^4` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^4`; `4`] STEX_SPHERE_COMPONENT_POLE) THEN
  ASM_REWRITE_TAC[DIMINDEX_4; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^4`; `4`] COMPONENT_LE_NORM) THEN
  UNDISCH_TAC `~((x:real^4)$4 = -- &1)` THEN
  UNDISCH_TAC `norm(x:real^4) = &1` THEN REAL_ARITH_TAC);;

let STEX_STEREO3_S_SMOOTH = prove
 (`smooth_map_on {x:real^4 | x$4 > -- &1} stereo3_s`,
  MP_TAC(ISPECL [`{x:real^4 | x$4 > -- &1}`; `stereo3_s`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^4. lift(stereo3_s x$k)) = (\x. lift(x$k / (&1 + x$4)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo3_s; LAMBDA_BETA; DIMINDEX_3];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^4 | x$4 > -- &1}`; `\x:real^4. lift(x$k)`;
                 `\x:real^4. lift(&1 + x$4)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
    MP_TAC(ISPECL [`{x:real^4 | x$4 > -- &1}`; `\x:real^4. lift(&1)`;
                   `\x:real^4. lift(x$4)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_GT; SMOOTH_MAP_ON_CONST;
             SMOOTH_MAP_ON_LIFT_COORDINATE];
    REAL_ARITH_TAC]);;

let STEX_STEREO3_S_INV_SMOOTH = prove
 (`smooth_map_on (:real^3) stereo3_s_inv`,
  MP_TAC(ISPECL [`(:real^3)`; `stereo3_s_inv`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_4] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:real^3. lift(stereo3_s_inv y$k)) =
    (\y. lift(if k = 4 then (&1 - norm y pow 2) / (norm y pow 2 + &1)
              else &2 * y$k / (norm y pow 2 + &1)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo3_s_inv; LAMBDA_BETA; DIMINDEX_4];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:num) = 4` THEN
  ASM_REWRITE_TAC[STEX_SMOOTH_INV_STEREO_HEIGHT;
                  STEX_SMOOTH_INV_STEREO_COORD]);;

let STEX_STEREO3_S_NORM2 = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE --(basis 4)
       ==> ~(&1 + x$4 = &0) /\
           norm(stereo3_s x) pow 2 = (&1 - x$4) / (&1 + x$4)`,
  X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 + (x:real^4)$4 = &0)` ASSUME_TAC THENL
   [MP_TAC STEX_STEREO3_S_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(x:real^4)$1 * x$1 + x$2 * x$2 + x$3 * x$3 + x$4 * x$4 = &1`
  MP_TAC THENL
   [UNDISCH_TAC `(x:real^4) IN sphere(vec 0,&1) DELETE --(basis 4)` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; NORM_EQ_1; DOT_4];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3; STEX_STEREO3_S_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 + (x:real^4)$4 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO3_S_LEFT = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE --(basis 4)
       ==> stereo3_s_inv(stereo3_s x) = x`,
  X_GEN_TAC `x:real^4` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO3_S_NORM2) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; STEX_STEREO3_S_INV_COMPONENTS] THEN
  ASM_REWRITE_TAC[STEX_STEREO3_S_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 + (x:real^4)$4 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO3_S_RIGHT = prove
 (`!y. stereo3_s(stereo3_s_inv y) = y`,
  X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_S_COMPONENTS;
              STEX_STEREO3_S_INV_COMPONENTS] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let STEX_STEREO3_S_INV_IN = prove
 (`!y. stereo3_s_inv y IN sphere(vec 0:real^4,&1) DELETE --(basis 4)`,
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; DOT_4; STEX_STEREO3_S_INV_COMPONENTS] THEN
    REWRITE_TAC[NORM_POW_2; DOT_3] THEN
    SUBGOAL_THEN
     `~((y:real^3)$1 * y$1 + y$2 * y$2 + y$3 * y$3 + &1 = &0)`
    MP_TAC THENL
     [MP_TAC(SPEC `(y:real^3)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^3)$2` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^4. v$4`) THEN
    SIMP_TAC[STEX_STEREO3_S_INV_COMPONENTS; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let STEX_STEREO3_S_CHART = prove
 (`open {x:real^4 | x$4 > -- &1} /\
   sphere(vec 0:real^4,&1) DELETE --(basis 4) SUBSET {x:real^4 | x$4 > -- &1} /\
   smooth_map_on {x:real^4 | x$4 > -- &1} stereo3_s /\
   smooth_map_on (:real^3) stereo3_s_inv /\
   (!x. x IN sphere(vec 0:real^4,&1) DELETE --(basis 4)
        ==> stereo3_s_inv(stereo3_s x) = x) /\
   (!y. stereo3_s_inv y IN sphere(vec 0:real^4,&1) DELETE --(basis 4) /\
        stereo3_s(stereo3_s_inv y) = y)`,
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; STEX_STEREO3_S_DOMAIN;
              STEX_STEREO3_S_SMOOTH; STEX_STEREO3_S_INV_SMOOTH;
              STEX_STEREO3_S_LEFT; STEX_STEREO3_S_RIGHT;
              STEX_STEREO3_S_INV_IN]);;

(* ------------------------------------------------------------------------- *)
(* The stereographic atlas of S^3, the inclusion, and the smooth Poincare    *)
(* statement for the 3-sphere.                                               *)
(* ------------------------------------------------------------------------- *)

let STEX_SPHERE_TWO_POLES_COVER = prove
 (`!x:real^N k.
        1 <= k /\ k <= dimindex(:N) /\ x IN sphere(vec 0,&1)
        ==> x IN sphere(vec 0,&1) DELETE basis k \/
            x IN sphere(vec 0,&1) DELETE --(basis k)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  ASM_CASES_TAC `x:real^N = basis k` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[STEX_BASIS_NEG_NEQ]);;

let SPHERE3_ATLAS = prove
 (`smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^4,&1)))
                         sphere3_atlas`,
  MATCH_MP_TAC STEX_GLOBAL_INVERSE_ATLAS THEN
  REWRITE_TAC[sphere3_atlas; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^4->bool`; `phi:real^4->real^3`] THEN
    DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN SUBST1_TAC)) THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THENL
     [MAP_EVERY EXISTS_TAC [`{x:real^4 | x$4 < &1}`; `stereo3_n_inv`] THEN
      REWRITE_TAC[STEX_STEREO3_N_CHART];
      MAP_EVERY EXISTS_TAC [`{x:real^4 | x$4 > -- &1}`; `stereo3_s_inv`] THEN
      REWRITE_TAC[STEX_STEREO3_S_CHART]];
    X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^4`; `4`] STEX_SPHERE_TWO_POLES_COVER) THEN
    ASM_REWRITE_TAC[DIMINDEX_4; ARITH] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC
       [`sphere(vec 0:real^4,&1) DELETE basis 4`; `stereo3_n`];
      MAP_EVERY EXISTS_TAC
       [`sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `stereo3_s`]] THEN
    ASM_REWRITE_TAC[]]);;

let SPHERE3_INCLUSION_IMMERSION = prove
 (`smooth_immersion_into sphere3_atlas (\x:real^4. x)`,
  MATCH_MP_TAC STEX_GLOBAL_INVERSE_IMMERSION THEN
  REWRITE_TAC[sphere3_atlas; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`U:real^4->bool`; `phi:real^4->real^3`] THEN
  DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`{x:real^4 | x$4 < &1}`; `stereo3_n_inv`] THEN
    REWRITE_TAC[STEX_STEREO3_N_CHART];
    MAP_EVERY EXISTS_TAC [`{x:real^4 | x$4 > -- &1}`; `stereo3_s_inv`] THEN
    REWRITE_TAC[STEX_STEREO3_S_CHART]]);;

(* The 3-sphere with its standard atlas satisfies the hypotheses of         *)
(* POINCARE_SMOOTH_STATEMENT, and the conclusion holds for it with the       *)
(* inclusion map.                                                            *)

let POINCARE_SMOOTH_HYPOTHESES_SPHERE_3 = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^4,&1)))
                         sphere3_atlas /\
   compact_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   ~(topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) = {}) /\
   simply_connected_space (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  REWRITE_TAC[SPHERE3_ATLAS] THEN
  MP_TAC POINCARE_HYPOTHESES_SPHERE_3 THEN SIMP_TAC[]);;

let POINCARE_SMOOTH_CONCLUSION_SPHERE_3 = prove
 (`?f:real^4->real^4.
        smooth_immersion_into sphere3_atlas f /\
        homeomorphic_map (subtopology euclidean (sphere(vec 0:real^4,&1)),
                          subtopology euclidean (sphere(vec 0,&1))) f`,
  EXISTS_TAC `\x:real^4. x` THEN
  REWRITE_TAC[SPHERE3_INCLUSION_IMMERSION; HOMEOMORPHIC_MAP_ID]);;

(* ------------------------------------------------------------------------- *)
(* The stereographic charts of S^2 in real^3 (north and south), the atlas of *)
(* S^2 and the inclusion of S^2.  Same pattern as for S^3.                   *)
(* ------------------------------------------------------------------------- *)

(* North chart: projection from basis 3 onto real^2. *)

let STEX_STEREO2_N_COMPONENTS = prove
 (`!x:real^3. stereo2_n x$1 = x$1 / (&1 - x$3) /\
              stereo2_n x$2 = x$2 / (&1 - x$3)`,
  SIMP_TAC[stereo2_n; LAMBDA_BETA; DIMINDEX_2; ARITH]);;

let STEX_STEREO2_N_INV_COMPONENTS = prove
 (`!y:real^2.
        stereo2_n_inv y$1 = &2 * y$1 / (norm y pow 2 + &1) /\
        stereo2_n_inv y$2 = &2 * y$2 / (norm y pow 2 + &1) /\
        stereo2_n_inv y$3 = (norm y pow 2 - &1) / (norm y pow 2 + &1)`,
  SIMP_TAC[stereo2_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let STEX_STEREO2_N_DOMAIN = prove
 (`sphere(vec 0:real^3,&1) DELETE basis 3 SUBSET {x:real^3 | x$3 < &1}`,
  REWRITE_TAC[SUBSET; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
  UNDISCH_TAC `~((x:real^3)$3 = &1)` THEN
  UNDISCH_TAC `norm(x:real^3) = &1` THEN REAL_ARITH_TAC);;

let STEX_STEREO2_N_SMOOTH = prove
 (`smooth_map_on {x:real^3 | x$3 < &1} stereo2_n`,
  MP_TAC(ISPECL [`{x:real^3 | x$3 < &1}`; `stereo2_n`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^3. lift(stereo2_n x$k)) = (\x. lift(x$k / (&1 - x$3)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo2_n; LAMBDA_BETA; DIMINDEX_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | x$3 < &1}`; `\x:real^3. lift(x$k)`;
                 `\x:real^3. lift(&1 - x$3)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    MP_TAC(ISPECL [`{x:real^3 | x$3 < &1}`; `\x:real^3. lift(&1)`;
                   `\x:real^3. lift(x$3)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_LT; SMOOTH_MAP_ON_CONST;
             SMOOTH_MAP_ON_LIFT_COORDINATE];
    REAL_ARITH_TAC]);;

let STEX_STEREO2_N_INV_SMOOTH = prove
 (`smooth_map_on (:real^2) stereo2_n_inv`,
  MP_TAC(ISPECL [`(:real^2)`; `stereo2_n_inv`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:real^2. lift(stereo2_n_inv y$k)) =
    (\y. lift(if k = 3 then (norm y pow 2 - &1) / (norm y pow 2 + &1)
              else &2 * y$k / (norm y pow 2 + &1)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo2_n_inv; LAMBDA_BETA; DIMINDEX_3];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:num) = 3` THEN
  ASM_REWRITE_TAC[STEX_SMOOTH_INV_STEREO_HEIGHT;
                  STEX_SMOOTH_INV_STEREO_COORD]);;

let STEX_STEREO2_N_NORM2 = prove
 (`!x. x IN sphere(vec 0:real^3,&1) DELETE basis 3
       ==> ~(&1 - x$3 = &0) /\
           norm(stereo2_n x) pow 2 = (&1 + x$3) / (&1 - x$3)`,
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 - (x:real^3)$3 = &0)` ASSUME_TAC THENL
   [MP_TAC STEX_STEREO2_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(x:real^3)$1 * x$1 + x$2 * x$2 + x$3 * x$3 = &1`
  MP_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1) DELETE basis 3` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; NORM_EQ_1; DOT_3];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2; STEX_STEREO2_N_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 - (x:real^3)$3 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO2_N_LEFT = prove
 (`!x. x IN sphere(vec 0:real^3,&1) DELETE basis 3
       ==> stereo2_n_inv(stereo2_n x) = x`,
  X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO2_N_NORM2) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_N_INV_COMPONENTS] THEN
  ASM_REWRITE_TAC[STEX_STEREO2_N_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 - (x:real^3)$3 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO2_N_RIGHT = prove
 (`!y. stereo2_n(stereo2_n_inv y) = y`,
  X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_N_COMPONENTS;
              STEX_STEREO2_N_INV_COMPONENTS] THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let STEX_STEREO2_N_INV_IN = prove
 (`!y. stereo2_n_inv y IN sphere(vec 0:real^3,&1) DELETE basis 3`,
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; DOT_3; STEX_STEREO2_N_INV_COMPONENTS] THEN
    REWRITE_TAC[NORM_POW_2; DOT_2] THEN
    SUBGOAL_THEN
     `~((y:real^2)$1 * y$1 + y$2 * y$2 + &1 = &0)`
    MP_TAC THENL
     [MP_TAC(SPEC `(y:real^2)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^2)$2` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[STEX_STEREO2_N_INV_COMPONENTS; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let STEX_STEREO2_N_CHART = prove
 (`open {x:real^3 | x$3 < &1} /\
   sphere(vec 0:real^3,&1) DELETE basis 3 SUBSET {x:real^3 | x$3 < &1} /\
   smooth_map_on {x:real^3 | x$3 < &1} stereo2_n /\
   smooth_map_on (:real^2) stereo2_n_inv /\
   (!x. x IN sphere(vec 0:real^3,&1) DELETE basis 3
        ==> stereo2_n_inv(stereo2_n x) = x) /\
   (!y. stereo2_n_inv y IN sphere(vec 0:real^3,&1) DELETE basis 3 /\
        stereo2_n(stereo2_n_inv y) = y)`,
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; STEX_STEREO2_N_DOMAIN;
              STEX_STEREO2_N_SMOOTH; STEX_STEREO2_N_INV_SMOOTH;
              STEX_STEREO2_N_LEFT; STEX_STEREO2_N_RIGHT;
              STEX_STEREO2_N_INV_IN]);;

(* South chart: projection from --(basis 3) onto real^2. *)

let STEX_STEREO2_S_COMPONENTS = prove
 (`!x:real^3. stereo2_s x$1 = x$1 / (&1 + x$3) /\
              stereo2_s x$2 = x$2 / (&1 + x$3)`,
  SIMP_TAC[stereo2_s; LAMBDA_BETA; DIMINDEX_2; ARITH]);;

let STEX_STEREO2_S_INV_COMPONENTS = prove
 (`!y:real^2.
        stereo2_s_inv y$1 = &2 * y$1 / (norm y pow 2 + &1) /\
        stereo2_s_inv y$2 = &2 * y$2 / (norm y pow 2 + &1) /\
        stereo2_s_inv y$3 = (&1 - norm y pow 2) / (norm y pow 2 + &1)`,
  SIMP_TAC[stereo2_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let STEX_STEREO2_S_DOMAIN = prove
 (`sphere(vec 0:real^3,&1) DELETE --(basis 3) SUBSET {x:real^3 | x$3 > -- &1}`,
  REWRITE_TAC[SUBSET; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
  UNDISCH_TAC `~((x:real^3)$3 = -- &1)` THEN
  UNDISCH_TAC `norm(x:real^3) = &1` THEN REAL_ARITH_TAC);;

let STEX_STEREO2_S_SMOOTH = prove
 (`smooth_map_on {x:real^3 | x$3 > -- &1} stereo2_s`,
  MP_TAC(ISPECL [`{x:real^3 | x$3 > -- &1}`; `stereo2_s`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^3. lift(stereo2_s x$k)) = (\x. lift(x$k / (&1 + x$3)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo2_s; LAMBDA_BETA; DIMINDEX_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | x$3 > -- &1}`; `\x:real^3. lift(x$k)`;
                 `\x:real^3. lift(&1 + x$3)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
    MP_TAC(ISPECL [`{x:real^3 | x$3 > -- &1}`; `\x:real^3. lift(&1)`;
                   `\x:real^3. lift(x$3)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[OPEN_HALFSPACE_COMPONENT_GT; SMOOTH_MAP_ON_CONST;
             SMOOTH_MAP_ON_LIFT_COORDINATE];
    REAL_ARITH_TAC]);;

let STEX_STEREO2_S_INV_SMOOTH = prove
 (`smooth_map_on (:real^2) stereo2_s_inv`,
  MP_TAC(ISPECL [`(:real^2)`; `stereo2_s_inv`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:real^2. lift(stereo2_s_inv y$k)) =
    (\y. lift(if k = 3 then (&1 - norm y pow 2) / (norm y pow 2 + &1)
              else &2 * y$k / (norm y pow 2 + &1)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; stereo2_s_inv; LAMBDA_BETA; DIMINDEX_3];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:num) = 3` THEN
  ASM_REWRITE_TAC[STEX_SMOOTH_INV_STEREO_HEIGHT;
                  STEX_SMOOTH_INV_STEREO_COORD]);;

let STEX_STEREO2_S_NORM2 = prove
 (`!x. x IN sphere(vec 0:real^3,&1) DELETE --(basis 3)
       ==> ~(&1 + x$3 = &0) /\
           norm(stereo2_s x) pow 2 = (&1 - x$3) / (&1 + x$3)`,
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 + (x:real^3)$3 = &0)` ASSUME_TAC THENL
   [MP_TAC STEX_STEREO2_S_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(x:real^3)$1 * x$1 + x$2 * x$2 + x$3 * x$3 = &1`
  MP_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1) DELETE --(basis 3)` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; NORM_EQ_1; DOT_3];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2; STEX_STEREO2_S_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 + (x:real^3)$3 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO2_S_LEFT = prove
 (`!x. x IN sphere(vec 0:real^3,&1) DELETE --(basis 3)
       ==> stereo2_s_inv(stereo2_s x) = x`,
  X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO2_S_NORM2) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_S_INV_COMPONENTS] THEN
  ASM_REWRITE_TAC[STEX_STEREO2_S_COMPONENTS] THEN
  UNDISCH_TAC `~(&1 + (x:real^3)$3 = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_STEREO2_S_RIGHT = prove
 (`!y. stereo2_s(stereo2_s_inv y) = y`,
  X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_S_COMPONENTS;
              STEX_STEREO2_S_INV_COMPONENTS] THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let STEX_STEREO2_S_INV_IN = prove
 (`!y. stereo2_s_inv y IN sphere(vec 0:real^3,&1) DELETE --(basis 3)`,
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; DOT_3; STEX_STEREO2_S_INV_COMPONENTS] THEN
    REWRITE_TAC[NORM_POW_2; DOT_2] THEN
    SUBGOAL_THEN
     `~((y:real^2)$1 * y$1 + y$2 * y$2 + &1 = &0)`
    MP_TAC THENL
     [MP_TAC(SPEC `(y:real^2)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(y:real^2)$2` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[STEX_STEREO2_S_INV_COMPONENTS; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let STEX_STEREO2_S_CHART = prove
 (`open {x:real^3 | x$3 > -- &1} /\
   sphere(vec 0:real^3,&1) DELETE --(basis 3) SUBSET {x:real^3 | x$3 > -- &1} /\
   smooth_map_on {x:real^3 | x$3 > -- &1} stereo2_s /\
   smooth_map_on (:real^2) stereo2_s_inv /\
   (!x. x IN sphere(vec 0:real^3,&1) DELETE --(basis 3)
        ==> stereo2_s_inv(stereo2_s x) = x) /\
   (!y. stereo2_s_inv y IN sphere(vec 0:real^3,&1) DELETE --(basis 3) /\
        stereo2_s(stereo2_s_inv y) = y)`,
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; STEX_STEREO2_S_DOMAIN;
              STEX_STEREO2_S_SMOOTH; STEX_STEREO2_S_INV_SMOOTH;
              STEX_STEREO2_S_LEFT; STEX_STEREO2_S_RIGHT;
              STEX_STEREO2_S_INV_IN]);;

(* ------------------------------------------------------------------------- *)
(* The stereographic atlas of S^2 and the inclusion of S^2.                 *)
(* ------------------------------------------------------------------------- *)

let SPHERE2_ATLAS = prove
 (`smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         sphere2_atlas`,
  MATCH_MP_TAC STEX_GLOBAL_INVERSE_ATLAS THEN
  REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `phi:real^3->real^2`] THEN
    DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN SUBST1_TAC)) THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THENL
     [MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 < &1}`; `stereo2_n_inv`] THEN
      REWRITE_TAC[STEX_STEREO2_N_CHART];
      MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 > -- &1}`; `stereo2_s_inv`] THEN
      REWRITE_TAC[STEX_STEREO2_S_CHART]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_TWO_POLES_COVER) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC
       [`sphere(vec 0:real^3,&1) DELETE basis 3`; `stereo2_n`];
      MAP_EVERY EXISTS_TAC
       [`sphere(vec 0:real^3,&1) DELETE --(basis 3)`; `stereo2_s`]] THEN
    ASM_REWRITE_TAC[]]);;

let SPHERE2_INCLUSION_IMMERSION = prove
 (`smooth_immersion_into sphere2_atlas (\x:real^3. x)`,
  MATCH_MP_TAC STEX_GLOBAL_INVERSE_IMMERSION THEN
  REWRITE_TAC[sphere2_atlas; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `phi:real^3->real^2`] THEN
  DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 < &1}`; `stereo2_n_inv`] THEN
    REWRITE_TAC[STEX_STEREO2_N_CHART];
    MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 > -- &1}`; `stereo2_s_inv`] THEN
    REWRITE_TAC[STEX_STEREO2_S_CHART]]);;

(* ------------------------------------------------------------------------- *)
(* Open subsets of real^N with the identity chart; images of the             *)
(* stereographic charts and their inverses; the inversion y |-> y/|y|^2 on   *)
(* real^N minus the origin and the transition maps of the sphere atlases.    *)
(* ------------------------------------------------------------------------- *)

let OPEN_SET_ATLAS = prove
 (`!U:real^N->bool.
        open U ==> smooth_manifold_atlas (subtopology euclidean U) (open_set_atlas U)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[smooth_manifold_atlas; open_set_atlas; IN_SING; PAIR_EQ;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL; IMAGE_ID; SUBTOPOLOGY_SUBTOPOLOGY;
                    INTER_IDEMPOT; HOMEOMORPHIC_MAP_ID];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `\x:real^N. x`] THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST1_TAC)
                               (CONJUNCTS_THEN SUBST1_TAC)) THEN
    EXISTS_TAC `\x:real^N. x` THEN REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

(* ------------------------------------------------------------------------- *)
(* The stereographic charts are homeomorphisms onto real^3 and real^2.       *)
(* ------------------------------------------------------------------------- *)

let STEX_STEREO3_HOMEOMORPHISMS = prove
 (`IMAGE stereo3_n (sphere(vec 0:real^4,&1) DELETE basis 4) = (:real^3) /\
   homeomorphism (sphere(vec 0:real^4,&1) DELETE basis 4,(:real^3))
                 (stereo3_n,stereo3_n_inv) /\
   IMAGE stereo3_s (sphere(vec 0:real^4,&1) DELETE --(basis 4)) = (:real^3) /\
   homeomorphism (sphere(vec 0:real^4,&1) DELETE --(basis 4),(:real^3))
                 (stereo3_s,stereo3_s_inv)`,
  MP_TAC(ISPECL [`sphere(vec 0:real^4,&1) DELETE basis 4`;
                 `{x:real^4 | x$4 < &1}`; `stereo3_n`; `stereo3_n_inv`]
    STEX_GLOBAL_INVERSE_HOMEOMORPHISM) THEN
  REWRITE_TAC[STEX_STEREO3_N_CHART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^4,&1) DELETE --(basis 4)`;
                 `{x:real^4 | x$4 > -- &1}`; `stereo3_s`; `stereo3_s_inv`]
    STEX_GLOBAL_INVERSE_HOMEOMORPHISM) THEN
  REWRITE_TAC[STEX_STEREO3_S_CHART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let STEX_STEREO2_HOMEOMORPHISMS = prove
 (`IMAGE stereo2_n (sphere(vec 0:real^3,&1) DELETE basis 3) = (:real^2) /\
   homeomorphism (sphere(vec 0:real^3,&1) DELETE basis 3,(:real^2))
                 (stereo2_n,stereo2_n_inv) /\
   IMAGE stereo2_s (sphere(vec 0:real^3,&1) DELETE --(basis 3)) = (:real^2) /\
   homeomorphism (sphere(vec 0:real^3,&1) DELETE --(basis 3),(:real^2))
                 (stereo2_s,stereo2_s_inv)`,
  MP_TAC(ISPECL [`sphere(vec 0:real^3,&1) DELETE basis 3`;
                 `{x:real^3 | x$3 < &1}`; `stereo2_n`; `stereo2_n_inv`]
    STEX_GLOBAL_INVERSE_HOMEOMORPHISM) THEN
  REWRITE_TAC[STEX_STEREO2_N_CHART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^3,&1) DELETE --(basis 3)`;
                 `{x:real^3 | x$3 > -- &1}`; `stereo2_s`; `stereo2_s_inv`]
    STEX_GLOBAL_INVERSE_HOMEOMORPHISM) THEN
  REWRITE_TAC[STEX_STEREO2_S_CHART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The inversion y |-> y / |y|^2 is a smooth involution of real^N minus the  *)
(* origin.                                                                   *)
(* ------------------------------------------------------------------------- *)

let STEX_SMOOTH_INVERSION = prove
 (`smooth_map_on ((:real^N) DELETE vec 0) (\y:real^N. inv(norm y pow 2) % y)`,
  SUBGOAL_THEN `open((:real^N) DELETE vec 0)` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`;
                 `\y:real^N. lift(inv(norm y pow 2))`; `\y:real^N. y`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\y:real^N. lift(norm y pow 2)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\y:real^N. y`]
      SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    SIMP_TAC[IN_DELETE; IN_UNIV; REAL_POW_EQ_0; NORM_EQ_0; ARITH]]);;

let STEX_INVERSION_INVOLUTION = prove
 (`!y:real^N. ~(y = vec 0)
              ==> ~(inv(norm y pow 2) % y = vec 0) /\
                  inv(norm(inv(norm y pow 2) % y) pow 2) %
                  (inv(norm y pow 2) % y) = y`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(y:real^N) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(norm(y:real^N) = &0)` THEN CONV_TAC REAL_FIELD);;

let STEX_DIFFEOMORPHISM_INVERSION = prove
 (`diffeomorphism_on ((:real^N) DELETE vec 0) ((:real^N) DELETE vec 0)
                     (\y:real^N. inv(norm y pow 2) % y)
                     (\y:real^N. inv(norm y pow 2) % y)`,
  REWRITE_TAC[diffeomorphism_on; STEX_SMOOTH_INVERSION] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV;
           STEX_INVERSION_INVOLUTION] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN
  MESON_TAC[STEX_INVERSION_INVOLUTION]);;

(* ------------------------------------------------------------------------- *)
(* Transition maps of the sphere atlases: on the chart image real^N minus   *)
(* the origin, both transitions are the inversion y |-> y / |y|^2.           *)
(* ------------------------------------------------------------------------- *)

let STEX_STEREO3_TRANSITION = prove
 (`!y:real^3.
        ~(y = vec 0)
        ==> stereo3_n_inv y IN sphere(vec 0,&1) DELETE --(basis 4) /\
            stereo3_s_inv y IN sphere(vec 0,&1) DELETE basis 4 /\
            stereo3_s(stereo3_n_inv y) = inv(norm y pow 2) % y /\
            stereo3_n(stereo3_s_inv y) = inv(norm y pow 2) % y`,
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `y:real^3` STEX_STEREO3_N_INV_IN) THEN
    SIMP_TAC[IN_DELETE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^4. v$4`) THEN
    SIMP_TAC[STEX_STEREO3_N_INV_COMPONENTS; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `y:real^3` STEX_STEREO3_S_INV_IN) THEN
    SIMP_TAC[IN_DELETE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^4. v$4`) THEN
    SIMP_TAC[STEX_STEREO3_S_INV_COMPONENTS; BASIS_COMPONENT; DIMINDEX_4;
             ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT;
                STEX_STEREO3_S_COMPONENTS; STEX_STEREO3_N_INV_COMPONENTS];
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT;
                STEX_STEREO3_N_COMPONENTS; STEX_STEREO3_S_INV_COMPONENTS]] THEN
  UNDISCH_TAC `&0 < norm(y:real^3) pow 2 + &1` THEN
  UNDISCH_TAC `~(norm(y:real^3) = &0)` THEN
  CONV_TAC REAL_FIELD);;

let STEX_STEREO2_TRANSITION = prove
 (`!y:real^2.
        ~(y = vec 0)
        ==> stereo2_n_inv y IN sphere(vec 0,&1) DELETE --(basis 3) /\
            stereo2_s_inv y IN sphere(vec 0,&1) DELETE basis 3 /\
            stereo2_s(stereo2_n_inv y) = inv(norm y pow 2) % y /\
            stereo2_n(stereo2_s_inv y) = inv(norm y pow 2) % y`,
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(y:real^2) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^2) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
    SIMP_TAC[IN_DELETE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[STEX_STEREO2_N_INV_COMPONENTS; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN
    SIMP_TAC[IN_DELETE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[STEX_STEREO2_S_INV_COMPONENTS; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
                STEX_STEREO2_S_COMPONENTS; STEX_STEREO2_N_INV_COMPONENTS];
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
                STEX_STEREO2_N_COMPONENTS; STEX_STEREO2_S_INV_COMPONENTS]] THEN
  UNDISCH_TAC `&0 < norm(y:real^2) pow 2 + &1` THEN
  UNDISCH_TAC `~(norm(y:real^2) = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* Each stereographic chart vanishes exactly at the opposite pole. *)

let STEX_STEREO3_ZERO = prove
 (`(!x. x IN sphere(vec 0:real^4,&1) DELETE basis 4
        ==> (stereo3_n x = vec 0 <=> x = --(basis 4))) /\
   (!x. x IN sphere(vec 0:real^4,&1) DELETE --(basis 4)
        ==> (stereo3_s x = vec 0 <=> x = basis 4))`,
  CONJ_TAC THEN X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^4`; `4`] STEX_SPHERE_COMPONENT_POLE) THEN
    UNDISCH_TAC `(x:real^4) IN sphere(vec 0,&1) DELETE basis 4` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; DIMINDEX_4; ARITH] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real^4` STEX_STEREO3_N_NORM2) THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0; NORM_0] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_N_COMPONENTS] THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_4; ARITH] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^4`; `4`] STEX_SPHERE_COMPONENT_POLE) THEN
    UNDISCH_TAC `(x:real^4) IN sphere(vec 0,&1) DELETE --(basis 4)` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; DIMINDEX_4; ARITH] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real^4` STEX_STEREO3_S_NORM2) THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0; NORM_0] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_S_COMPONENTS] THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
    REAL_ARITH_TAC]);;

let STEX_STEREO2_ZERO = prove
 (`(!x. x IN sphere(vec 0:real^3,&1) DELETE basis 3
        ==> (stereo2_n x = vec 0 <=> x = --(basis 3))) /\
   (!x. x IN sphere(vec 0:real^3,&1) DELETE --(basis 3)
        ==> (stereo2_s x = vec 0 <=> x = basis 3))`,
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
    UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1) DELETE basis 3` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; DIMINDEX_3; ARITH] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real^3` STEX_STEREO2_N_NORM2) THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0; NORM_0] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_N_COMPONENTS] THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
    UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1) DELETE --(basis 3)` THEN
    SIMP_TAC[IN_DELETE; IN_SPHERE_0; DIMINDEX_3; ARITH] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real^3` STEX_STEREO2_S_NORM2) THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0; NORM_0] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_S_COMPONENTS] THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC]);;

(* The image of the overlap of the two charts is real^N minus the origin. *)

let STEX_STEREO3_OVERLAP_IMAGE = prove
 (`IMAGE stereo3_n ((sphere(vec 0:real^4,&1) DELETE basis 4) INTER
                    (sphere(vec 0:real^4,&1) DELETE --(basis 4))) =
   (:real^3) DELETE vec 0 /\
   IMAGE stereo3_s ((sphere(vec 0:real^4,&1) DELETE basis 4) INTER
                    (sphere(vec 0:real^4,&1) DELETE --(basis 4))) =
   (:real^3) DELETE vec 0`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV; IN_INTER] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^4` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1 STEX_STEREO3_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[IN_DELETE];
    DISCH_TAC THEN EXISTS_TAC `stereo3_n_inv y` THEN
    MP_TAC(SPEC `y:real^3` STEX_STEREO3_TRANSITION) THEN
    MP_TAC(SPEC `y:real^3` STEX_STEREO3_N_INV_IN) THEN
    ASM_SIMP_TAC[IN_DELETE; STEX_STEREO3_N_RIGHT];
    DISCH_THEN(X_CHOOSE_THEN `x:real^4` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT2 STEX_STEREO3_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[IN_DELETE];
    DISCH_TAC THEN EXISTS_TAC `stereo3_s_inv y` THEN
    MP_TAC(SPEC `y:real^3` STEX_STEREO3_TRANSITION) THEN
    MP_TAC(SPEC `y:real^3` STEX_STEREO3_S_INV_IN) THEN
    ASM_SIMP_TAC[IN_DELETE; STEX_STEREO3_S_RIGHT]]);;

let STEX_STEREO2_OVERLAP_IMAGE = prove
 (`IMAGE stereo2_n ((sphere(vec 0:real^3,&1) DELETE basis 3) INTER
                    (sphere(vec 0:real^3,&1) DELETE --(basis 3))) =
   (:real^2) DELETE vec 0 /\
   IMAGE stereo2_s ((sphere(vec 0:real^3,&1) DELETE basis 3) INTER
                    (sphere(vec 0:real^3,&1) DELETE --(basis 3))) =
   (:real^2) DELETE vec 0`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV; IN_INTER] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1 STEX_STEREO2_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[IN_DELETE];
    DISCH_TAC THEN EXISTS_TAC `stereo2_n_inv y` THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_TRANSITION) THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
    ASM_SIMP_TAC[IN_DELETE; STEX_STEREO2_N_RIGHT];
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT2 STEX_STEREO2_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[IN_DELETE];
    DISCH_TAC THEN EXISTS_TAC `stereo2_s_inv y` THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_TRANSITION) THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN
    ASM_SIMP_TAC[IN_DELETE; STEX_STEREO2_S_RIGHT]]);;

(* The chart inverses of pc_mfd_base are the explicit inverse maps, and the  *)
(* transition maps chart_trans are the inversion on real^N minus 0.          *)

let STEX_SPHERE3_CHART_INV = prove
 (`chart_inv (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n) =
   stereo3_n_inv /\
   chart_inv (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s) =
   stereo3_s_inv`,
  REWRITE_TAC[FUN_EQ_THM; chart_inv; FST; SND] THEN CONJ_TAC THEN
  X_GEN_TAC `y:real^3` THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `x:real^4` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_MESON_TAC[STEX_STEREO3_N_LEFT];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[STEX_STEREO3_N_INV_IN; STEX_STEREO3_N_RIGHT];
    STRIP_TAC THEN ASM_MESON_TAC[STEX_STEREO3_S_LEFT];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[STEX_STEREO3_S_INV_IN; STEX_STEREO3_S_RIGHT]]);;

let STEX_SPHERE2_CHART_INV = prove
 (`chart_inv (sphere(vec 0:real^3,&1) DELETE basis 3,stereo2_n) =
   stereo2_n_inv /\
   chart_inv (sphere(vec 0:real^3,&1) DELETE --(basis 3),stereo2_s) =
   stereo2_s_inv`,
  REWRITE_TAC[FUN_EQ_THM; chart_inv; FST; SND] THEN CONJ_TAC THEN
  X_GEN_TAC `y:real^2` THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `x:real^3` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_MESON_TAC[STEX_STEREO2_N_LEFT];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[STEX_STEREO2_N_INV_IN; STEX_STEREO2_N_RIGHT];
    STRIP_TAC THEN ASM_MESON_TAC[STEX_STEREO2_S_LEFT];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[STEX_STEREO2_S_INV_IN; STEX_STEREO2_S_RIGHT]]);;

let STEX_SPHERE3_CHART_TRANS = prove
 (`!y. ~(y = vec 0)
       ==> chart_trans (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n)
                       (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s) y =
           inv(norm y pow 2) % y /\
           chart_trans (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s)
                       (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n) y =
           inv(norm y pow 2) % y`,
  SIMP_TAC[chart_trans; SND; STEX_SPHERE3_CHART_INV; STEX_STEREO3_TRANSITION]);;

let STEX_SPHERE2_CHART_TRANS = prove
 (`!y. ~(y = vec 0)
       ==> chart_trans (sphere(vec 0:real^3,&1) DELETE basis 3,stereo2_n)
                       (sphere(vec 0:real^3,&1) DELETE --(basis 3),stereo2_s) y =
           inv(norm y pow 2) % y /\
           chart_trans (sphere(vec 0:real^3,&1) DELETE --(basis 3),stereo2_s)
                       (sphere(vec 0:real^3,&1) DELETE basis 3,stereo2_n) y =
           inv(norm y pow 2) % y`,
  SIMP_TAC[chart_trans; SND; STEX_SPHERE2_CHART_INV; STEX_STEREO2_TRANSITION]);;

