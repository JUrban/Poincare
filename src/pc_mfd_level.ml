(* ========================================================================= *)
(* pc_mfd_level: regular level sets of a smooth function f on an open set    *)
(* W of a 3-manifold (top,atlas) as 2-manifolds.  The leaf N = lvs_set W f u *)
(* carries the subspace topology and the atlas lvs_atlas of ALL adapted      *)
(* charts (IMAGE e s INTER N, lvs_proj o e'), e an mfd_param of an open s    *)
(* of real^3 into W with inverse e' and f(e y) = u + y$3 (slice charts, Lee  *)
(* ISM Thm 5.8, Cor 5.14).  This file also fixes the vocabulary of the       *)
(* induced metric (lvs_jac, lvs_metric), the unit normal (lvs_df,            *)
(* lvs_normal) and the second fundamental form (lvs_II) used by              *)
(* pc_mfd_level2-4.  Results: adapted charts are charts, they cover N        *)
(* (SMOOTH_INVERSE_FUNCTION_THEOREM) and are compatible (LVS_MANIFOLD),      *)
(* Hausdorff and compactness corollaries, smoothness of restrictions and of  *)
(* the inclusion, shifted charts.                                            *)
(* ========================================================================= *)

needs "src/pc_mfd_restrict.ml";;
needs "src/pc_cmp_defs.ml";;
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The definitions.  The slice maps lvs_iota and lvs_proj; the level set and *)
(* its regularity (smooth on W, nonzero differential at the points of the    *)
(* level set, in the preferred chart); the adapted atlas.                    *)
(* ------------------------------------------------------------------------- *)

let lvs_iota = new_definition
 `lvs_iota (z:real^2) = vector[z$1; z$2; &0]:real^3`;;

let lvs_proj = new_definition
 `lvs_proj (y:real^3) = vector[y$1; y$2]:real^2`;;

let lvs_set = new_definition
 `lvs_set (W:A->bool) (f:A->real) (u:real) = {x | x IN W /\ f x = u}`;;

let lvs_regular = new_definition
 `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) (W:A->bool) (f:A->real)
              (u:real) <=>
    mfd_smooth_on atlas W (\x. lift(f x)) /\
    !x. x IN lvs_set W f u
        ==> ~(frechet_derivative (\y. lift(f(chart_inv (chart_at atlas x) y)))
                                 (at (SND(chart_at atlas x) x)) = (\h. vec 0))`;;

let lvs_atlas = new_definition
 `lvs_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
            (W:A->bool) (f:A->real) (u:real) =
    {(IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x))) | s,e,e' |
       mfd_diffeo euclidean (open_set_atlas (:real^3)) (s:real^3->bool) top atlas
                  (IMAGE (e:real^3->A) s) e (e':A->real^3) /\
       IMAGE e s SUBSET W /\
       (!y. y IN s ==> f(e y) = u + y$3)}`;;

(* The induced metric in the preferred adapted chart at x: J^T g(x) J, with  *)
(* J the 3x2 derivative of the inverse adapted chart, read in the preferred  *)
(* chart of atlas at x.                                                      *)

let lvs_jac = new_definition
 `lvs_jac (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
          (W:A->bool) (f:A->real) (u:real) (x:A) =
    frechet_derivative
      (\z:real^2. SND(chart_at atlas x)
                     (chart_inv (chart_at (lvs_atlas top atlas W f u) x) z))
      (at (SND(chart_at (lvs_atlas top atlas W f u) x) x))`;;

let lvs_metric = new_definition
 `lvs_metric (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
             (g:A->real^3^3) (W:A->bool) (f:A->real) (u:real) =
    \x. transp(matrix(lvs_jac top atlas W f u x)) ** g x **
        matrix(lvs_jac top atlas W f u x)`;;

(* The coordinate differential of f at x in the preferred chart, the unit    *)
(* normal grad f / |grad f|, and the second fundamental form                 *)
(* Hess(f|TN) / |grad f| as a 2x2 matrix in the preferred adapted chart      *)
(* (MT's shape operator S, as a bilinear form).                              *)

let lvs_df = new_definition
 `lvs_df (atlas:((A->bool)#(A->real^3))->bool) (f:A->real) (x:A) =
    (lambda i. drop(frechet_derivative
                      (\y. lift(f(chart_inv (chart_at atlas x) y)))
                      (at (SND(chart_at atlas x) x)) (basis i))):real^3`;;

let lvs_normal = new_definition
 `lvs_normal (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (f:A->real)
             (x:A) =
    inv(sqrt(lgrad2 (metric_local atlas (chart_at atlas x) g)
                    (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x))) %
    (matrix_inv(g x) ** lvs_df atlas f x)`;;

let lvs_II = new_definition
 `lvs_II (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
         (W:A->bool) (f:A->real) (u:real) (x:A) =
    (lambda a b.
       cmp_lhess (metric_local atlas (chart_at atlas x) g)
                 (\y. f(chart_inv (chart_at atlas x) y))
                 (SND(chart_at atlas x) x)
                 (lvs_jac top atlas W f u x (basis a))
                 (lvs_jac top atlas W f u x (basis b)) /
       sqrt(lgrad2 (metric_local atlas (chart_at atlas x) g)
                   (f o chart_inv (chart_at atlas x))
                   (SND(chart_at atlas x) x))):real^2^2`;;

(* ------------------------------------------------------------------------- *)
(* The slice maps lvs_iota : real^2 -> real^3 (z |-> (z,0)) and lvs_proj :   *)
(* real^3 -> real^2 (y |-> (y1,y2)).                                         *)
(* ------------------------------------------------------------------------- *)

let LVS_IOTA_COMPONENT = prove
 (`!z:real^2. (lvs_iota z)$1 = z$1 /\ (lvs_iota z)$2 = z$2 /\ (lvs_iota z)$3 = &0`,
  REWRITE_TAC[lvs_iota; VECTOR_3]);;

let LVS_PROJ_COMPONENT = prove
 (`!y:real^3. (lvs_proj y)$1 = y$1 /\ (lvs_proj y)$2 = y$2`,
  REWRITE_TAC[lvs_proj; VECTOR_2]);;

let LVS_PROJ_IOTA = prove
 (`!z:real^2. lvs_proj(lvs_iota z) = z`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT;
              LVS_IOTA_COMPONENT]);;

let LVS_IOTA_PROJ = prove
 (`!y:real^3. y$3 = &0 ==> lvs_iota(lvs_proj y) = y`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; LVS_PROJ_COMPONENT;
           LVS_IOTA_COMPONENT]);;

let LVS_IOTA_INJ = prove
 (`!z z':real^2. lvs_iota z = lvs_iota z' <=> z = z'`,
  MESON_TAC[LVS_PROJ_IOTA]);;

let LVS_IOTA_LINEAR = prove
 (`linear lvs_iota`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; LVS_IOTA_COMPONENT;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LVS_PROJ_LINEAR = prove
 (`linear lvs_proj`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let LVS_IOTA_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s lvs_iota`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\x:real^2. x`; `lvs_iota`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[LVS_IOTA_LINEAR; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let LVS_PROJ_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s lvs_proj`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. x`; `lvs_proj`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[LVS_PROJ_LINEAR; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let LVS_OPEN_IOTA_PREIMAGE = prove
 (`!s. open s ==> open {z:real^2 | lvs_iota z IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LVS_IOTA_LINEAR]);;

let LVS_IOTA_CONTINUOUS_MAP = prove
 (`!s. continuous_map (subtopology euclidean {z:real^2 | lvs_iota z IN s},
                       subtopology euclidean s) lvs_iota`,
  GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN2;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LVS_IOTA_LINEAR] THEN SET_TAC[]);;

let LVS_PROJ_CONTINUOUS_MAP = prove
 (`continuous_map (euclidean,euclidean) lvs_proj`,
  MP_TAC(ISPECL [`lvs_proj`; `(:real^3)`] CONTINUOUS_MAP_EUCLIDEAN) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LVS_PROJ_LINEAR]);;

(* ------------------------------------------------------------------------- *)
(* Adapted parametrizations.  Membership in lvs_atlas; the basic facts of an *)
(* mfd_diffeo from an open set of real^N; on the leaf the third coordinate   *)
(* vanishes, the chart image is the slice of the z with (z,0) IN s, and the  *)
(* inverse chart is z |-> e(z,0).                                            *)
(* ------------------------------------------------------------------------- *)

let LVS_ATLAS_IN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u (c:(A->bool)#(A->real^2)).
     c IN lvs_atlas top atlas W f u <=>
     ?s e e'. mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas
                         (IMAGE e s) e e' /\
              IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
              c = (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x)))`,
  REWRITE_TAC[lvs_atlas; IN_ELIM_THM] THEN MESON_TAC[]);;

let LVS_ATLAS_MEMBER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e'.
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3)
     ==> (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x))) IN
         lvs_atlas top atlas W f u`,
  REWRITE_TAC[LVS_ATLAS_IN] THEN MESON_TAC[]);;

let LVS_DIFFEO_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) e'.
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas (IMAGE e s) e e'
     ==> open s /\ open_in top (IMAGE e s) /\ IMAGE e s SUBSET topspace top /\
         continuous_map (subtopology euclidean s,top) e /\
         continuous_map (subtopology top (IMAGE e s),euclidean) e' /\
         (!y. y IN s ==> e'(e y) = y) /\
         (!x. x IN IMAGE e s ==> e' x IN s /\ e(e' x) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM OPEN_IN]) THEN
  ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `IMAGE (e':A->real^N) (IMAGE (e:real^N->A) s) SUBSET s` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^N->A) s` THEN REWRITE_TAC[IN_IMAGE] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let LVS_ADAPTED_LEAF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e'.
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3)
     ==> (!x. x IN IMAGE e s INTER lvs_set W f u
              ==> (e' x)$3 = &0 /\ lvs_iota(lvs_proj(e' x)) = e' x /\
                  lvs_iota(lvs_proj(e' x)) IN s) /\
         (!z. lvs_iota z IN s
              ==> e(lvs_iota z) IN IMAGE e s INTER lvs_set W f u /\
                  lvs_proj(e'(e(lvs_iota z))) = z) /\
         IMAGE (\x. lvs_proj(e' x)) (IMAGE e s INTER lvs_set W f u) =
         {z | lvs_iota z IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LVS_DIFFEO_FACTS) THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE e s INTER lvs_set W f u
        ==> ((e':A->real^3) x)$3 = &0 /\ lvs_iota(lvs_proj(e' x)) = e' x /\
            lvs_iota(lvs_proj(e' x)) IN s`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_INTER; lvs_set; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(e':A->real^3) x IN s /\ (e:real^3->A)(e' x) = x`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->real)((e:real^3->A)((e':A->real^3) x)) = u + (e' x)$3`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((e':A->real^3) x)$3 = &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LVS_IOTA_PROJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. lvs_iota z IN s
        ==> (e:real^3->A)(lvs_iota z) IN IMAGE e s INTER lvs_set W f u /\
            lvs_proj((e':A->real^3)(e(lvs_iota z))) = z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->A)(lvs_iota z) IN IMAGE e s` ASSUME_TAC THENL
     [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[IN_INTER; lvs_set; IN_ELIM_THM; LVS_PROJ_IOTA;
                 LVS_IOTA_COMPONENT; REAL_ADD_RID] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `(e:real^3->A)(lvs_iota z)` THEN
    ASM_MESON_TAC[]]);;

let LVS_CHART_INV = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e' z.
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\ lvs_iota z IN s
     ==> chart_inv (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x))) z =
         e(lvs_iota z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LVS_DIFFEO_FACTS) THEN
  REWRITE_TAC[chart_inv; FST; SND] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `lvs_iota z = (e':A->real^3) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[IN_INTER];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* An adapted chart is a chart of the leaf (subspace topology): its domain   *)
(* is open in N, its image is the open slice of the z with (z,0) IN s, and   *)
(* it is a homeomorphism with inverse z |-> e(z,0).                          *)
(* ------------------------------------------------------------------------- *)

let LVS_ADAPTED_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e'.
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3)
     ==> open_in (subtopology top (lvs_set W f u)) (IMAGE e s INTER lvs_set W f u) /\
         open (IMAGE (\x. lvs_proj(e' x)) (IMAGE e s INTER lvs_set W f u)) /\
         homeomorphic_map
           (subtopology (subtopology top (lvs_set W f u))
                        (IMAGE e s INTER lvs_set W f u),
            subtopology euclidean
              (IMAGE (\x. lvs_proj(e' x)) (IMAGE e s INTER lvs_set W f u)))
           (\x. lvs_proj(e' x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP LVS_DIFFEO_FACTS (CONJUNCT1 th)) THEN
    MP_TAC(MATCH_MP LVS_ADAPTED_LEAF th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "leaf1")
              (CONJUNCTS_THEN2 (LABEL_TAC "leaf2") SUBST1_TAC)) THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `IMAGE (e:real^3->A) s` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN
   `lvs_set W f u INTER (IMAGE (e:real^3->A) s INTER lvs_set W f u) =
    IMAGE e s INTER lvs_set W f u`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `\z:real^2. (e:real^3->A)(lvs_iota z)` THEN
  REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:A. lvs_proj((e':A->real^3) x)) = lvs_proj o e'`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN
      REWRITE_TAC[LVS_PROJ_CONTINUOUS_MAP] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `IMAGE (e:real^3->A) s` THEN ASM_REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER;
                  TOPSPACE_SUBTOPOLOGY] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      USE_THEN "leaf1" (MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; SIMP_TAC[]]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^2. (e:real^3->A)(lvs_iota z)) = e o lvs_iota`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN
      ASM_REWRITE_TAC[LVS_IOTA_CONTINUOUS_MAP];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      USE_THEN "leaf2" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "leaf1" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "leaf2" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Straightening a function with nonzero differential in real^3 (the inverse *)
(* function theorem SMOOTH_INVERSE_FUNCTION_THEOREM applied to Phi(y) = R(y  *)
(* - y0) + (g y - c) e3, R an orthogonal map Q followed by the projection to *)
(* the plane x3 = 0, with Q(grad g(y0)/|grad g(y0)|) = e3).                  *)
(* ------------------------------------------------------------------------- *)

let LVS_LINEAR_FUNCTIONAL_DOT = prove
 (`!L:real^N->real^1. linear L ==> !h. drop(L h) = (matrix L)$1 dot h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drop] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
                         [GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_1; LE_REFL]);;

let LVS_COMPLETE_LINEAR = prove
 (`!L:real^3->real^1.
     linear L /\ ~(L = (\h. vec 0))
     ==> ?R:real^3->real^3.
           linear R /\ (!h. (R h)$3 = &0) /\
           (!h. R h + drop(L h) % basis 3 = vec 0 ==> h = vec 0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = (matrix(L:real^3->real^1))$1` THEN
  SUBGOAL_THEN `!h. drop((L:real^3->real^1) h) = v dot h` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC LVS_LINEAR_FUNCTIONAL_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((L:real^3->real^1) = (\h. vec 0))` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REWRITE_TAC[DROP_VEC; DOT_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Q. orthogonal_transformation (Q:real^3->real^3) /\
                    Q(inv(norm(v:real^3)) % v) = basis 3`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_EXISTS THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
                 NORM_EQ_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(Q:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. (Q:real^3->real^3) a dot Q b = a dot b` ASSUME_TAC THENL
   [ASM_MESON_TAC[orthogonal_transformation]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. ((Q:real^3->real^3) h)$3 = inv(norm(v:real^3)) * drop((L:real^3->real^1) h)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(Q:real^3->real^3) h dot Q(inv(norm(v:real^3)) % v)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `(Q:real^3->real^3)(inv(norm(v:real^3)) % v) = basis 3`] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
      REWRITE_TAC[ASSUME `!a b. (Q:real^3->real^3) a dot Q b = a dot b`; DOT_RMUL] THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM];
    ALL_TAC] THEN
  EXISTS_TAC `\h:real^3. (Q:real^3->real^3) h - ((Q h)$3) % basis 3` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `h:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `drop((L:real^3->real^1) h) = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w$3`) THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; DIMINDEX_3; ARITH; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `((Q:real^3->real^3) h)$3 = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `(Q:real^3->real^3) h = vec 0` ASSUME_TAC THENL
     [UNDISCH_TAC
       `(Q:real^3->real^3) h - ((Q h)$3) % basis 3 +
        drop((L:real^3->real^1) h) % basis 3 = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_SUB_RZERO];
      ALL_TAC] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE; LINEAR_0]]);;

let LVS_STRAIGHTEN = prove
 (`!S0 (g:real^3->real) y0 c.
     open S0 /\ y0 IN S0 /\ smooth_map_on S0 (\y. lift(g y)) /\
     ~(frechet_derivative (\y. lift(g y)) (at y0) = (\h. vec 0))
     ==> ?t t' (Phi:real^3->real^3) (Psi:real^3->real^3).
                        open t /\ y0 IN t /\ t SUBSET S0 /\
                        diffeomorphism_on t t' Phi Psi /\
                        (!y. y IN t ==> g y = c + (Phi y)$3)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = frechet_derivative (\y. lift((g:real^3->real) y)) (at y0)` THEN
  SUBGOAL_THEN `((\y. lift((g:real^3->real) y)) has_derivative L) (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S0:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(L:real^3->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  MP_TAC(ISPEC `L:real^3->real^1` LVS_COMPLETE_LINEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
  ABBREV_TAC
   `Phi = \y:real^3. (R:real^3->real^3)(y - y0) + ((g:real^3->real) y - c) % basis 3` THEN
  SUBGOAL_THEN `!y. ((Phi:real^3->real^3) y)$3 = (g:real^3->real) y - c`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S0 (Phi:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\y:real^3. (R:real^3->real^3)(y - y0)) = R o (\y. y - y0)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      SUBGOAL_THEN
       `(\y:real^3. ((g:real^3->real) y - c) % basis 3:real^3) =
        (\y. drop((\y. lift(g y) - lift c) y) % basis 3)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; DROP_SUB; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\y. (R:real^3->real^3)(y - y0)) has_derivative R) (at y0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y:real^3. (R:real^3->real^3)(y - y0)) = (\y. R y - R y0)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; LINEAR_SUB]; ALL_TAC] THEN
    MP_TAC(ISPECL [`R:real^3->real^3`; `R:real^3->real^3`;
                   `\y:real^3. (R:real^3->real^3) y0`; `\h:real^3. vec 0:real^3`;
                   `at (y0:real^3)`] HAS_DERIVATIVE_SUB) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO;
                 ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. ((g:real^3->real) y - c) % basis 3:real^3) has_derivative
     (\h. drop((L:real^3->real^1) h) % basis 3)) (at y0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `((\y. lift((g:real^3->real) y) - lift c) has_derivative
       (\h. (L:real^3->real^1) h - vec 0)) (at y0)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX];
      DISCH_THEN(MP_TAC o ISPEC `basis 3:real^3` o
                 MATCH_MP HAS_DERIVATIVE_VMUL_DROP) THEN
      REWRITE_TAC[DROP_SUB; LIFT_DROP; DROP_VEC; REAL_SUB_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((Phi:real^3->real^3) has_derivative
     (\h. (R:real^3->real^3) h + drop((L:real^3->real^1) h) % basis 3)) (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear (\h. (R:real^3->real^3) h + drop((L:real^3->real^1) h) % basis 3)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(det(matrix(frechet_derivative (Phi:real^3->real^3) (at y0))) = &0)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `h:real^3` THEN
    ONCE_REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN
    USE_THEN "inj" (MATCH_ACCEPT_TAC o SPEC `h:real^3`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `S0:real^3->bool`; `y0:real^3`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `t':real^3->bool`
    (X_CHOOSE_THEN `Psi:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `t':real^3->bool`;
                        `Phi:real^3->real^3`; `Psi:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Adapted parametrizations exist around every point of a regular level set: *)
(* e = chart_inv c o Psi, with Psi the inverse of the straightening map of f *)
(* in the preferred chart c at x.                                            *)
(* ------------------------------------------------------------------------- *)

let LVS_ADAPTED_EXISTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u
     ==> ?s e e'. mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas
                             (IMAGE e s) e e' /\
                  IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
                  x IN IMAGE e s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set W f u` THEN
    SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lvs_regular]) THEN
  SUBGOAL_THEN
   `~(frechet_derivative
        (\y. lift((f:A->real)(chart_inv (chart_at atlas x) y)))
        (at (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x) x)) =
      (\h. vec 0))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^3)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^3`
    SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  MP_TAC(ISPECL [`IMAGE (psi:A->real^3) (V INTER W)`;
                 `\y:real^3. (f:A->real)(chart_inv (V,psi) y)`;
                 `(psi:A->real^3) x`; `u:real`] LVS_STRAIGHTEN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
                               (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^3)`) THEN
      ASM_REWRITE_TAC[FST; SND; o_DEF];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `t':real^3->bool`
    (X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Psi:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `mfd_param top atlas t' (chart_inv (V:A->bool,psi:A->real^3) o
                            (Psi:real^3->real^3))`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->real^3) V`; `t:real^3->bool`;
                          `Phi:real^3->real^3`] THEN
    ASM_SIMP_TAC[MFD_PARAM_CHART_INV; DIFFEOMORPHISM_ON_SYM] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (psi:A->real^3) (V INTER W)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`t':real^3->bool`;
                        `chart_inv (V:A->bool,psi:A->real^3) o (Psi:real^3->real^3)`;
                        `e':A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `V:A->bool`; `psi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cinv") (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!y. y IN t'
        ==> (Psi:real^3->real^3) y IN IMAGE (psi:A->real^3) (V INTER W)`
  (LABEL_TAC "psit") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) y IN t` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "psit" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) y IN t` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:A->real)(chart_inv (V,psi) ((Psi:real^3->real^3) y)) =
      u + ((Phi:real^3->real^3)(Psi y))$3`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_IMAGE; o_THM] THEN
    EXISTS_TAC `(Phi:real^3->real^3)((psi:A->real^3) x)` THEN
    SUBGOAL_THEN `(psi:A->real^3) x IN t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Adapted charts are smoothly compatible.  The transition is z |->          *)
(* lvs_proj(e2'(e1(z,0))) on the open slice of s12, the set of y IN s1 with  *)
(* e1 y IN e2(s2), where e2' o e1 is smooth.                                 *)
(* ------------------------------------------------------------------------- *)

let LVS_EUCLIDEAN_ATLAS = prove
 (`smooth_manifold_atlas (euclidean:(real^N)topology) (open_set_atlas (:real^N))`,
  MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let LVS_PARAM_TRANS_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s1 e1 e1' s2 e2 e2'.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s1 top atlas (IMAGE e1 s1) e1 e1' /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s2 top atlas (IMAGE e2 s2) e2 e2'
     ==> open {y | y IN s1 /\ e1 y IN IMAGE e2 s2} /\
         smooth_map_on {y | y IN s1 /\ e1 y IN IMAGE e2 s2} (e2' o e1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s1:real^N->bool`; `e1:real^N->A`; `e1':A->real^N`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s2:real^N->bool`; `e2:real^N->A`; `e2':A->real^N`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s12 = {y | y IN s1 /\ (e1:real^N->A) y IN IMAGE (e2:real^N->A) s2}` THEN
  SUBGOAL_THEN `open (s12:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s12" THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e1:real^N->A`; `subtopology euclidean (s1:real^N->bool)`;
                   `top:A topology`; `IMAGE (e2:real^N->A) s2`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s12:real^N->bool) SUBSET s1` ASSUME_TAC THENL
   [EXPAND_TAC "s12" THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^N)) s2 top
                 (atlas:((A->bool)#(A->real^N))->bool)
                 (IMAGE (e2:real^N->A) s2) e2 (e2':A->real^N)` THEN
  UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^N)) s1 top
                 (atlas:((A->bool)#(A->real^N))->bool)
                 (IMAGE (e1:real^N->A) s1) e1 (e1':A->real^N)` THEN
  REWRITE_TAC[mfd_diffeo] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `s12:real^N->bool`; `IMAGE (e2:real^N->A) s2`;
                 `e1:real^N->A`; `e2':A->real^N`] MFD_SMOOTH_MAP_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s12" THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNIV]);;

let LVS_ADAPTED_COMPAT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s1 e1 e1' s2 e2 e2'.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s1 top atlas (IMAGE e1 s1) e1 e1' /\
     IMAGE e1 s1 SUBSET W /\ (!y. y IN s1 ==> f(e1 y) = u + y$3) /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s2 top atlas (IMAGE e2 s2) e2 e2' /\
     IMAGE e2 s2 SUBSET W /\ (!y. y IN s2 ==> f(e2 y) = u + y$3)
     ==> ?g. smooth_map_on
               (IMAGE (\x. lvs_proj(e1' x))
                  ((IMAGE e1 s1 INTER lvs_set W f u) INTER
                   (IMAGE e2 s2 INTER lvs_set W f u))) g /\
             !x. x IN (IMAGE e1 s1 INTER lvs_set W f u) INTER
                      (IMAGE e2 s2 INTER lvs_set W f u)
                 ==> g(lvs_proj(e1' x)) = lvs_proj(e2' x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s1:real^3->bool`;
                 `e1:real^3->A`; `e1':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1a")
              (CONJUNCTS_THEN2 (LABEL_TAC "l1b") (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s1:real^3->bool`; `e1:real^3->A`; `e1':A->real^3`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s1:real^3->bool`; `e1:real^3->A`; `e1':A->real^3`;
                 `s2:real^3->bool`; `e2:real^3->A`; `e2':A->real^3`]
                LVS_PARAM_TRANS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s12 = {y | y IN s1 /\ (e1:real^3->A) y IN IMAGE (e2:real^3->A) s2}` THEN
  EXISTS_TAC `\z:real^2. lvs_proj((e2':A->real^3)((e1:real^3->A)(lvs_iota z)))` THEN
  SUBGOAL_THEN
   `IMAGE (\x. lvs_proj((e1':A->real^3) x))
      ((IMAGE (e1:real^3->A) s1 INTER lvs_set W f u) INTER
       (IMAGE (e2:real^3->A) s2 INTER lvs_set W f u)) =
    {z | lvs_iota z IN s12}`
  SUBST1_TAC THENL
   [EXPAND_TAC "s12" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      USE_THEN "l1a" (MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; STRIP_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM IN_IMAGE] THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(e1:real^3->A)(lvs_iota z)` THEN
      USE_THEN "l1b" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC
       `(e1:real^3->A)(lvs_iota z) IN IMAGE e1 s1 INTER lvs_set W f u` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^2. lvs_proj((e2':A->real^3)((e1:real^3->A)(lvs_iota z)))) =
      lvs_proj o ((e2' o e1) o lvs_iota)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[LVS_PROJ_LINEAR; LVS_OPEN_IOTA_PREIMAGE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `s12:real^3->bool` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; LVS_IOTA_SMOOTH] THEN SET_TAC[];
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "l1a" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; STRIP_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The leaf is a smooth 2-manifold (LVS_MANIFOLD), Hausdorff when top is,    *)
(* compact when it is a compact subset of top; closedness and compactness    *)
(* from compact sublevel sets of a continuous f.                             *)
(* ------------------------------------------------------------------------- *)

let LVS_SET_SUBSET = prove
 (`!W (f:A->real) u. lvs_set W f u SUBSET W`,
  REWRITE_TAC[lvs_set] THEN SET_TAC[]);;

let LVS_TOPSPACE = prove
 (`!top W (f:A->real) u.
     open_in top W ==> topspace (subtopology top (lvs_set W f u)) = lvs_set W f u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  MP_TAC(ISPECL [`W:A->bool`; `f:A->real`; `u:real`] LVS_SET_SUBSET) THEN
  SET_TAC[]);;

let LVS_MANIFOLD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u
     ==> smooth_manifold_atlas (subtopology top (lvs_set W f u))
                               (lvs_atlas top atlas W f u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_manifold_atlas] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^2`] THEN
    REWRITE_TAC[LVS_ATLAS_IN; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                   `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_CHART) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN ASM_SIMP_TAC[LVS_TOPSPACE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                  LVS_ADAPTED_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (e:real^3->A) s INTER lvs_set W f u`;
                          `\x. lvs_proj((e':A->real^3) x)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LVS_ATLAS_MEMBER THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER]];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^2`;
                         `V:A->bool`; `psi:A->real^2`] THEN
    REWRITE_TAC[LVS_ATLAS_IN; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `e1:real^3->A`
       (X_CHOOSE_THEN `e1':A->real^3` STRIP_ASSUME_TAC)))
     (X_CHOOSE_THEN `s2:real^3->bool` (X_CHOOSE_THEN `e2:real^3->A`
       (X_CHOOSE_THEN `e2':A->real^3` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`;
                   `s1:real^3->bool`; `e1:real^3->A`; `e1':A->real^3`;
                   `s2:real^3->bool`; `e2:real^3->A`; `e2':A->real^3`]
                  LVS_ADAPTED_COMPAT) THEN
    ASM_REWRITE_TAC[]]);;

let LVS_HAUSDORFF = prove
 (`!top W (f:A->real) u.
     hausdorff_space top ==> hausdorff_space (subtopology top (lvs_set W f u))`,
  SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY]);;

let LVS_COMPACT = prove
 (`!top W (f:A->real) u.
     compact_in top (lvs_set W f u)
     ==> compact_space (subtopology top (lvs_set W f u))`,
  SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY]);;

let LVS_CLOSED_IN = prove
 (`!top W (f:A->real) u.
     open_in top W /\ continuous_map (subtopology top W,euclideanreal) f
     ==> closed_in (subtopology top W) (lvs_set W f u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed_in euclideanreal {u:real}` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_T1_SING THEN
    REWRITE_TAC[T1_SPACE_EUCLIDEANREAL; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->real`; `subtopology top (W:A->bool)`; `euclideanreal`;
                 `{u:real}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[lvs_set; TOPSPACE_SUBTOPOLOGY; IN_SING] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]);;

let LVS_COMPACT_SUBLEVEL = prove
 (`!top (f:A->real) u c.
     continuous_map (top,euclideanreal) f /\
     compact_in top {x | x IN topspace top /\ f x <= c} /\ u <= c
     ==> compact_in top (lvs_set (topspace top) f u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `{x:A | x IN topspace top /\ f x <= c}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[lvs_set; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_REFL];
    SUBGOAL_THEN `closed_in euclideanreal {u:real}` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_T1_SING THEN
      REWRITE_TAC[T1_SPACE_EUCLIDEANREAL; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:A->real`; `top:A topology`; `euclideanreal`;
                   `{u:real}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[lvs_set; IN_SING]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness.  A parametrization read in a chart of atlas is smooth; smooth *)
(* functions on W restrict to smooth functions on the leaf; the inverse      *)
(* adapted charts read in the charts of atlas are smooth                     *)
(* (LVS_CHART_AMBIENT), so the inclusion of the leaf is smooth.              *)
(* ------------------------------------------------------------------------- *)

let LVS_PARAM_CHART_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) e' c.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas (IMAGE e s) e e' /\
     c IN atlas
     ==> open {y | y IN s /\ e y IN FST c} /\
         smooth_map_on {y | y IN s /\ e y IN FST c} (SND c o e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `e':A->real^N`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^N))
                  (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A)`
  MP_TAC THENL [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  DISCH_THEN(MP_TAC o SPECL [`((:real^N),(\x:real^N. x))`;
                             `c:(A->bool)#(A->real^N)`]) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV; IN_UNIV] THEN
  DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o e o chart_inv ((:real^N),(\x:real^N. x))` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID; IN_UNIV]);;

let LVS_PARAM_SMOOTH_COMPOSE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W s (e:real^N->A) e' (k:A->real^K).
     smooth_manifold_atlas top atlas /\ open_in top W /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ mfd_smooth_on atlas W k
     ==> smooth_map_on s (k o e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `e':A->real^N`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[FUN_IN_IMAGE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `e':A->real^N`;
                 `c:(A->bool)#(A->real^N)`] LVS_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `((k:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
              (SND c o (e:real^N->A))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[FUN_IN_IMAGE; SUBSET];
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                               (k:A->real^K)` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let LVS_SMOOTH_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u (k:A->real^K).
     smooth_manifold_atlas top atlas /\ open_in top W /\ mfd_smooth_on atlas W k
     ==> mfd_smooth_on (lvs_atlas top atlas W f u) (lvs_set W f u) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_on] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^2)` THEN REWRITE_TAC[LVS_ATLAS_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN
   `(IMAGE (e:real^3->A) s INTER lvs_set W f u) INTER lvs_set W f u =
    IMAGE e s INTER lvs_set W f u`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `((k:A->real^K) o (e:real^3->A)) o lvs_iota` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `s:real^3->bool` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; LVS_IOTA_SMOOTH] THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC LVS_PARAM_SMOOTH_COMPOSE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^3))->bool`;
                            `W:A->bool`; `e':A->real^3`] THEN
      ASM_REWRITE_TAC[]]]);;

let LVS_CHART_AMBIENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u c c'.
     smooth_manifold_atlas top atlas /\
     c IN lvs_atlas top atlas W f u /\ c' IN atlas
     ==> open {w | w IN IMAGE (SND c) (FST c) /\ chart_inv c w IN FST c'} /\
         smooth_map_on {w | w IN IMAGE (SND c) (FST c) /\ chart_inv c w IN FST c'}
                       (\w. SND c' (chart_inv c w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LVS_ATLAS_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
     (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c':(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{w | w IN {z | lvs_iota z IN s} /\
         chart_inv (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj((e':A->real^3) x))) w
         IN FST(c':(A->bool)#(A->real^3))} =
    {z | lvs_iota z IN {y | y IN s /\ (e:real^3->A) y IN FST c'}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    ASM_CASES_TAC `lvs_iota z IN (s:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(SND(c':(A->bool)#(A->real^3)) o (e:real^3->A)) o lvs_iota` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c':(A->bool)#(A->real^3))}` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; LVS_IOTA_SMOOTH] THEN SET_TAC[]]);;

let LVS_INCLUSION_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u
     ==> mfd_smooth_map (lvs_atlas top atlas W f u) atlas (lvs_set W f u) (\x. x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`;
                 `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`]
                LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[LVS_MANIFOLD] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w. SND(c':(A->bool)#(A->real^3))
                   (chart_inv (c:(A->bool)#(A->real^2)) w)` THEN
  REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `{w | w IN IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c) /\
                   chart_inv c w IN FST(c':(A->bool)#(A->real^3))}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Shifted adapted charts (an adapted parametrization for the level u,       *)
(* translated by c e3, is adapted for the level u + c) and the sanity        *)
(* instance: the plane y3 = 0 is a regular level set of y |-> y3 on real^3,  *)
(* a nonempty smooth 2-manifold.                                             *)
(* ------------------------------------------------------------------------- *)

let LVS_TRANSLATION_DIFFEO = prove
 (`!s (a:real^N).
     open s
     ==> diffeomorphism_on (IMAGE (\y. y - a) s) s (\y. y + a) (\y. y - a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  SUBGOAL_THEN `IMAGE (\y:real^N. y - a) s = IMAGE (\y. --a + y) s` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_TRANSLATION] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `(--a + y) + a:real^N = y`;
                IMAGE_ID];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[OPEN_TRANSLATION; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

let LVS_ATLAS_SHIFT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e' c.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3)
     ==> (IMAGE e s INTER lvs_set W f (u + c),(\x. lvs_proj(e' x - c % basis 3)))
         IN lvs_atlas top atlas W f (u + c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `c % basis 3:real^3`] LVS_TRANSLATION_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_diffeo euclidean (open_set_atlas (:real^3))
               (IMAGE (\y. y - c % basis 3) s) top
               (atlas:((A->bool)#(A->real^3))->bool) (IMAGE (e:real^3->A) s)
               (e o (\y. y + c % basis 3)) ((\y. y - c % basis 3) o (e':A->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN];
    ALL_TAC] THEN
  REWRITE_TAC[LVS_ATLAS_IN] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (\y:real^3. y - c % basis 3) s`;
                        `(e:real^3->A) o (\y. y + c % basis 3)`;
                        `(\y:real^3. y - c % basis 3) o (e':A->real^3)`] THEN
  SUBGOAL_THEN
   `IMAGE ((e:real^3->A) o (\y. y + c % basis 3)) (IMAGE (\y. y - c % basis 3) s) =
    IMAGE e s`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF;
                VECTOR_ARITH `(y - c % basis 3) + c % basis 3:real^3 = y`] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; o_THM;
                VECTOR_ARITH `(y - c % basis 3) + c % basis 3:real^3 = y`] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    REWRITE_TAC[PAIR_EQ; FUN_EQ_THM; o_THM]]);;

let LVS_SANITY_PLANE = prove
 (`lvs_regular (open_set_atlas (:real^3)) (:real^3) (\y:real^3. y$3) (&0) /\
   ~(lvs_set (:real^3) (\y:real^3. y$3) (&0) = {}) /\
   smooth_manifold_atlas
     (subtopology euclidean (lvs_set (:real^3) (\y:real^3. y$3) (&0)))
     (lvs_atlas euclidean (open_set_atlas (:real^3)) (:real^3)
                (\y:real^3. y$3) (&0))`,
  SUBGOAL_THEN
   `!x:real^3. chart_at (open_set_atlas (:real^3)) x = ((:real^3),(\x. x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `x:real^3`] CHART_AT) THEN
    REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    REWRITE_TAC[open_set_atlas; IN_SING] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lvs_regular (open_set_atlas (:real^3)) (:real^3) (\y:real^3. y$3) (&0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[lvs_regular] THEN
    SUBGOAL_THEN
     `!y:real^3. chart_inv ((:real^3),(\x:real^3. x)) y = y`
    ASSUME_TAC THENL [SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FST; SND; ETA_AX] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_smooth_on; open_set_atlas; IN_SING] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV; o_DEF] THEN
      SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; OPEN_UNIV; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative (\y:real^3. lift(y$3)) (at x) = (\y. lift(y$3))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `basis 3:real^3`) THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; GSYM DROP_EQ; LIFT_DROP;
             DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; lvs_set; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[VEC_COMPONENT];
    MATCH_MP_TAC LVS_MANIFOLD THEN
    ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; GSYM OPEN_IN; OPEN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* Regularity from adapted parametrizations.  If f is smooth on W and every  *)
(* point of the level set lies in the image of a parametrization e with f(e  *)
(* y) = u + y$3 (e.g. flow charts), then the level set is regular: d(f o     *)
(* chart_inv c) o D(SND c o e) = d(y |-> y3).                                *)
(* ------------------------------------------------------------------------- *)

let LVS_REGULAR_ADAPTED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     mfd_smooth_on atlas W (\x. lift(f x)) /\
     (!x. x IN lvs_set W f u
          ==> ?s e e'. mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas
                                  (IMAGE e s) e e' /\
                       (!y. y IN s ==> f(e y) = u + y$3) /\ x IN IMAGE e s)
     ==> lvs_regular atlas W f u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lvs_regular] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) s` THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3`
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set W f u` THEN SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c:(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `y0 IN {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `K = frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) (at y0)` THEN
  SUBGOAL_THEN
   `((SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) has_derivative K) (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = frechet_derivative (\y. lift((f:A->real)(chart_inv c y)))
                           (at (SND(c:(A->bool)#(A->real^3)) x))` THEN
  SUBGOAL_THEN
   `((\y. lift((f:A->real)(chart_inv c y))) has_derivative D)
    (at (SND(c:(A->bool)#(A->real^3)) x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_MESON_TAC[MFDM_CHART];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
                                 (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
      ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((f:A->real)(chart_inv c y))) o
      (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))) has_derivative
     ((D:real^3->real^1) o (K:real^3->real^3))) (at y0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `((\y. lift((f:A->real)(chart_inv c y))) has_derivative D)
                 (at (SND(c:(A->bool)#(A->real^3)) x))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((f:A->real)(chart_inv c y))) o
      (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))) has_derivative
     (\h. lift(h$3))) (at y0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\y:real^3. lift(u + y$3)` THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (SND c ((e:real^3->A) y)) =
                    e y` SUBST1_TAC THENL
       [ASM_MESON_TAC[MFDM_CHART]; ASM_SIMP_TAC[]];
      REWRITE_TAC[LIFT_ADD] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV)
        [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->real^1) o (K:real^3->real^3) = (\h. lift(h$3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(\y. lift((f:A->real)(chart_inv c y))) o
                (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))` THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(D:real^3->real^1) o (K:real^3->real^3) = (\h. lift(h$3))` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 3:real^3`) THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; GSYM DROP_EQ; LIFT_DROP;
           DROP_VEC] THEN
  REAL_ARITH_TAC);;

