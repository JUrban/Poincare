(* ========================================================================= *)
(* Unit pc_p2b_lim (Part 2B): separation, local orientability and the class  *)
(* p2b_ksep pass to geometric limits; monotonicity of canonical              *)
(* neighbourhoods in C.  Main theorems, for the statements of pc_p2b_defs    *)
(* and pc_p3_iface: P2_SEP_LIMIT_STATEMENT, P2B_SEP_LIMIT_VIEW_STATEMENT,    *)
(* P2B_LORIENT_LIMIT_STATEMENT, P2B_LORIENT_LIMIT_VIEW_STATEMENT,            *)
(* P2B_KSEP_LIMIT_STATEMENT, P2B_CANON_MONO_C_STATEMENT.                     *)
(*                                                                           *)
(* First, neck charts shrink radially (power maps of pc_smt_radial) into a   *)
(* relatively compact sub-annulus with the same central sphere, are carried  *)
(* along smooth embeddings, and neck-sphere separation passes from the       *)
(* targets of embeddings of an exhaustion to the source                      *)
(* (P2B_SEP_EMBED_CORE).                                                     *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_smt_radial.ml";;
needs "src/pc_apx_scal.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_p2b_scalpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* L1. Exhaustions: increasing, and compact sets lie in one member.          *)
(* ------------------------------------------------------------------------- *)


let P2B_EXHAUST_MONO = prove
 (`!W:num->A->bool. (!k. W k SUBSET W (SUC k)) ==> !m n. m <= n ==> W m SUBSET W n`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\m n:num. (W:num->A->bool) m SUBSET W n` TRANSITIVE_STEPWISE_LE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[]);;

let P2B_COMPACT_IN_EXHAUST = prove
 (`!top (W:num->A->bool) K.
     (!k. open_in top (W k) /\ W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\ compact_in top K
     ==> ?k. K SUBSET W k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->A->bool) m SUBSET W n` (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `{(W:num->A->bool) k | k IN (:num)}`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?ns. FINITE ns /\ (V:(A->bool)->bool) = IMAGE (W:num->A->bool) ns`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:num->A->bool`; `(:num)`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
    UNDISCH_TAC `(V:(A->bool)->bool) SUBSET {(W:num->A->bool) k | k IN (:num)}` THEN
    REWRITE_TAC[SIMPLE_IMAGE; SUBSET_UNIV] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN ASM_REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(W:num->A->bool) n SUBSET W N` MP_TAC THENL
   [USE_THEN "mono" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* L2. The radial power map with exponent 1/2: a diffeomorphism of the neck *)
(* annulus onto annulus (sqrt(1/2)) (sqrt 2), the identity on the unit      *)
(* sphere, sqrt on the rays.                                                 *)
(* ------------------------------------------------------------------------- *)


let P2B_SHRINK_DIFFEO = prove
 (`mfd_diffeo euclidean (open_set_atlas (:real^3)) (annulus (&1 / &2) (&2))
              euclidean (open_set_atlas (:real^3))
              (annulus (sqrt(&1 / &2)) (sqrt(&2)))
              (\x:real^3. norm x rpow (&1 / &2 - &1) % x)
              (\x. norm x rpow (inv(&1 / &2) - &1) % x)`,
  REWRITE_TAC[MFD_DIFFEO_EUCLIDEAN] THEN
  MP_TAC(SPECL [`&1 / &2`; `&1 / &2`; `&2`]
    (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_POWER_ANNULUS)) THEN
  SIMP_TAC[RPOW_SQRT; REAL_ARITH `&0 <= &1 / &2 /\ &0 <= &2`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC);;

let P2B_SHRINK_NUMS = prove
 (`&1 / &2 < sqrt(&1 / &2) /\ sqrt(&2) < &2 /\
   &1 / &2 < sqrt(&3 / &4) /\ sqrt(&3 / &4) < &1 /\
   &1 < sqrt(&4 / &3) /\ sqrt(&4 / &3) < &2`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let P2B_SHRINK_NUMS2 = prove
 (`sqrt(&1 / &2) < &1 /\ &1 < sqrt(&2)`,
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let P2B_POWER_MAP_RAY = prove
 (`!c. &0 < c
       ==> (\x:real^3. norm x rpow (&1 / &2 - &1) % x) (c % basis 1) = sqrt c % basis 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
  REWRITE_TAC[REAL_ARITH `(&1 / &2 - &1) + &1 = &1 / &2`] THEN
  ASM_SIMP_TAC[RPOW_SQRT; REAL_LT_IMP_LE]);;

let P2B_POWER_MAP_RAY_B = prove
 (`!c. &0 < c
       ==> norm(c % basis 1:real^3) rpow (&1 / &2 - &1) % (c % basis 1:real^3) =
           sqrt c % basis 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `c:real` P2B_POWER_MAP_RAY) THEN
  ASM_REWRITE_TAC[]);;

let P2B_POWER_MAP_SPHERE = prove
 (`!x:real^3. norm x = &1 ==> (\x:real^3. norm x rpow (&1 / &2 - &1) % x) x = x`,
  SIMP_TAC[RPOW_ONE; VECTOR_MUL_LID]);;

let P2B_POWER_MAP_SPHERE_IMAGE = prove
 (`IMAGE (\x:real^3. norm x rpow (&1 / &2 - &1) % x) (sphere(vec 0,&1)) = sphere(vec 0,&1)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `y:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[RPOW_ONE; VECTOR_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[RPOW_ONE; VECTOR_MUL_LID]]);;

let P2B_NORM_RAY = prove
 (`!c. &0 < c ==> norm(c % basis 1:real^3) = c`,
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* L3. Neck charts: basic facts, the shrunk chart, compactness of its image, *)
(* the two sides of the central sphere, transport along embeddings.         *)
(* ------------------------------------------------------------------------- *)


let P2B_EUCLIDEAN_ATLAS3 = prove
 (`smooth_manifold_atlas euclidean (open_set_atlas (:real^3))`,
  MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let P2B_NECK_SHRINK = prove
 (`!top atlas (e:real^3->A).
     smooth_manifold_atlas top atlas /\ mfd_neck_chart top atlas e
     ==> mfd_neck_chart top atlas (e o (\x. norm x rpow (&1 / &2 - &1) % x)) /\
         IMAGE (e o (\x. norm x rpow (&1 / &2 - &1) % x)) (annulus (&1 / &2) (&2)) =
         IMAGE e (annulus (sqrt(&1 / &2)) (sqrt(&2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart; mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `e':A->real^3`)) THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. norm x rpow (&1 / &2 - &1) % x) (annulus (&1 / &2) (&2)) =
                annulus (sqrt(&1 / &2)) (sqrt(&2))` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MFD_DIFFEO_MAPS P2B_SHRINK_DIFFEO) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:real^3->A) o (\x. norm x rpow (&1 / &2 - &1) % x))
                      (annulus (&1 / &2) (&2)) =
                IMAGE e (annulus (sqrt(&1 / &2)) (sqrt(&2)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `annulus (sqrt(&1 / &2)) (sqrt(&2)) SUBSET (annulus (&1 / &2) (&2):real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN MP_TAC P2B_SHRINK_NUMS THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `annulus (&1 / &2) (&2):real^3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`;
                 `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))`; `e:real^3->A`; `e':A->real^3`;
                 `annulus (sqrt(&1 / &2)) (sqrt(&2)):real^3->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_ANNULUS] THEN DISCH_TAC THEN
  EXISTS_TAC `((\x:real^3. norm x rpow (inv(&1 / &2) - &1) % x) o (e':A->real^3))` THEN
  MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
  EXISTS_TAC `euclidean:(real^3)topology` THEN EXISTS_TAC `open_set_atlas (:real^3)` THEN
  EXISTS_TAC `annulus (sqrt(&1 / &2)) (sqrt(&2)):real^3->bool` THEN
  ASM_REWRITE_TAC[P2B_EUCLIDEAN_ATLAS3; P2B_SHRINK_DIFFEO]);;

let P2B_NECK_CHART_BASICS = prove
 (`!top atlas (e:real^3->A).
     mfd_neck_chart top atlas e
     ==> continuous_map (subtopology euclidean (annulus (&1 / &2) (&2)),top) e /\
         (!y z. y IN annulus (&1 / &2) (&2) /\ z IN annulus (&1 / &2) (&2) /\ e y = e z
                ==> y = z) /\
         IMAGE e (annulus (&1 / &2) (&2)) SUBSET topspace top /\
         open_in top (IMAGE e (annulus (&1 / &2) (&2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart; mfd_param] THEN
  DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_diffeo]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map
       (subtopology euclidean (annulus (&1 / &2) (&2)),top) (e:real^3->A)` THEN
    REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[OPEN_IN_SUBSET]]);;

let P2B_NECK_SHRINK_COMPACT = prove
 (`!top atlas (e:real^3->A).
     mfd_neck_chart top atlas e
     ==> ?K. compact_in top K /\ IMAGE e (annulus (sqrt(&1 / &2)) (sqrt(&2))) SUBSET K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_NECK_CHART_BASICS) THEN
  EXISTS_TAC `IMAGE (e:real^3->A) {y:real^3 | sqrt(&1 / &2) <= norm y /\ norm y <= sqrt(&2)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `sqrt(&2)` THEN SIMP_TAC[];
        SUBGOAL_THEN `{y:real^3 | sqrt(&1 / &2) <= norm y /\ norm y <= sqrt(&2)} =
                      cball(vec 0,sqrt(&2)) DIFF ball(vec 0,sqrt(&1 / &2))`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
          REAL_ARITH_TAC;
          SIMP_TAC[CLOSED_DIFF; CLOSED_CBALL; OPEN_BALL]]];
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN MP_TAC P2B_SHRINK_NUMS THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; annulus; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]]);;

let P2B_NECK_SIDE_PATH = prove
 (`!top atlas (e:real^3->A) r1 r2 y1 y2.
     mfd_neck_chart top atlas e /\
     (annulus r1 r2:real^3->bool) SUBSET annulus (&1 / &2) (&2) /\
     DISJOINT (annulus r1 r2:real^3->bool) (sphere(vec 0,&1)) /\
     y1 IN annulus r1 r2 /\ y2 IN annulus r1 r2
     ==> path_component_of
           (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) (e y1) (e y2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_NECK_CHART_BASICS) THEN
  SUBGOAL_THEN `sphere(vec 0,&1) SUBSET (annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (annulus r1 r2:real^3->bool),
                    subtopology top (topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))))
                   e`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `subtopology euclidean (annulus r1 r2:real^3->bool) =
                    subtopology (subtopology euclidean (annulus (&1 / &2) (&2)))
                                (annulus r1 r2)` SUBST1_TAC THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_connected_in
      (subtopology top (topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))))
      (IMAGE e (annulus r1 r2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (annulus r1 r2:real^3->bool)` THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; PATH_CONNECTED_IN_EUCLIDEAN] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`] (CONJUNCT1 PATH_CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[annulus];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(e:real^3->A) y1` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] PATH_COMPONENT_OF_MAXIMAL)) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `(e:real^3->A) y2`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN]]);;

let P2B_NECK_CHART_TRANSPORT = prove
 (`!top atlas top' atlas' (e:real^3->B) W (phi:B->A) psi.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_neck_chart top atlas e /\
     mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\
     IMAGE e (annulus (&1 / &2) (&2)) SUBSET W
     ==> mfd_neck_chart top' atlas' (phi o e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart; mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `e':B->real^3`) STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->B) (annulus (&1 / &2) (&2)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `W:B->bool`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `IMAGE (phi:B->A) W`; `phi:B->A`; `psi:A->B`;
                 `IMAGE (e:real^3->B) (annulus (&1 / &2) (&2))`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(e':B->real^3) o (psi:A->B)` THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`; `:B`,`:B`; `:A`,`:C`; `:3`,`:M`; `:3`,`:N`; `:3`,`:P`]
                 MFD_DIFFEO_COMPOSE) THEN
  EXISTS_TAC `top:B topology` THEN EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN
  EXISTS_TAC `IMAGE (e:real^3->B) (annulus (&1 / &2) (&2))` THEN
  ASM_REWRITE_TAC[P2B_EUCLIDEAN_ATLAS3]);;

let P2B_PATH_TRANSPORT = prove
 (`!top atlas top' atlas' W (phi:B->A) psi S (g:real->B).
     mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) W top'
                (atlas':((A->bool)#(A->real^3))->bool) (IMAGE phi W) phi psi /\
     S SUBSET W /\
     path_in (subtopology top (topspace top DIFF S)) g /\
     IMAGE g (real_interval[&0,&1]) SUBSET W
     ==> path_component_of (subtopology top' (topspace top' DIFF IMAGE phi S))
                           (phi(g(&0))) (phi(g(&1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_component_of] THEN
  EXISTS_TAC `(phi:B->A) o (g:real->B)` THEN REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top' (IMAGE (phi:B->A) W)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  UNDISCH_TAC `path_in (subtopology top (topspace top DIFF S)) (g:real->B)` THEN
  REWRITE_TAC[path_in; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (W:B->bool)` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; o_THM] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real->B) t IN W /\ ~(g t IN S)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':A topology`; `IMAGE (phi:B->A) W`] OPEN_IN_SUBSET) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `s:B` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(g:real->B) t = s` (fun th -> ASM_MESON_TAC[th]) THEN
      SUBGOAL_THEN `(psi:A->B)((phi:B->A)((g:real->B) t)) = g t /\ psi(phi s) = s`
      MP_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]]]);;

let P2B_PATH_IMP_CONNECTED_COMPONENT = prove
 (`!top x y:A. path_component_of top x y ==> connected_component_of top x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `x:A`] PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT_OF) THEN
  REWRITE_TAC[SUBSET; IN] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* L4. The core: if an exhaustion W k of a Hausdorff 3-manifold embeds into *)
(* 3-manifolds whose neck spheres separate, its neck spheres separate.  A   *)
(* path joining the two sides would lie, together with the image of the    *)
(* shrunk neck chart, in one W k and map to a path in the target.           *)
(* ------------------------------------------------------------------------- *)


let P2B_SEP_EMBED_CORE = prove
 (`!top atlas (W:num->B->bool) (phi:num->B->A) (top':num->A topology) atlas'.
     hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     (!k. open_in top (W k) /\ W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\
     (!k. smooth_manifold_atlas (top' k) (atlas' k:((A->bool)#(A->real^3))->bool) /\
          apx_sphere_sep (top' k) (atlas' k) /\
          ?psi. mfd_diffeo top atlas (W k) (top' k) (atlas' k) (IMAGE (phi k) (W k)) (phi k) psi)
     ==> apx_sphere_sep top atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tgt"))))) THEN
  REWRITE_TAC[apx_sphere_sep] THEN X_GEN_TAC `e:real^3->B` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_NECK_CHART_BASICS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "intop") (LABEL_TAC "openim")))) THEN
  ABBREV_TAC `S = IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1 / &2) (&2) /\ ~(norm y = &1)
                ==> (e:real^3->B) y IN topspace top DIFF S` (LABEL_TAC "off") THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [USE_THEN "intop" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) = z` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. &1 / &2 < c /\ c < &2 /\ ~(c = &1)
                ==> (e:real^3->B)(c % basis 1) IN topspace top DIFF S` (LABEL_TAC "offr") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "off" MATCH_MP_TAC THEN
    SUBGOAL_THEN `norm(c % basis 1:real^3) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC P2B_NORM_RAY THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `norm(c % basis 1:real^3) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC P2B_NORM_RAY THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN
  CONJ_TAC THENL
   [USE_THEN "offr" MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "offr" MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `closed_in top (S:B->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE] THEN
    REWRITE_TAC[SUBSET; annulus; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_path_connected_space (subtopology top (topspace top DIFF (S:B->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_PATH_CONNECTED_SPACE_OPEN_SUBSET THEN CONJ_TAC THENL
     [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED];
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  ABBREV_TAC `X = subtopology top (topspace top DIFF (S:B->bool))` THEN
  SUBGOAL_THEN `path_component_of X ((e:real^3->B)(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:B topology`; `(e:real^3->B)(&3 / &4 % basis 1)`]
                  PATH_COMPONENT_EQ_CONNECTED_COMPONENT_OF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `e:real^3->B`]
                P2B_NECK_SHRINK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `e:real^3->B`]
                P2B_NECK_SHRINK_COMPACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC P2B_SHRINK_NUMS THEN MP_TAC P2B_SHRINK_NUMS2 THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(sqrt(&3 / &4) % basis 1:real^3) = sqrt(&3 / &4) /\
                norm(&3 / &4 % basis 1:real^3) = &3 / &4 /\
                norm(&4 / &3 % basis 1:real^3) = &4 / &3 /\
                norm(sqrt(&4 / &3) % basis 1:real^3) = sqrt(&4 / &3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC P2B_NORM_RAY THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `path_component_of X ((e:real^3->B)(sqrt(&3 / &4) % basis 1))
                                    (e(&3 / &4 % basis 1))` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN EXPAND_TAC "S" THEN MATCH_MP_TAC P2B_NECK_SIDE_PATH THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `&1 / &2`; `&1`] THEN
    ASM_REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER;
                    IN_SPHERE_0; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN TRY GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_component_of X ((e:real^3->B)(&4 / &3 % basis 1))
                                    (e(sqrt(&4 / &3) % basis 1))` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN EXPAND_TAC "S" THEN MATCH_MP_TAC P2B_NECK_SIDE_PATH THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `&1`; `&2`] THEN
    ASM_REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER;
                    IN_SPHERE_0; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN TRY GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_component_of X ((e:real^3->B)(sqrt(&3 / &4) % basis 1))
                                    (e(sqrt(&4 / &3) % basis 1))` MP_TAC THENL
   [ASM_MESON_TAC[PATH_COMPONENT_OF_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[path_component_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (IMAGE (g:real->B) (real_interval[&0,&1])) /\
                IMAGE g (real_interval[&0,&1]) SUBSET topspace top DIFF S`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:B topology`; `g:real->B`] COMPACT_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `W:num->B->bool`;
                 `K0 UNION IMAGE (g:real->B) (real_interval[&0,&1])`] P2B_COMPACT_IN_EXHAUST) THEN
  ASM_SIMP_TAC[COMPACT_IN_UNION; UNION_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "tgt" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sepk")
    (X_CHOOSE_TAC `psi:A->B`))) THEN
  ABBREV_TAC `e2 = (e:real^3->B) o (\x. norm x rpow (&1 / &2 - &1) % x)` THEN
  SUBGOAL_THEN `(S:B->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K0:B->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->B) (annulus (sqrt(&1 / &2)) (sqrt(&2)))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart (top' (k:num)) (atlas' k) ((phi:num->B->A) k o (e2:real^3->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_NECK_CHART_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `(W:num->B->bool) k`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "e2" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K0:B->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "sepk" (MP_TAC o SPEC `(phi:num->B->A) k o (e2:real^3->B)` o
                   REWRITE_RULE[apx_sphere_sep]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A) k o (e2:real^3->B)) (sphere(vec 0,&1)) = IMAGE (phi k) S /\
                ((phi:num->B->A) k o (e2:real^3->B)) (&3 / &4 % basis 1) =
                phi k ((e:real^3->B)(sqrt(&3 / &4) % basis 1)) /\
                ((phi:num->B->A) k o (e2:real^3->B)) (&4 / &3 % basis 1) =
                phi k ((e:real^3->B)(sqrt(&4 / &3) % basis 1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "e2" THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IMAGE_o; P2B_POWER_MAP_SPHERE_IMAGE; o_THM] THEN
    SIMP_TAC[P2B_POWER_MAP_RAY_B; REAL_ARITH `&0 < &3 / &4 /\ &0 < &4 / &3`];
    ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC P2B_PATH_IMP_CONNECTED_COMPONENT THEN
  SUBGOAL_THEN `(phi:num->B->A) k ((e:real^3->B)(sqrt(&3 / &4) % basis 1)) =
                phi k ((g:real->B)(&0)) /\
                (phi:num->B->A) k ((e:real^3->B)(sqrt(&4 / &3) % basis 1)) =
                phi k ((g:real->B)(&1))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2B_PATH_TRANSPORT THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `atlas' (k:num):((A->bool)#(A->real^3))->bool`;
                        `(W:num->B->bool) k`; `psi:A->B`] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `path_in X (g:real->B)` THEN EXPAND_TAC "X" THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* Geometric limits.  The exhaustion and the time-0 embeddings of a flow     *)
(* limit, slices of histories and of regular views at the base times are     *)
(* smooth, and P2_SEP_LIMIT (histories) and P2B_SEP_LIMIT_VIEW               *)
(* (regular views).                                                          *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

let P2B_FLOW_LIMIT_EXHAUST = prove
 (`!V x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t Q (top,atlas) g xl Tl
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
         ?W phi. (!k. open_in top (W k) /\ W k SUBSET W (SUC k) /\ xl IN W k) /\
                 UNIONS {W k | k IN (:num)} = topspace top /\
                 (!k. phi k xl = x k) /\
                 (!k. ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (t k))
                                       (rfs_vatlas (V k) (t k)) (IMAGE (phi k) (W k))
                                       (phi k) psi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `&0`] o
      check (fun th -> can (term_match [] `!k:num s:real. P k s`) (concl th))) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      check (fun th -> can (term_match [] `!k:num. &0 < ts k /\ Q k`) (concl th))) THEN
    REAL_ARITH_TAC]);;

let P2B_SEP_FROM_FLOW_LIMIT = prove
 (`!V x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t Q (top,atlas) g xl Tl /\
     (!k. smooth_manifold_atlas (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)) /\
          apx_sphere_sep (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)))
     ==> apx_sphere_sep top atlas`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2B_FLOW_LIMIT_EXHAUST) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
      (X_CHOOSE_THEN `phi:num->B->A` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC P2B_SEP_EMBED_CORE THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`;
                        `\k. rfs_vtop ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (t k)`;
                        `\k. rfs_vatlas ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (t k)`] THEN
  ASM_REWRITE_TAC[]);;

let P2B_HS_SLICE_SMOOTH = prove
 (`!hs:(A)rfs_history t x.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs t)
     ==> rfs_live hs t /\
         hausdorff_space (rfs_top_at hs t) /\
         smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `rfs_live (hs:(A)rfs_history) t` THENL
   [ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_live; rfs_horizon]; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
    REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) t` o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `(x:A) IN topspace(rfs_top_at hs t)` THEN
    ASM_REWRITE_TAC[rfs_top_at; TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]]);;

(* P2_SEP_LIMIT (the Part 3 statement, pc_p3_iface) and its view form.     *)

let P2B_SEP_LIMIT = prove
 (`!(u:A->bool) (w:B->bool). P2_SEP_LIMIT_STATEMENT u w`,
  REWRITE_TAC[P2_SEP_LIMIT_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2B_SEP_FROM_FLOW_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`\n. rfs_view ((hs:num->(A)rfs_history) n)`;
                        `x:num->A`; `t:num->real`; `Q:num->real`;
                        `g:real->B->real^3^3`; `xl:B`; `Tl:real`] THEN
  ASM_REWRITE_TAC[P2B_RFS_VIEW_PARTS] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) k`; `(t:num->real) k`; `(x:num->A) k`]
                P2B_HS_SLICE_SMOOTH) THEN
  ASM_SIMP_TAC[P2B_HS_SEP_SLICES]);;

let P2B_FLOW_LIMIT_BASE_SLICE = prove
 (`!V x t Q (top:B topology) atlas g xl Tl k.
     p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t Q (top,atlas) g xl Tl
     ==> x k IN topspace(rfs_vtop (V k) (t k))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2B_FLOW_LIMIT_EXHAUST) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
      (X_CHOOSE_THEN `phi:num->B->A` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `k:num` o
    check (fun th -> can (term_match [] `!k:num. ?psi:A->B. P k psi`) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[mfd_diffeo]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:num->A) k = (phi:num->B->A) k xl` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2B_SEP_LIMIT_VIEW = prove
 (`!(u:A->bool) (w:B->bool). P2B_SEP_LIMIT_VIEW_STATEMENT u w`,
  REWRITE_TAC[P2B_SEP_LIMIT_VIEW_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2B_SEP_FROM_FLOW_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)`;
                        `x:num->A`; `t:num->real`; `Q:num->real`;
                        `g:real->B->real^3^3`; `xl:B`; `Tl:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2c_regular_view ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)` THEN
  REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->real) k` o CONJUNCT1) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
  MATCH_MP_TAC P2B_FLOW_LIMIT_BASE_SLICE THEN
  MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
                        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                        `xl:B`; `Tl:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Canonical neighbourhoods are monotone in C on genuine slices              *)
(* (P2B_CANON_MONO_C).  Caps: the scalar curvature is bounded on U by the    *)
(* ratio clause and positive, so sup R > 0.  C-components: positive          *)
(* sectional curvature gives positive scalar curvature (in an orthonormal    *)
(* frame R is the sum of the sectional curvatures of the coordinate planes,  *)
(* P2B_LSCALAR_POS_SECT of the unit pc_p2b_scalpos), and R is bounded on the *)
(* compact component.                                                        *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

let P2B_CAP_CORE_SUBSET = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> Y SUBSET U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN STRIP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let P2B_RFS_SUP_LT_MONO = prove
 (`!S c c'. rfs_sup_lt S c /\ c <= c' ==> rfs_sup_lt S c'`,
  REWRITE_TAC[rfs_sup_lt] THEN MESON_TAC[REAL_LTE_TRANS]);;

let P2B_RFS_INF_GT_MONO = prove
 (`!S c c'. rfs_inf_gt S c /\ c' <= c ==> rfs_inf_gt S c'`,
  REWRITE_TAC[rfs_inf_gt] THEN MESON_TAC[REAL_LET_TRANS]);;

let P2B_CAP_RATIO = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y
     ==> (!y. y IN U ==> &0 < mfd_scalar atlas g y) /\
         ?d. d < C /\
             !y1 y2. y1 IN U /\ y2 IN U
                     ==> mfd_scalar atlas g y2 / mfd_scalar atlas g y1 <= d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[]);;

let P2B_CAP_SUP_POS = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x.
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> (?b. !z. z IN IMAGE (mfd_scalar atlas g) U ==> z <= b) /\
         &0 < sup(IMAGE (mfd_scalar atlas g) U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
  SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2B_CAP_RATIO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?b. !z. z IN IMAGE (mfd_scalar atlas (g:A->real^3^3)) U ==> z <= b`
  ASSUME_TAC THENL
   [EXISTS_TAC `d * mfd_scalar atlas (g:A->real^3^3) x` THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) x` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let P2B_RFS_CAP_MONO_C = prove
 (`!top atlas (g:A->real^3^3) C C' eps U Y x.
     &1 < C /\ C <= C' /\ rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> rfs_cap (top,atlas) g C' eps U Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`] P2B_CAP_SUP_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)))` THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
  ASM_REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "diam") (CONJUNCTS_THEN2 (LABEL_TAC "ratio")
    (CONJUNCTS_THEN2 (LABEL_TAC "vol") (CONJUNCTS_THEN2 (LABEL_TAC "dcl")
    (CONJUNCTS_THEN2 (LABEL_TAC "gr1") (LABEL_TAC "gr2")))))))))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C * k:real` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL];
    MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
    USE_THEN "vol" (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)) pow 3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    USE_THEN "dcl" (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]]);;

let P2B_C_COMPONENT_SCALAR = prove
 (`!top atlas (g:A->real^3^3) C U x.
     riemannian_metric atlas g /\ rfs_c_component (top,atlas) g C U /\ x IN U
     ==> (!y. y IN U ==> &0 < mfd_scalar atlas g y) /\
         (?b. !z. z IN IMAGE (mfd_scalar atlas g) U ==> z <= b) /\
         &0 < sup(IMAGE (mfd_scalar atlas g) U) /\
         &0 <= inf(IMAGE (mfd_scalar atlas g) U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                U IN connected_components_of top /\ compact_in top U /\
                (!y u v. y IN U /\ ~collinear {vec 0,u,v}
                         ==> &0 < mfd_sectional atlas (g:A->real^3^3) y u v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN U ==> &0 < mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b. !z. z IN IMAGE (mfd_scalar atlas (g:A->real^3^3)) U ==> z <= b`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `real_bounded (IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS];
      REWRITE_TAC[real_bounded] THEN MESON_TAC[REAL_ARITH `abs z <= b ==> z <= b`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) x` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    MATCH_MP_TAC REAL_LE_INF THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; REAL_LT_IMP_LE] THEN ASM SET_TAC[]]);;

let P2B_RFS_C_COMPONENT_MONO_C = prove
 (`!top atlas (g:A->real^3^3) C C' U x.
     &1 < C /\ C <= C' /\ riemannian_metric atlas g /\
     rfs_c_component (top,atlas) g C U /\ x IN U
     ==> rfs_c_component (top,atlas) g C' U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `U:A->bool`; `x:A`] P2B_C_COMPONENT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S0 = sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  ABBREV_TAC `I0 = inf(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `&0 <= inv(sqrt S0) /\ &0 <= inv(sqrt I0) /\ inv C' <= inv C`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
  ASM_REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dlo") (CONJUNCTS_THEN2 (LABEL_TAC "dhi")
    (CONJUNCTS_THEN2 (LABEL_TAC "gr1") (LABEL_TAC "gr2")))))))))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2B_RFS_INF_GT_MONO THEN EXISTS_TAC `inv C * S0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C * inv(sqrt S0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `C * inv(sqrt I0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B_RFS_SUP_LT_MONO THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]]);;

let P2B_CANON_MONO_C = prove
 (`!u:A->bool. P2B_CANON_MONO_C_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_CANON_MONO_C_STATEMENT; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `C':real`; `eps:real`; `x:A`;
                       `t:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; p3_canon_at; rfs_strong_canonical] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN
   `!U Y. rfs_cap ((TM:real->A topology) t,AT t) (G t) C eps U Y /\ (x:A) IN Y
          ==> rfs_cap (TM t,AT t) (G t) C' eps U Y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U. (x:A) IN U /\ rfs_c_component ((TM:real->A topology) t,AT t) (G t) C U
        ==> rfs_c_component (TM t,AT t) (G t) C' U` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_RFS_C_COMPONENT_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* Local orientability passes to geometric limits (P2B_LORIENT_LIMIT,        *)
(* P2B_LORIENT_LIMIT_VIEW) and the class of kappa-solutions with separating  *)
(* necks and local orientability is closed under eventual limits             *)
(* (P2B_KSEP_LIMIT).  Route: an open subset of the limit with compact        *)
(* closure lies in one exhaustion set W k, which is diffeomorphic to an open *)
(* subset of a stage; the oriented atlas of the stage, pulled back along the *)
(* diffeomorphism and joined to the limit's atlas, is a smooth oriented      *)
(* atlas on the subset (P2B_ORIENTABLE_EMBED).                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Atlases: identity maps between an atlas and a union, pullback charts. *)

let P2B_SMOOTH_MAP_ID_UNION = prove
 (`!top (A:((X->bool)#(X->real^N))->bool) B W.
     smooth_manifold_atlas top (A UNION B)
     ==> mfd_smooth_map A (A UNION B) W (\x. x) /\
         mfd_smooth_map (A UNION B) A W (\x. x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM] THEN
  CONJ_TAC THEN
  (MAP_EVERY X_GEN_TAC [`U:X->bool`; `phi:X->real^N`; `V:X->bool`; `psi:X->real^N`] THEN
   STRIP_TAC THEN REWRITE_TAC[FST; SND] THEN
   MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
   EXISTS_TAC `IMAGE (phi:X->real^N) (U INTER V)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(\y:real^N. psi(chart_inv (U:X->bool,phi) y):real^N) =
                 psi o (\x:X. x) o chart_inv (U,phi)` (SUBST1_TAC o SYM) THENL
    [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
   MP_TAC(ISPECL [`top:X topology`; `A UNION B:((X->bool)#(X->real^N))->bool`;
                  `U:X->bool`; `phi:X->real^N`; `V:X->bool`; `psi:X->real^N`]
                 CHART_TRANS_SMOOTH) THEN
   ASM_REWRITE_TAC[IN_UNION; chart_trans; SND]));;

let P2B_DIFFEO_ATLAS_UNION = prove
 (`!top atlas X top' atlas' O V (phi:A->B) psi.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
     smooth_manifold_atlas top' (atlas' UNION O) /\
     mfd_diffeo top atlas X top' atlas' V phi psi
     ==> mfd_diffeo top atlas X top' (atlas' UNION O) V phi psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `O:((B->bool)#(B->real^N))->bool`; `V:B->bool`] P2B_SMOOTH_MAP_ID_UNION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) X top' (atlas':((B->bool)#(B->real^N))->bool) V (phi:A->B) psi` THEN
  REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(phi:A->B) = (\x:B. x) o phi` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`;
                          `atlas':((B->bool)#(B->real^N))->bool`; `top':B topology`;
                          `V:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID];
    SUBGOAL_THEN `(psi:B->A) = psi o (\x:B. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `top':B topology`;
                          `atlas':((B->bool)#(B->real^N))->bool`; `top:A topology`;
                          `V:B->bool`] THEN
    ASM_REWRITE_TAC[IMAGE_ID; SUBSET_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID]]);;

let P2B_PULLBACK_CHART = prove
 (`!top atlas X top' O V (phi:A->B) psi D (f:B->real^N).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' O /\ (D,f) IN O /\
     mfd_diffeo top atlas X top' O V phi psi
     ==> open_in (subtopology top X) {y | y IN X /\ phi y IN D} /\
         IMAGE (f o phi) {y | y IN X /\ phi y IN D} = IMAGE f (D INTER V) /\
         open (IMAGE f (D INTER V)) /\
         homeomorphic_map (subtopology (subtopology top X) {y | y IN X /\ phi y IN D},
                           subtopology euclidean (IMAGE f (D INTER V))) (f o phi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MP_TAC(ISPECL [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `D:B->bool`;
                 `f:B->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET topspace top /\ (V:B->bool) SUBSET topspace top' /\
                (D:B->bool) SUBSET topspace top'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:A->B) {y | y IN X /\ phi y IN D} = D INTER V` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (phi:A->B) X = V` THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`phi:A->B`; `subtopology top (X:A->bool)`; `top':B topology`;
                   `D:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN UNDISCH_TAC `(X:A->bool) SUBSET topspace top` THEN SET_TAC[];
    ASM_REWRITE_TAC[IMAGE_o];
    MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`;
                          `D:B->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top' (D INTER V:B->bool)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `subtopology top' (D INTER V:B->bool) =
                    subtopology (subtopology top' V) (D INTER V)` SUBST1_TAC THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP]; ALL_TAC] THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC `IMAGE (phi:A->B) {y | y IN X /\ phi y IN D} = D INTER V` THEN
      UNDISCH_TAC `(X:A->bool) SUBSET topspace top` THEN
      UNDISCH_TAC `(V:B->bool) SUBSET topspace top'` THEN SET_TAC[];
      SUBGOAL_THEN
       `subtopology top' (D INTER V:B->bool) = subtopology (subtopology top' D) (D INTER V) /\
        subtopology euclidean (IMAGE (f:B->real^N) (D INTER V)) =
        subtopology (subtopology euclidean (IMAGE f D)) (IMAGE f (D INTER V))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THEN AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN
      UNDISCH_TAC `(D:B->bool) SUBSET topspace top'` THEN SET_TAC[]]]);;

let P2B_PULLBACK_COMPAT_PP = prove
 (`!top atlas X top' O V (phi:A->B) psi D1 (f1:B->real^N) D2 f2.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' O /\ mfd_diffeo top atlas X top' O V phi psi /\
     (D1,f1) IN O /\ (D2,f2) IN O
     ==> ?g. smooth_map_on (IMAGE (f1 o phi) ({y | y IN X /\ phi y IN D1} INTER
                                              {y | y IN X /\ phi y IN D2})) g /\
             !y. y IN {y | y IN X /\ phi y IN D1} INTER {y | y IN X /\ phi y IN D2}
                 ==> g((f1 o phi) y) = (f2 o phi) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`D1:B->bool`; `f1:B->real^N`; `D2:B->bool`; `f2:B->real^N`] o
    CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [smooth_manifold_atlas] o
    check (fun th -> concl th = `smooth_manifold_atlas (top':B topology)
                                   (O:((B->bool)#(B->real^N))->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real^N->real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f1:B->real^N) (D1 INTER D2)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]);;

let P2B_PULLBACK_COMPAT_RP = prove
 (`!top atlas X top' O V (phi:A->B) psi U (h:A->real^N) D (f:B->real^N).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' O /\ mfd_diffeo top atlas X top' O V phi psi /\
     (U,h) IN atlas /\ (D,f) IN O
     ==> ?g. smooth_map_on (IMAGE h ((U INTER X) INTER {y | y IN X /\ phi y IN D})) g /\
             !y. y IN (U INTER X) INTER {y | y IN X /\ phi y IN D}
                 ==> g(h y) = (f o phi) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `(f:B->real^N) o (phi:A->B) o chart_inv (U:A->bool,h:A->real^N)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) X top'
                  (O:((B->bool)#(B->real^N))->bool) V (phi:A->B) psi` THEN
    REWRITE_TAC[mfd_diffeo; mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`(U:A->bool,h:A->real^N)`; `(D:B->bool,f:B->real^N)`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN SET_TAC[];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `h:A->real^N`] CHART_INV) THEN ASM_SIMP_TAC[]]);;

let P2B_PULLBACK_COMPAT_PR = prove
 (`!top atlas X top' O V (phi:A->B) psi U (h:A->real^N) D (f:B->real^N).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' O /\ mfd_diffeo top atlas X top' O V phi psi /\
     (U,h) IN atlas /\ (D,f) IN O
     ==> ?g. smooth_map_on (IMAGE (f o phi) ({y | y IN X /\ phi y IN D} INTER (U INTER X))) g /\
             !y. y IN {y | y IN X /\ phi y IN D} INTER (U INTER X)
                 ==> g((f o phi) y) = h y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  EXISTS_TAC `(h:A->real^N) o (psi:B->A) o chart_inv (D:B->bool,f:B->real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (f:B->real^N) {z | z IN D INTER V /\ (psi:B->A) z IN U}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) X top'
                    (O:((B->bool)#(B->real^N))->bool) V (phi:A->B) psi` THEN
      REWRITE_TAC[mfd_diffeo; mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`(D:B->bool,f:B->real^N)`; `(U:A->bool,h:A->real^N)`] o
                 CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[FST; SND]];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `D:B->bool`;
                   `f:B->real^N`] CHART_INV) THEN ASM_SIMP_TAC[]]);;

let P2B_SMOOTH_ATLAS_UNION = prove
 (`!top (A:((X->bool)#(X->real^N))->bool) B.
     smooth_manifold_atlas top A /\ smooth_manifold_atlas top B /\
     (!U phi V psi. (U,phi) IN A /\ (V,psi) IN B
                    ==> (?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
                             !x. x IN U INTER V ==> g(phi x) = psi x) /\
                        (?g. smooth_map_on (IMAGE psi (V INTER U)) g /\
                             !x. x IN V INTER U ==> g(psi x) = phi x))
     ==> smooth_manifold_atlas top (A UNION B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_manifold_atlas; IN_UNION] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`U:X->bool`; `phi:X->real^N`; `V:X->bool`; `psi:X->real^N`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let P2B_IN_PULLBACK_ATLAS = prove
 (`!(O:((B->bool)#(B->real^N))->bool) X (phi:A->B) W k.
     (W,k) IN IMAGE (\c. ({y | y IN X /\ phi y IN FST c},SND c o phi)) O <=>
     ?D f. (D,f) IN O /\ W = {y | y IN X /\ phi y IN D} /\ k = f o phi`,
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let P2B_PULLBACK_SMOOTH_ATLAS = prove
 (`!top atlas X top' O V (phi:A->B) psi.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (O:((B->bool)#(B->real^N))->bool) /\
     mfd_diffeo top atlas X top' O V phi psi
     ==> smooth_manifold_atlas (subtopology top X)
           (IMAGE (\c. ({y | y IN X /\ phi y IN FST c},SND c o phi)) O) /\
         smooth_manifold_atlas (subtopology top X)
           (restrict_atlas atlas X UNION
            IMAGE (\c. ({y | y IN X /\ phi y IN FST c},SND c o phi)) O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (X:A->bool) /\ open_in top' (V:B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->bool`]
                SMOOTH_MANIFOLD_ATLAS_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `P = IMAGE (\c. ({y | y IN X /\ (phi:A->B) y IN FST c},SND c o phi))
                        (O:((B->bool)#(B->real^N))->bool)` THEN
  SUBGOAL_THEN
   `!W k. (W,k) IN P
          ==> open_in (subtopology top X) W /\ open (IMAGE (k:A->real^N) W) /\
              homeomorphic_map (subtopology (subtopology top X) W,
                                subtopology euclidean (IMAGE k W)) k`
  (LABEL_TAC "pch") THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `D:B->bool` (X_CHOOSE_THEN `f:B->real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->bool`;
                   `top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `V:B->bool`;
                   `phi:A->B`; `psi:B->A`; `D:B->bool`; `f:B->real^N`] P2B_PULLBACK_CHART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN topspace(subtopology top X) ==> ?W k. (W,k) IN (P:((A->bool)#(A->real^N))->bool) /\ x IN W`
  (LABEL_TAC "pcov") THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:A->B) x IN topspace top'` MP_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `V:B->bool`] OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->B) x` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [smooth_manifold_atlas] o
      check (fun th -> concl th = `smooth_manifold_atlas (top':B topology)
                                     (O:((B->bool)#(B->real^N))->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:B->bool` (X_CHOOSE_THEN `f:B->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`{y | y IN X /\ (phi:A->B) y IN D}`; `(f:B->real^N) o (phi:A->B)`] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`D:B->bool`; `f:B->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
SUBGOAL_THEN `smooth_manifold_atlas (subtopology top X) (P:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[smooth_manifold_atlas] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "pch" ACCEPT_TAC;
      USE_THEN "pcov" ACCEPT_TAC;
      EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS] THEN
      MAP_EVERY X_GEN_TAC [`U1:A->bool`; `k1:A->real^N`; `U2:A->bool`; `k2:A->real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `D1:B->bool` (X_CHOOSE_THEN `f1:B->real^N` STRIP_ASSUME_TAC))
        (X_CHOOSE_THEN `D2:B->bool` (X_CHOOSE_THEN `f2:B->real^N` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B_PULLBACK_COMPAT_PP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `top':B topology`; `O:((B->bool)#(B->real^N))->bool`;
                            `V:B->bool`; `psi:B->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B_SMOOTH_ATLAS_UNION THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `h:A->real^N`; `W:A->bool`; `k:A->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U0:A->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `D:B->bool` (X_CHOOSE_THEN `f:B->real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2B_PULLBACK_COMPAT_RP;
    MATCH_MP_TAC P2B_PULLBACK_COMPAT_PR] THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `top':B topology`; `O:((B->bool)#(B->real^N))->bool`;
                        `V:B->bool`; `psi:B->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2B_PULLBACK_ORIENTED = prove
 (`!top atlas X top' O V (phi:A->B) psi.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (O:((B->bool)#(B->real^N))->bool) /\
     mfd_oriented_atlas O /\ mfd_diffeo top atlas X top' O V phi psi
     ==> mfd_oriented_atlas (IMAGE (\c. ({y | y IN X /\ phi y IN FST c},SND c o phi)) O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->bool`;
                 `top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `V:B->bool`;
                 `phi:A->B`; `psi:B->A`] P2B_PULLBACK_SMOOTH_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top' (V:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  ABBREV_TAC `P = IMAGE (\c. ({y | y IN X /\ (phi:A->B) y IN FST c},SND c o phi))
                        (O:((B->bool)#(B->real^N))->bool)` THEN
  REWRITE_TAC[mfd_oriented_atlas; FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`W1:A->bool`; `k1:A->real^N`; `W2:A->bool`; `k2:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(W1:A->bool,k1:A->real^N) IN P` THEN
  UNDISCH_TAC `(W2:A->bool,k2:A->real^N) IN P` THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `D2:B->bool` (X_CHOOSE_THEN `f2:B->real^N` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:B->bool` (X_CHOOSE_THEN `f1:B->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(W1:A->bool,k1:A->real^N) IN P /\ (W2,k2) IN P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[P2B_IN_PULLBACK_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN X /\ (phi:A->B) x IN D1 /\ phi x IN D2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN W1 INTER W2` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_jac (W1:A->bool,k1:A->real^N) (W2,k2) x =
                chart_jac (D1:B->bool,f1:B->real^N) (D2,f2) ((phi:A->B) x)` SUBST1_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `mfd_oriented_atlas (O:((B->bool)#(B->real^N))->bool)` THEN
    REWRITE_TAC[mfd_oriented_atlas] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER; FST]] THEN
  REWRITE_TAC[chart_jac; SND] THEN ASM_REWRITE_TAC[o_THM] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `chart_trans (D1:B->bool,f1:B->real^N) (D2,f2)` THEN
  SUBGOAL_THEN `open (IMAGE (f1:B->real^N) (D1 INTER V))` MP_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`;
                          `D1:B->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[open_def] THEN
  DISCH_THEN(MP_TAC o SPEC `(f1:B->real^N) ((phi:A->B) x)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?y:A. y IN X /\ phi y = (w:B)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[chart_trans; SND; o_THM] THEN
    SUBGOAL_THEN `chart_inv (D1:B->bool,f1:B->real^N) (f1 w) = w` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `D1:B->bool`;
                     `f1:B->real^N`] CHART_INV) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv ({y | y IN X /\ (phi:A->B) y IN D1},(f1:B->real^N) o phi)
                            (f1 w) = (y:A)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`subtopology top (X:A->bool)`; `P:((A->bool)#(A->real^N))->bool`;
                     `{y | y IN X /\ (phi:A->B) y IN D1}`; `(f1:B->real^N) o (phi:A->B)`]
                    CHART_INV) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:A` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `D1:B->bool`;
                   `f1:B->real^N`; `D2:B->bool`; `f2:B->real^N`; `(phi:A->B) x`]
                  CHART_TRANS_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[chart_jac; SND]]);;

(* ------------------------------------------------------------------------- *)
(* Orientability of an open subset diffeomorphic to an orientable one.     *)

let P2B_DIFFEO_ATLAS_SUB = prove
 (`!top atlas X top' atlas' O V (phi:A->B) psi.
     mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) X top'
                (atlas' UNION O:((B->bool)#(B->real^N))->bool) V phi psi
     ==> mfd_diffeo top atlas X top' O V phi psi`,
  REWRITE_TAC[mfd_diffeo; mfd_smooth_map; IN_UNION] THEN MESON_TAC[]);;

let P2B_ORIENTABLE_EMBED = prove
 (`!top atlas X top' atlas' V (phi:A->B) psi.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
     mfd_orientable top' atlas' /\ mfd_diffeo top atlas X top' atlas' V phi psi
     ==> mfd_orientable (subtopology top X) (restrict_atlas atlas X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_orientable top' (atlas':((B->bool)#(B->real^N))->bool)` THEN
  REWRITE_TAC[mfd_orientable] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:((B->bool)#(B->real^N))->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) X top'
                  (O:((B->bool)#(B->real^N))->bool) V (phi:A->B) psi` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_DIFFEO_ATLAS_SUB THEN
    EXISTS_TAC `atlas':((B->bool)#(B->real^N))->bool` THEN
    MATCH_MP_TAC P2B_DIFFEO_ATLAS_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\c. ({y | y IN X /\ (phi:A->B) y IN FST c},SND c o phi))
                    (O:((B->bool)#(B->real^N))->bool)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->bool`;
                 `top':B topology`; `O:((B->bool)#(B->real^N))->bool`; `V:B->bool`;
                 `phi:A->B`; `psi:B->A`] P2B_PULLBACK_SMOOTH_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2B_PULLBACK_ORIENTED THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `top':B topology`; `V:B->bool`; `psi:B->A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local orientability of limits of histories and of regular views.       *)

let P2B_LORIENT_EMBED_CORE = prove
 (`!top atlas (W:num->B->bool) (phi:num->B->A) (top':num->A topology) atlas'.
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     (!k. open_in top (W k) /\ W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\
     (!k. smooth_manifold_atlas (top' k) (atlas' k:((A->bool)#(A->real^3))->bool) /\
          mfd_orientable (top' k) (atlas' k) /\
          ?psi. mfd_diffeo top atlas (W k) (top' k) (atlas' k) (IMAGE (phi k) (W k)) (phi k) psi)
     ==> p2b_lorient top atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tgt")))) THEN
  REWRITE_TAC[p2b_lorient] THEN X_GEN_TAC `X:B->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `W:num->B->bool`; `top closure_of (X:B->bool)`]
                P2B_COMPACT_IN_EXHAUST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  USE_THEN "tgt" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:A->B`))) THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:A`,`:B`] P2B_ORIENTABLE_EMBED) THEN
  MAP_EVERY EXISTS_TAC [`(top':num->A topology) k`; `(atlas':num->((A->bool)#(A->real^3))->bool) k`;
                        `IMAGE ((phi:num->B->A) k) X`; `(phi:num->B->A) k`; `psi:A->B`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  EXISTS_TAC `(W:num->B->bool) k` THEN
  EXISTS_TAC `IMAGE ((phi:num->B->A) k) (W k)` THEN ASM_REWRITE_TAC[]);;

let P2B_LORIENT_FROM_FLOW_LIMIT = prove
 (`!V x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t Q (top,atlas) g xl Tl /\
     (!k. smooth_manifold_atlas (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)) /\
          mfd_orientable (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)))
     ==> p2b_lorient top atlas`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2B_FLOW_LIMIT_EXHAUST) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
      (X_CHOOSE_THEN `phi:num->B->A` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC P2B_LORIENT_EMBED_CORE THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`;
                        `\k. rfs_vtop ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (t k)`;
                        `\k. rfs_vatlas ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (t k)`] THEN
  ASM_REWRITE_TAC[]);;

let P2B_HS_SLICE_STAGE = prove
 (`!hs:(A)rfs_history t x.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs t)
     ==> rfs_slab hs t <= hs_count hs /\
         rfs_top_at hs t = hs_top hs (rfs_slab hs t) /\
         rfs_atlas_at hs t = hs_atlas hs (rfs_slab hs t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`; `x:A`] P2B_HS_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_live; rfs_horizon]; SIMP_TAC[]]);;

let P2B_LORIENT_LIMIT = prove
 (`!(u:A->bool) (w:B->bool). P2B_LORIENT_LIMIT_STATEMENT u w`,
  REWRITE_TAC[P2B_LORIENT_LIMIT_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2B_LORIENT_FROM_FLOW_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`\n. rfs_view ((hs:num->(A)rfs_history) n)`;
                        `x:num->A`; `t:num->real`; `Q:num->real`;
                        `g:real->B->real^3^3`; `xl:B`; `Tl:real`] THEN
  ASM_REWRITE_TAC[P2B_RFS_VIEW_PARTS] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) k`; `(t:num->real) k`; `(x:num->A) k`]
                P2B_HS_SLICE_SMOOTH) THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) k`; `(t:num->real) k`; `(x:num->A) k`]
                P2B_HS_SLICE_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let P2B_LORIENT_LIMIT_VIEW = prove
 (`!(u:A->bool) (w:B->bool). P2B_LORIENT_LIMIT_VIEW_STATEMENT u w`,
  REWRITE_TAC[P2B_LORIENT_LIMIT_VIEW_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2B_LORIENT_FROM_FLOW_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)`;
                        `x:num->A`; `t:num->real`; `Q:num->real`;
                        `g:real->B->real^3^3`; `xl:B`; `Tl:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  SUBGOAL_THEN `~(topspace(rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    MATCH_MP_TAC P2B_FLOW_LIMIT_BASE_SLICE THEN
    MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `xl:B`; `Tl:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `p2c_regular_view ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)` THEN
  REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->real) k` o CONJUNCT1) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Eventual limits of kappa-solutions (P2B_KSEP_LIMIT).                    *)

let P2B_DIFFEO_RESTRICT_TARGET = prove
 (`!top atlas X top' atlas' Y (f:A->B) g.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
     mfd_diffeo top atlas X top' atlas' Y f g
     ==> mfd_diffeo top atlas X (subtopology top' Y) (restrict_atlas atlas' Y) Y f g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) X top'
                 (atlas':((B->bool)#(B->real^N))->bool) Y (f:A->B) g` THEN
  REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^N))->bool) X (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `h:A->real^N`; `V:B->bool`; `k:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `V0:B->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (h:A->real^N) {x | x IN U INTER X /\ (f:A->B) x IN V0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
      MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `h:A->real^N`; `V0:B->bool`; `k:B->real^N`]) THEN
      ASM_REWRITE_TAC[FST; SND]];
    UNDISCH_TAC `mfd_smooth_map (atlas':((B->bool)#(B->real^N))->bool)
                   (atlas:((A->bool)#(A->real^N))->bool) Y (g:B->A)` THEN
    REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`V:B->bool`; `k:B->real^N`; `U:A->bool`; `h:A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `V0:B->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(h:A->real^N) o (g:B->A) o chart_inv (V0:B->bool,k:B->real^N)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `V0:B->bool`; `k:B->real^N`; `Y:B->bool`; `x:B`]
                    MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (k:B->real^N) {y | y IN V0 INTER Y /\ (g:B->A) y IN U}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
        MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`V0:B->bool`; `k:B->real^N`; `U:A->bool`; `h:A->real^N`]) THEN
        ASM_REWRITE_TAC[FST; SND]]]]);;

let P2B_LORIENT_EMBED_CORE2 = prove
 (`!top atlas (W:num->B->bool) (phi:num->B->B) (top':num->B topology) atlas'.
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     (!k. open_in top (W k) /\ W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\
     (!k. hausdorff_space (top' k) /\
          smooth_manifold_atlas (top' k) (atlas' k:((B->bool)#(B->real^3))->bool) /\
          p2b_lorient (top' k) (atlas' k) /\
          ?psi. mfd_diffeo top atlas (W k) (top' k) (atlas' k) (IMAGE (phi k) (W k)) (phi k) psi)
     ==> p2b_lorient top atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tgt")))) THEN
  REWRITE_TAC[p2b_lorient] THEN X_GEN_TAC `X:B->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `W:num->B->bool`; `top closure_of (X:B->bool)`]
                P2B_COMPACT_IN_EXHAUST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  USE_THEN "tgt" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lor") (X_CHOOSE_TAC `psi:B->B`)))) THEN
  SUBGOAL_THEN `(X:B->bool) SUBSET W (k:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (X:B->bool)` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) X
                  ((top':num->B topology) k) ((atlas':num->((B->bool)#(B->real^3))->bool) k)
                  (IMAGE ((phi:num->B->B) k) X) (phi k) (psi:B->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `(W:num->B->bool) k` THEN
    EXISTS_TAC `IMAGE ((phi:num->B->B) k) (W k)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = IMAGE ((phi:num->B->B) k) X` THEN
  SUBGOAL_THEN `open_in ((top':num->B topology) k) Y` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in ((top':num->B topology) k) ((top' k) closure_of Y)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MFD_DIFFEO_MAPS (ASSUME
      `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) k)
                  ((top':num->B topology) k) ((atlas':num->((B->bool)#(B->real^3))->bool) k)
                  (IMAGE ((phi:num->B->B) k) (W k)) (phi k) (psi:B->B)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `compact_in ((top':num->B topology) k)
                    (IMAGE ((phi:num->B->B) k) (top closure_of X))` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology top ((W:num->B->bool) k)` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE ((phi:num->B->B) k) (top closure_of X)` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXPAND_TAC "Y" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC P2B_ORIENTABLE_EMBED THEN
  MAP_EVERY EXISTS_TAC [`subtopology ((top':num->B topology) k) Y`;
                        `restrict_atlas ((atlas':num->((B->bool)#(B->real^3))->bool) k) Y`;
                        `Y:B->bool`; `(phi:num->B->B) k`; `psi:B->B`] THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN CONJ_TAC THENL
   [USE_THEN "lor" (MP_TAC o REWRITE_RULE[p2b_lorient]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B_DIFFEO_RESTRICT_TARGET THEN ASM_REWRITE_TAC[]]);;

let P2B_FLOW_LIMIT_ON_EXHAUST = prove
 (`!V x t Q J (top:B topology) atlas g xl.
     p3_flow_limit_on (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) x t Q J (top,atlas) g xl
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
         ?W phi k0. (!k. open_in top (W k) /\ W k SUBSET W (SUC k) /\ xl IN W k) /\
                    UNIONS {W k | k IN (:num)} = topspace top /\
                    (!k. phi k xl = x k) /\
                    (!k. k0 <= k
                         ==> ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (t k))
                                              (rfs_vatlas (V k) (t k)) (IMAGE (phi k) (W k))
                                              (phi k) psi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&0`; `{xl:B}`; `0`; `&1`] o
    check (fun th -> can (term_match [] `!a:real b:real K:B->bool m:num eta:real. P a b K m eta`)
                         (concl th))) THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; COMPACT_IN_SING; REAL_LT_01] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1) THEN
    REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID]]);;

let P2B_KVIEW_SLICE = prove
 (`!top atlas (g:real->B->real^3^3) s.
     rfs_vtop (p2b_kview (top,atlas) g) s = (if s <= &0 then top else discrete_topology {}) /\
     rfs_vatlas (p2b_kview (top,atlas) g) s = atlas`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; IN_ELIM_THM]);;

let P2B_SHIFT_EXHAUST = prove
 (`!top (W:num->B->bool) k0.
     (!k. open_in top (W k) /\ W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top
     ==> (!k. open_in top (W(k + k0)) /\ W(k + k0) SUBSET W(SUC k + k0)) /\
         UNIONS {W(k + k0) | k IN (:num)} = topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W(m + k0)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:B`) THEN ASM_REWRITE_TAC[]]);;

let P2B_DIFFEO_IMAGE_TOPSPACE = prove
 (`!top atlas W top' atlas' (f:A->B) g x.
     mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) W top'
                (atlas':((B->bool)#(B->real^M))->bool) (IMAGE f W) f g /\ x IN W
     ==> f x IN topspace top'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2B_KSEP_LIMIT_DIRECT = prove
 (`!top atlas (g:num->real->B->real^3^3) x t Q top' atlas' g' xl J.
     (!k. hausdorff_space (top k) /\ p2b_ksep (top k) (atlas k) /\
          smooth_manifold_atlas (top k) (atlas k:((B->bool)#(B->real^3))->bool)) /\
     p3_flow_limit_on (\k. p2b_kview (top k,atlas k) (g k)) x t Q J
                      (top':B topology,atlas') g' xl
     ==> p2b_ksep top' atlas'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2B_FLOW_LIMIT_ON_EXHAUST) THEN
  REWRITE_TAC[P2B_KVIEW_SLICE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
      (X_CHOOSE_THEN `phi:num->B->B` (X_CHOOSE_THEN `k0:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dif")))))))))) THEN
  SUBGOAL_THEN
   `!k. k0 <= k
        ==> ?psi. mfd_diffeo (top':B topology) (atlas':((B->bool)#(B->real^3))->bool)
                             ((W:num->B->bool) k) ((top:num->B topology) k)
                             (atlas k:((B->bool)#(B->real^3))->bool)
                             (IMAGE ((phi:num->B->B) k) (W k)) (phi k) (psi:B->B)`
  (LABEL_TAC "dk") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "dif" (fun th -> MP_TAC(MATCH_MP (SPEC `k:num` th) (ASSUME `k0 <= k:num`))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:B->B`) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) k`; `discrete_topology({}:B->bool)`;
                   `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(phi:num->B->B) k`; `psi:B->B`; `xl:B`] P2B_DIFFEO_IMAGE_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `W:num->B->bool`; `k0:num`] P2B_SHIFT_EXHAUST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2b_ksep] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] P2B_SEP_EMBED_CORE) THEN
    MAP_EVERY EXISTS_TAC [`\k. (W:num->B->bool)(k + k0)`; `\k. (phi:num->B->B)(k + k0)`;
                          `\k. (top:num->B topology)(k + k0)`;
                          `\k. (atlas:num->((B->bool)#(B->real^3))->bool)(k + k0)`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "seq" (MP_TAC o SPEC `k + k0:num`) THEN REWRITE_TAC[p2b_ksep] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "dk" MATCH_MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC P2B_LORIENT_EMBED_CORE2 THEN
    MAP_EVERY EXISTS_TAC [`\k. (W:num->B->bool)(k + k0)`; `\k. (phi:num->B->B)(k + k0)`;
                          `\k. (top:num->B topology)(k + k0)`;
                          `\k. (atlas:num->((B->bool)#(B->real^3))->bool)(k + k0)`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "seq" (MP_TAC o SPEC `k + k0:num`) THEN REWRITE_TAC[p2b_ksep] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "dk" MATCH_MP_TAC THEN ARITH_TAC]);;

let P2B_KSEP_LIMIT = prove
 (`!w:B->bool. P2B_KSEP_LIMIT_STATEMENT w`,
  REWRITE_TAC[P2B_KSEP_LIMIT_STATEMENT] THEN MATCH_ACCEPT_TAC P2B_KSEP_LIMIT_DIRECT);;

