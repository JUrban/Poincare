needs "src/pc_moi_s3032_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s32_gfacts: shared geometric facts for the Sec 32 files           *)
(* pc_moi_s32_cell and pc_moi_s32_sides, Moise GTM 47, Theorem 32.2.        *)
(*   1. The model cylinder: compact, its interior and frontier, the two     *)
(*      hemispheres of the frontier meet in the rim, model points.          *)
(*   2. An injective continuous map on a compact set of real^N into real^N  *)
(*      maps interior to interior and frontier to frontier (invariance of   *)
(*      domain, both ways); the forms for moi_s32_model.                    *)
(*   3. The chain lies in g(v) plus the centre: hh i in g(rev(dd(2i))),     *)
(*      bb i in the level region, so off g(rim) and inside interior g(cyl). *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. The model cylinder: closed, bounded, compact; its interior is the     *)
(* open cylinder, its frontier the union of the two hemispheres, which meet *)
(* in the rim; centre, qlo, qhi are interior points on the axis.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GF_RAD_CONT = prove
 (`!a:real^3. (\x:real^3. lift(x$1 pow 2 + x$3 pow 2)) continuous at a`,
  GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_LIFT_POW THEN
  SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH]);;

let MOI_S3GF_RAD_CLOSED = prove
 (`closed {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1}`,
  MP_TAC(ISPECL [`\x:real^3. lift(x$1 pow 2 + x$3 pow 2)`; `{y:real^1 | y$1 <= &1}`]
    CONTINUOUS_CLOSED_PREIMAGE_UNIV) THEN
  REWRITE_TAC[MOI_S3GF_RAD_CONT; CLOSED_HALFSPACE_COMPONENT_LE; IN_ELIM_THM;
              LIFT_COMPONENT]);;

let MOI_S3GF_RAD_OPEN = prove
 (`open {x:real^3 | x$1 pow 2 + x$3 pow 2 < &1}`,
  MP_TAC(ISPECL [`\x:real^3. lift(x$1 pow 2 + x$3 pow 2)`; `{y:real^1 | y$1 < &1}`]
    CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[MOI_S3GF_RAD_CONT; OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM;
              LIFT_COMPONENT]);;

let MOI_S3GF_CYL_EQ = prove
 (`moi_s32_cyl = {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1} INTER
                 ({x:real^3 | x$2 <= &1} INTER {x:real^3 | x$2 >= -- &1})`,
  REWRITE_TAC[moi_s32_cyl; EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_S3GF_CYL_CLOSED = prove
 (`closed moi_s32_cyl`,
  REWRITE_TAC[MOI_S3GF_CYL_EQ] THEN
  REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[MOI_S3GF_RAD_CLOSED; CLOSED_HALFSPACE_COMPONENT_LE;
              CLOSED_HALFSPACE_COMPONENT_GE]);;

let MOI_S3GF_CYL_BOUNDED = prove
 (`bounded moi_s32_cyl`,
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^3,&2)` THEN
  REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; moi_s32_cyl; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_LE_SQUARE; DOT_3] THEN
  SUBGOAL_THEN `(x:real^3)$2 pow 2 <= &1` MP_TAC THENL
   [ASM_REWRITE_TAC[ABS_SQUARE_LE_1]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3)$1 pow 2 + x$3 pow 2 <= &1` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_S3GF_CYL_COMPACT = prove
 (`compact moi_s32_cyl`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; MOI_S3GF_CYL_BOUNDED; MOI_S3GF_CYL_CLOSED]);;

(* A point with x1^2 + x3^2 = 1 has points with larger radius arbitrarily   *)
(* close, so the closed solid cylinder of radius 1 has the open one as its  *)
(* interior.                                                                *)

let MOI_S3GF_INTERIOR_RAD = prove
 (`interior {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1} =
   {x:real^3 | x$1 pow 2 + x$3 pow 2 < &1}`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[MOI_S3GF_RAD_OPEN] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LT_IMP_LE]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$3 pow 2 <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN ball(x,e)` MP_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    UNDISCH_TAC `ball(x:real^3,e) SUBSET {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `w = vector[(x:real^3)$1; &0; x$3]:real^3` THEN
  SUBGOAL_THEN `norm(w:real^3) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[vector_norm; DOT_3; VECTOR_3] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REWRITE_TAC[SQRT_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x + (e / &2) % w:real^3) IN ball(x,e)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^3,x + y) = norm y`; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x + (e / &2) % w:real^3)$1 pow 2 + (x + (e / &2) % w)$3 pow 2 <= &1`
  MP_TAC THENL
   [UNDISCH_TAC `ball(x:real^3,e) SUBSET {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "w" THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  SUBGOAL_THEN `((x:real^3)$1 + e / &2 * x$1) pow 2 + (x$3 + e / &2 * x$3) pow 2 =
                (&1 + e / &2) pow 2 * (x$1 pow 2 + x$3 pow 2)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  MP_TAC(SPEC `e / &2` REAL_LE_POW_2) THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let MOI_S3GF_INTERIOR_CYL = prove
 (`interior moi_s32_cyl =
   {x:real^3 | x$1 pow 2 + x$3 pow 2 < &1 /\ abs(x$2) < &1}`,
  REWRITE_TAC[MOI_S3GF_CYL_EQ; INTERIOR_INTER; MOI_S3GF_INTERIOR_RAD;
              INTERIOR_HALFSPACE_COMPONENT_LE; INTERIOR_HALFSPACE_COMPONENT_GE] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_S3GF_FRONTIER_CYL = prove
 (`frontier moi_s32_cyl = moi_s32_lohemi UNION moi_s32_hihemi`,
  REWRITE_TAC[frontier; MOI_S3GF_INTERIOR_CYL;
              MATCH_MP CLOSURE_CLOSED MOI_S3GF_CYL_CLOSED] THEN
  REWRITE_TAC[moi_s32_lohemi; moi_s32_hihemi; moi_s32_lo; moi_s32_hi; moi_s32_cyl;
              EXTENSION; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN REAL_ARITH_TAC);;

let MOI_S3GF_HEMI_INTER = prove
 (`moi_s32_lohemi INTER moi_s32_hihemi = moi_s32_rim`,
  REWRITE_TAC[moi_s32_lohemi; moi_s32_hihemi; moi_s32_lo; moi_s32_hi; moi_s32_rim;
              moi_s32_disk; moi_s32_cyl; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN REAL_ARITH_TAC);;

let MOI_S3GF_MODEL_POINTS = prove
 (`vec 0 IN interior moi_s32_cyl /\ moi_s32_qlo IN interior moi_s32_cyl /\
   moi_s32_qhi IN interior moi_s32_cyl /\
   moi_s32_rim SUBSET frontier moi_s32_cyl /\
   moi_s32_lohemi SUBSET frontier moi_s32_cyl /\
   moi_s32_hihemi SUBSET frontier moi_s32_cyl /\
   vec 0 IN moi_s32_axis /\ moi_s32_qlo IN moi_s32_axis /\ moi_s32_qhi IN moi_s32_axis`,
  REWRITE_TAC[MOI_S3GF_FRONTIER_CYL; MOI_S3GF_INTERIOR_CYL; GSYM MOI_S3GF_HEMI_INTER] THEN
  REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT; moi_s32_qlo; moi_s32_qhi; moi_s32_axis;
              VECTOR_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN SET_TAC[]);;

let MOI_S3GF_CYL_PARTS = prove
 (`interior moi_s32_cyl SUBSET moi_s32_cyl /\
   frontier moi_s32_cyl SUBSET moi_s32_cyl /\
   frontier moi_s32_cyl INTER interior moi_s32_cyl = {}`,
  REWRITE_TAC[INTERIOR_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN REWRITE_TAC[MOI_S3GF_CYL_CLOSED];
    REWRITE_TAC[frontier] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Invariance of domain both ways: a continuous injective map on a       *)
(* compact subset of real^N into real^N maps interior onto the interior of  *)
(* the image and frontier onto its frontier.  The forms for moi_s32_model.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GF_INTERIOR_IMAGE = prove
 (`!(g:real^N->real^N) s.
     compact s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
     ==> interior(IMAGE g s) = IMAGE g (interior s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `g:real^N->real^N`; `IMAGE (g:real^N->real^N) s`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^N->real^N` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g':real^N->real^N`; `IMAGE (g:real^N->real^N) s`]
      CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `IMAGE (g':real^N->real^N) (IMAGE g s) = s`] THEN
    MP_TAC(ISPEC `IMAGE (g:real^N->real^N) s` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!y. y IN IMAGE (g:real^N->real^N) s ==> g ((g':real^N->real^N) y) = y` THEN
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN ASM_REWRITE_TAC[LE_REFL]]);;

let MOI_S3GF_FRONTIER_IMAGE = prove
 (`!(g:real^N->real^N) s.
     compact s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
     ==> frontier(IMAGE g s) = IMAGE g (frontier s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (g:real^N->real^N) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  SUBGOAL_THEN `interior(IMAGE (g:real^N->real^N) s) = IMAGE g (interior s)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S3GF_INTERIOR_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET]);;

let MOI_S3GF_MODEL_HOMEO = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> ?g'. homeomorphism (moi_s32_cyl,IMAGE g moi_s32_cyl) (g,g')`,
  REWRITE_TAC[moi_s32_model] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_REWRITE_TAC[MOI_S3GF_CYL_COMPACT]);;

let MOI_S3GF_MODEL_INTERIOR = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> interior (IMAGE g moi_s32_cyl) = IMAGE g (interior moi_s32_cyl)`,
  REWRITE_TAC[moi_s32_model] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3GF_INTERIOR_IMAGE THEN
  ASM_REWRITE_TAC[MOI_S3GF_CYL_COMPACT]);;

let MOI_S3GF_MODEL_OPEN = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> moi_s32_open g = IMAGE g (interior moi_s32_cyl) /\ open (moi_s32_open g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_INTERIOR) THEN
  REWRITE_TAC[moi_s32_open; OPEN_INTERIOR] THEN ASM_REWRITE_TAC[]);;

let MOI_S3GF_MODEL_FRONTIER = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> frontier (IMAGE g moi_s32_cyl) = IMAGE g (frontier moi_s32_cyl)`,
  REWRITE_TAC[moi_s32_model] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3GF_FRONTIER_IMAGE THEN
  ASM_REWRITE_TAC[MOI_S3GF_CYL_COMPACT]);;

let MOI_S3GF_MODEL_BD_INTERIOR = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> IMAGE g (frontier moi_s32_cyl) INTER interior (IMAGE g moi_s32_cyl) = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3GF_MODEL_INTERIOR) THEN
  UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN
  REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN
  UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                     ==> x = y` THEN
  SET_TAC[]);;

(* The open set v of the model: its image is open, lies in the open set M,  *)
(* and misses g(rim) and the centre.                                        *)

let MOI_S3GF_MODEL_V = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> open (IMAGE g v) /\ IMAGE g v SUBSET moi_s32_open g /\
         DISJOINT (IMAGE g v) (IMAGE g moi_s32_rim) /\
         ~(g (vec 0) IN IMAGE g moi_s32_rim) /\ ~(g (vec 0) IN IMAGE g v) /\
         g (vec 0) IN moi_s32_open g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN
  REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  MP_TAC MOI_STD_S32_MODEL_FACTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS];
      ASM_MESON_TAC[SUBSET]];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `v SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `moi_s32_rim SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `interior moi_s32_cyl SUBSET moi_s32_cyl` THEN
    UNDISCH_TAC `frontier moi_s32_cyl SUBSET moi_s32_cyl` THEN
    UNDISCH_TAC `frontier moi_s32_cyl INTER interior moi_s32_cyl = {}` THEN
    UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    SET_TAC[];
    UNDISCH_TAC `moi_s32_rim SUBSET moi_s32_disk` THEN
    UNDISCH_TAC `moi_s32_disk SUBSET moi_s32_cyl` THEN
    UNDISCH_TAC `vec 0 IN moi_s32_disk` THEN UNDISCH_TAC `~(vec 0 IN moi_s32_rim)` THEN
    UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    SET_TAC[];
    UNDISCH_TAC `v SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `interior moi_s32_cyl SUBSET moi_s32_cyl` THEN
    UNDISCH_TAC `DISJOINT v moi_s32_axis` THEN UNDISCH_TAC `vec 0 IN moi_s32_axis` THEN
    UNDISCH_TAC `vec 0 IN moi_s32_disk` THEN UNDISCH_TAC `moi_s32_disk SUBSET moi_s32_cyl` THEN
    UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The chain lies in g(v) plus the centre.  Every torus s2 k is compact  *)
(* and lies in g(rev(dd k)) (canonical configuration at k, index 0), so the *)
(* annulus hh i on its boundary does too; the bridges bb i lie in the level *)
(* region, a union of three revolved cells, all inside v.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3GF_TOWER_TORI = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !k. pl_solid_torus (s2 k) /\ compact (s2 k) /\
             s2 k SUBSET IMAGE g (revolution (dd k)) /\
             frontier (s2 k) SUBSET IMAGE g (revolution (dd k)) /\
             revolution (dd k) SUBSET v /\
             IMAGE g (revolution (dd k)) SUBSET IMAGE g v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cc") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `k:int` THEN
  REMOVE_THEN "cc" (MP_TAC o SPEC `k:int`) THEN
  REWRITE_TAC[canonical_configuration] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[ARITH; INT_ADD_RID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact ((s2:int->real^3->bool) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STD_PL_SOLID_TORUS_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s2:int->real^3->bool) k SUBSET
                IMAGE (g:real^3->real^3) (revolution (dd k))` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `revolution ((dd:int->real^3->bool) k) SUBSET v` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED; SUBSET_TRANS];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_S3GF_CHAIN_PIECES0 = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_tower g v pp dd s2 /\ moi_s32_chain g dd s2 hh bb jl jh
     ==> !i. hh i SUBSET IMAGE g (revolution (dd (&2 * i))) /\
             hh i SUBSET IMAGE g v /\ bb i SUBSET IMAGE g v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP MOI_S3GF_TOWER_TORI) MP_TAC) THEN
  REWRITE_TAC[moi_s32_chain] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  X_GEN_TAC `i:int` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:int` o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "pl_annulus_with_ends"
                                              with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `(hh:int->real^3->bool) i SUBSET
                IMAGE (g:real^3->real^3) (revolution (dd (&2 * i)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl g dd i` THEN
    ASM_REWRITE_TAC[moi_s32_lvl; UNION_SUBSET] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3GF_CHAIN_V0 = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_tower g v pp dd s2 /\ moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_chainset g hh bb SUBSET g (vec 0) INSERT IMAGE g v`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S3GF_CHAIN_PIECES0) THEN
  REWRITE_TAC[moi_s32_chainset; UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:int`) THEN SET_TAC[];
    SET_TAC[]]);;

(* The forms with the antecedent of the theorems CELL and SIDES.          *)

let MOI_S3GF_CHAIN_PIECES = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> (!i. hh i SUBSET IMAGE g (revolution (dd (&2 * i)))) /\
         (!i. hh i SUBSET IMAGE g v) /\ (!i. bb i SUBSET IMAGE g v)`,
  MESON_TAC[MOI_S3GF_CHAIN_PIECES0]);;

let MOI_S3GF_CHAIN_V = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_chainset g hh bb SUBSET g (vec 0) INSERT IMAGE g v`,
  MESON_TAC[MOI_S3GF_CHAIN_V0]);;

(* So the chain lies in M, misses g(rim), and the pseudo-cell minus g(rim)  *)
(* is the chain.                                                            *)

let MOI_S3GF_CHAIN_OPEN = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_chainset g hh bb SUBSET moi_s32_open g /\
         DISJOINT (moi_s32_chainset g hh bb) (IMAGE g moi_s32_rim) /\
         (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) DIFF IMAGE g moi_s32_rim =
         moi_s32_chainset g hh bb`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S3GF_CHAIN_V) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_MODEL_V o CONJUNCT1) THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (moi_s32_chainset (g:real^3->real^3) hh bb) (IMAGE g moi_s32_rim)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_chainset (g:real^3->real^3) hh bb SUBSET g (vec 0) INSERT IMAGE g v` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) v) (IMAGE g moi_s32_rim)` THEN
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN IMAGE g moi_s32_rim)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `moi_s32_chainset (g:real^3->real^3) hh bb SUBSET g (vec 0) INSERT IMAGE g v` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) v SUBSET moi_s32_open g` THEN
    UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN moi_s32_open g` THEN
    SET_TAC[];
    UNDISCH_TAC `DISJOINT (moi_s32_chainset (g:real^3->real^3) hh bb) (IMAGE g moi_s32_rim)` THEN
    SET_TAC[]]);;

