(* ========================================================================= *)
(* pc_smt_sep: neck spheres separate in a smooth 3-manifold whose components *)
(* are simply connected, SMT_SC_SPHERE_SEP (APX_SC_SPHERE_SEP_STATEMENT of   *)
(* pc_apx_sep.ml). A winding map g to the punctured plane, equal to cexp(2   *)
(* pi i beta |x|) across the neck and 1 elsewhere, lifts through cexp on the *)
(* component of the neck (pc_top_cover, COVERING_MAP_LIFT_STRONG); off the   *)
(* sphere it has an explicit logarithm h0 jumping by 2 pi i across the       *)
(* sphere; a connected set joining the two sides would force the lift and h0 *)
(* to differ by a constant, contradicting the radial path.                   *)
(*                                                                           *)
(* Generalities (the cexp covering, logarithms of 1 on                      *)
(* connected sets); manifolds are locally path connected by                  *)
(* GEO_MANIFOLD_LOCALLY_PATH_CONNECTED of pc_mfd_diff.ml.                    *)
(* ========================================================================= *)

needs "src/pc_smt_glue.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_apx_sep.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_CEXP_COVERING = prove
 (`covering_map (subtopology euclidean (:complex),
                 subtopology euclidean ((:complex) DIFF {Cx(&0)})) cexp`,
  REWRITE_TAC[COVERING_MAP_EUCLIDEAN; COVERING_SPACE_CEXP_PUNCTURED_PLANE]);;

(* A continuous logarithm of 1 on a connected set is constant. *)

let SMT_CEXP_ONE_CONSTANT = prove
 (`!top D (f:A->complex) a b.
        connected_in top D /\ continuous_map (subtopology top D,euclidean) f /\
        (!x. x IN D ==> cexp(f x) = Cx(&1)) /\ a IN D /\ b IN D
        ==> f a = f b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (f:A->complex) D)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONNECTED_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology top (D:A->bool)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:complex. z`; `IMAGE (f:A->complex) D`]
    CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IMP_CONJ; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `cexp((f:A->complex) x) = Cx(&1) /\ cexp(f y) = Cx(&1)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CEXP_EQ_1] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `~(n - m = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((f:A->complex) y = f x)` THEN
      REWRITE_TAC[COMPLEX_EQ] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `n - m = &0` THEN REWRITE_TAC[REAL_SUB_0] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `n - m:real` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_SIMP_TAC[INTEGER_SUB] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(f:A->complex) y - f x` COMPLEX_NORM_GE_RE_IM) THEN
    ASM_REWRITE_TAC[IM_SUB] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&2 * n * pi - &2 * m * pi)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&2 * n * pi - &2 * m * pi = (&2 * pi) * (n - m)`;
                REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs(&2) * abs pi) * &1` THEN
    CONJ_TAC THENL
     [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The winding angle 2 pi i beta(|x|) across the neck.                       *)
(* ------------------------------------------------------------------------- *)

let smt_wind = new_definition
 `smt_wind (x:real^N) = Cx(&2 * pi * smooth_step((&6 * norm x - &4) / &5)) * ii`;;

let SMT_WIND_CONTINUOUS = prove
 (`smt_wind continuous_on (:real^N)`,
  SUBGOAL_THEN `smt_wind = \x:real^N. Cx(&2 * pi * smooth_step((&6 * norm x - &4) / &5)) * ii`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; smt_wind]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
  REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
  SUBGOAL_THEN `(\x:real^N. lift((&6 * norm x - &4) / &5)) continuous_on (:real^N)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. lift((&6 * norm x - &4) / &5)) =
                  (\x. inv(&5) % (&6 % (lift o norm) x) - lift(&4 / &5))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_CMUL) THEN
    REWRITE_TAC[ETA_AX; CONTINUOUS_ON_LIFT_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(&2 * pi * smooth_step((&6 * norm x - &4) / &5))) =
    (\y. (&2 * pi) % y) o ((lift o smooth_step o drop) o
                            (\x. lift((&6 * norm x - &4) / &5)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; GSYM LIFT_CMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    REWRITE_TAC[SMOOTH_STEP_SMOOTH];
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID]]);;

let SMT_WIND_INNER = prove
 (`!x:real^N. norm x <= &2 / &3 ==> smt_wind x = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smt_wind] THEN
  SUBGOAL_THEN `smooth_step((&6 * norm(x:real^N) - &4) / &5) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO]);;

let SMT_WIND_OUTER = prove
 (`!x:real^N. &3 / &2 <= norm x ==> smt_wind x = Cx(&2 * pi) * ii`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smt_wind] THEN
  SUBGOAL_THEN `smooth_step((&6 * norm(x:real^N) - &4) / &5) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

let SMT_CEXP_2PI_II = prove
 (`cexp(Cx(&2 * pi) * ii) = Cx(&1)`,
  MP_TAC(SPEC `&1` CEXP_INTEGER_2PI) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_LID]);;

let SMT_CEXP_WIND_OFF = prove
 (`!x:real^N. ~(&2 / &3 < norm x /\ norm x < &3 / &2) ==> cexp(smt_wind x) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(x:real^N) <= &2 / &3` THENL
   [ASM_SIMP_TAC[SMT_WIND_INNER; CEXP_0];
    SUBGOAL_THEN `&3 / &2 <= norm(x:real^N)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SMT_WIND_OUTER; SMT_CEXP_2PI_II]]]);;

(* ------------------------------------------------------------------------- *)
(* The winding map of a neck chart and its logarithm off the                 *)
(* neck sphere.                                                              *)
(* ------------------------------------------------------------------------- *)

let SMT_CONT_THROUGH_INV = prove
 (`!top N W (e':A->real^M) (FF:real^M->real^P).
        continuous_map (subtopology top N,euclidean) e' /\ W SUBSET N /\
        FF continuous_on (:real^M)
        ==> continuous_map (subtopology top W,euclidean) (\y. FF(e' y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:A. (FF:real^M->real^P)(e' y)) = FF o e'` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `euclidean:(real^M)topology` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `subtopology top (W:A->bool) = subtopology (subtopology top N) W`
    SUBST1_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`FF:real^M->real^P`; `(:real^M)`; `(:real^P)`]
      CONTINUOUS_MAP_EUCLIDEAN2) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; SUBSET_UNIV]]);;

let SMT_NECK_WINDING_MAP = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_neck_chart top atlas e
        ==> ?g h0.
              continuous_map (top,euclidean) g /\
              (!y. y IN topspace top ==> ~(g y = Cx(&0))) /\
              (!x. x IN annulus (&1 / &2) (&2) ==> g(e x) = cexp(smt_wind x)) /\
              continuous_map (subtopology top
                (topspace top DIFF IMAGE e (sphere(vec 0,&1))),euclidean) h0 /\
              (!y. y IN topspace top DIFF IMAGE e (sphere(vec 0,&1))
                   ==> cexp(h0 y) = g y) /\
              (!x. x IN annulus (&1 / &2) (&1) ==> h0(e x) = smt_wind x) /\
              (!x. x IN annulus (&1) (&2)
                   ==> h0(e x) = smt_wind x - Cx(&2 * pi) * ii)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_neck_chart top (atlas:((A->bool)#(A->real^3))->bool)
                               (e:real^3->A)` THEN
  REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  (* the annuli and the compact middle *)
  SUBGOAL_THEN
   `annulus (&1 / &2) (&1) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
    annulus (&1) (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
    sphere(vec 0,&1) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
    cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3) SUBSET
      annulus (&1 / &2) (&2):real^3->bool /\
    sphere(vec 0,&1) SUBSET
      cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3):real^3->bool`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0;
                IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
          (e:real^3->A) x = e y ==> x = y`
  (LABEL_TAC "einj") THENL
   [ASM_MESON_TAC[MFD_PARAM_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))) /\
    open_in top (IMAGE (e:real^3->A) (annulus (&1) (&2))) /\
    open_in top (topspace top DIFF
                 IMAGE (e:real^3->A) (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`atlas:((A->bool)#(A->real^3))->bool`; `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`atlas:((A->bool)#(A->real^3))->bool`; `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC
       [`atlas:((A->bool)#(A->real^3))->bool`; `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  (* bookkeeping on the pieces of the neck *)
  SUBGOAL_THEN
   `DISJOINT (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))
             (IMAGE (e:real^3->A) (annulus (&1) (&2))) /\
    DISJOINT (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))
             (IMAGE (e:real^3->A) (sphere(vec 0,&1))) /\
    DISJOINT (IMAGE (e:real^3->A) (annulus (&1) (&2)))
             (IMAGE (e:real^3->A) (sphere(vec 0,&1))) /\
    IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) UNION
      IMAGE (e:real^3->A) (annulus (&1) (&2)) UNION
      IMAGE (e:real^3->A) (sphere(vec 0,&1)) =
      IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) /\
    IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET
      IMAGE (e:real^3->A) (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3)) /\
    IMAGE (e:real^3->A) (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3)) SUBSET
      IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `a:real^3 = b` MP_TAC THENL
       [USE_THEN "einj" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(b:real^3) IN annulus (&1 / &2) (&1)` THEN
      UNDISCH_TAC `(b:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `a:real^3 = b` MP_TAC THENL
       [USE_THEN "einj" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(b:real^3) IN annulus (&1 / &2) (&1)` THEN
      UNDISCH_TAC `(b:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `a:real^3 = b` MP_TAC THENL
       [USE_THEN "einj" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(b:real^3) IN annulus (&1) (&2)` THEN
      UNDISCH_TAC `(b:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the winding map *)
  EXISTS_TAC `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))
                  then cexp(smt_wind((e':A->real^3) y)) else Cx(&1)` THEN
  EXISTS_TAC `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))
                  then smt_wind((e':A->real^3) y)
                  else if y IN IMAGE (e:real^3->A) (annulus (&1) (&2))
                  then smt_wind(e' y) - Cx(&2 * pi) * ii
                  else Cx(&0)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cexp o smt_wind) continuous_on (:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[SMT_WIND_CONTINUOUS; CONTINUOUS_ON_CEXP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN topspace top DIFF
             IMAGE (e:real^3->A) (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3)) /\
        y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))
        ==> ~(&2 / &3 <= norm((e':A->real^3) y) /\ norm(e' y) <= &3 / &2)`
  (LABEL_TAC "off") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
      (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* g is continuous *)
    MP_TAC(ISPECL [`top:A topology`; `euclidean:(complex)topology`;
                   `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))`;
                   `topspace top DIFF IMAGE (e:real^3->A)
                      (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3))`;
                   `\y. (cexp o smt_wind) ((e':A->real^3) y)`; `\y:A. Cx(&1)`;
                   `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))
                        then cexp(smt_wind((e':A->real^3) y)) else Cx(&1)`]
      MFDG_CONTINUOUS_GLUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMT_CONT_THROUGH_INV THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[SUBSET_REFL];
        SIMP_TAC[o_THM];
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC SMT_CEXP_WIND_OFF THEN
        USE_THEN "off" (MP_TAC o SPEC `y:A`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) UNION
      (topspace top DIFF IMAGE (e:real^3->A)
         (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3))) = topspace top`
     (fun th -> REWRITE_TAC[th; SUBTOPOLOGY_TOPSPACE]) THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3))
                 SUBSET IMAGE e (annulus (&1 / &2) (&2))` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
    SET_TAC[];
    (* g never vanishes *)
    REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[CEXP_NZ; CX_INJ] THEN REAL_ARITH_TAC;
    (* g on the neck *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    (* h0 is continuous off the sphere *)
    SUBGOAL_THEN
     `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET
        IMAGE e (annulus (&1 / &2) (&2)) /\
      IMAGE (e:real^3->A) (annulus (&1) (&2)) SUBSET
        IMAGE e (annulus (&1 / &2) (&2))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`top:A topology`; `euclidean:(complex)topology`;
      `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))`;
      `IMAGE (e:real^3->A) (annulus (&1) (&2))`;
      `\y. smt_wind((e':A->real^3) y)`;
      `\y. smt_wind((e':A->real^3) y) - Cx(&2 * pi) * ii`;
      `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))
           then smt_wind((e':A->real^3) y)
           else if y IN IMAGE (e:real^3->A) (annulus (&1) (&2))
           then smt_wind(e' y) - Cx(&2 * pi) * ii
           else Cx(&0)`] MFDG_CONTINUOUS_GLUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMT_CONT_THROUGH_INV THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[SMT_WIND_CONTINUOUS];
        MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_SUB THEN
        REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
        MATCH_MP_TAC SMT_CONT_THROUGH_INV THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[SMT_WIND_CONTINUOUS];
        SIMP_TAC[];
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~((y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))`
         (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))
                              (IMAGE e (annulus (&1) (&2)))` THEN
        UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THEN
        SET_TAC[]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL
     [`top:A topology`; `euclidean:(complex)topology`;
      `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) UNION
       IMAGE (e:real^3->A) (annulus (&1) (&2))`;
      `topspace top DIFF IMAGE (e:real^3->A)
         (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3))`;
      `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))
           then smt_wind((e':A->real^3) y)
           else if y IN IMAGE (e:real^3->A) (annulus (&1) (&2))
           then smt_wind(e' y) - Cx(&2 * pi) * ii
           else Cx(&0)`;
      `\y:A. Cx(&0)`;
      `\y. if y IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))
           then smt_wind((e':A->real^3) y)
           else if y IN IMAGE (e:real^3->A) (annulus (&1) (&2))
           then smt_wind(e' y) - Cx(&2 * pi) * ii
           else Cx(&0)`] MFDG_CONTINUOUS_GLUE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_UNION; CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(&2 / &3 <= norm((e':A->real^3) y) /\ norm(e' y) <= &3 / &2)`
        MP_TAC THENL
         [USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET
                       IMAGE e (annulus (&1 / &2) (&2))` THEN
          UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THEN
          SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(z:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
         [UNDISCH_TAC `(z:real^3) IN annulus (&1 / &2) (&1)` THEN
          UNDISCH_TAC `annulus (&1 / &2) (&1) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
          SET_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC SMT_WIND_INNER THEN
        UNDISCH_TAC `(z:real^3) IN annulus (&1 / &2) (&1)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(&2 / &3 <= norm((e':A->real^3) y) /\ norm(e' y) <= &3 / &2)`
        MP_TAC THENL
         [USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1) (&2)) SUBSET
                       IMAGE e (annulus (&1 / &2) (&2))` THEN
          UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THEN
          SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(z:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
         [UNDISCH_TAC `(z:real^3) IN annulus (&1) (&2)` THEN
          UNDISCH_TAC `annulus (&1) (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
          SET_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `smt_wind(z:real^3) = Cx(&2 * pi) * ii` SUBST1_TAC THENL
         [MATCH_MP_TAC SMT_WIND_OUTER THEN
          UNDISCH_TAC `(z:real^3) IN annulus (&1) (&2)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[COMPLEX_SUB_REFL]];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) UNION
       IMAGE (e:real^3->A) (annulus (&1) (&2))) UNION
      (topspace top DIFF IMAGE (e:real^3->A)
         (cball(vec 0,&3 / &2) DIFF ball(vec 0,&2 / &3))) =
      topspace top DIFF IMAGE e (sphere(vec 0,&1))`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(SET_RULE
     `!n t p1 p2 s k:A->bool.
        n SUBSET t /\ k SUBSET n /\ s SUBSET k /\ p1 UNION p2 UNION s = n /\
        DISJOINT p2 s /\ DISJOINT p1 s
        ==> (p1 UNION p2) UNION (t DIFF k) = t DIFF s`) THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` THEN
    ASM_REWRITE_TAC[];
    (* h0 is a logarithm of g off the sphere *)
    X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))`
       (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))` THEN
      UNDISCH_TAC `annulus (&1 / &2) (&1) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))`
       (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))` THEN
        UNDISCH_TAC `annulus (&1) (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CEXP_SUB; SMT_CEXP_2PI_II; COMPLEX_DIV_1];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CEXP_0] THEN
    SUBGOAL_THEN `~((y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)))`
     (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `~((y:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))` THEN
    UNDISCH_TAC `~((y:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2)))` THEN
    UNDISCH_TAC `~((y:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1)))` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) UNION
      IMAGE e (annulus (&1) (&2)) UNION IMAGE e (sphere(vec 0,&1)) =
      IMAGE e (annulus (&1 / &2) (&2))` THEN
    SET_TAC[];
    (* values of h0 *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
      UNDISCH_TAC `annulus (&1 / &2) (&1) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
      UNDISCH_TAC `annulus (&1) (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((e:real^3->A) x IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))`
     (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`e:real^3->A`; `annulus (&1) (&2):real^3->bool`; `x:real^3`]
        FUN_IN_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)))
                            (IMAGE (e:real^3->A) (annulus (&1) (&2)))` THEN SET_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]]]);;

(* ------------------------------------------------------------------------- *)
(* The separation theorem SMT_SC_SPHERE_SEP.                                 *)
(* ------------------------------------------------------------------------- *)

(* The radial path across the neck, from 3/4 e1 to 4/3 e1. *)

let SMT_RADIAL_PATH = prove
 (`!s. s IN interval[vec 0:real^1,vec 1]
       ==> (&3 / &4 + &7 / &12 * drop s) % basis 1 IN
           annulus (&1 / &2) (&2):real^3->bool`,
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; annulus; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let SMT_RADIAL_PATH_CONTINUOUS = prove
 (`(\s:real^1. (&3 / &4 + &7 / &12 * drop s) % basis 1:real^3)
   continuous_on interval[vec 0,vec 1]`,
  MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
  REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID]);;

let SMT_SC_SPHERE_SEP = prove
 (`!u:A->bool. APX_SC_SPHERE_SEP_STATEMENT u`,
  REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT; apx_sphere_sep; apx_separates] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sc"))) THEN
  X_GEN_TAC `e:real^3->A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `e:real^3->A`] SMT_NECK_WINDING_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->complex` (X_CHOOSE_THEN `h0:A->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "gneck") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "hlog") (CONJUNCTS_THEN2 (LABEL_TAC "hin")
        (LABEL_TAC "hout"))))))))) THEN
  UNDISCH_TAC `mfd_neck_chart top (atlas:((A->bool)#(A->real^3))->bool)
                               (e:real^3->A)` THEN
  REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN
   `&3 / &4 % basis 1 IN annulus (&1 / &2) (&1):real^3->bool /\
    &4 / &3 % basis 1 IN annulus (&1) (&2):real^3->bool /\
    &3 / &4 % basis 1 IN annulus (&1 / &2) (&2):real^3->bool /\
    &4 / &3 % basis 1 IN annulus (&1 / &2) (&2):real^3->bool`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
          (e:real^3->A) x = e y ==> x = y`
  (LABEL_TAC "einj") THENL
   [ASM_MESON_TAC[MFD_PARAM_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN annulus (&1 / &2) (&2) /\ ~(norm x = &1)
        ==> (e:real^3->A) x IN topspace top DIFF IMAGE e (sphere(vec 0,&1))`
  (LABEL_TAC "off") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
      UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "einj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e:real^3->A)(&3 / &4 % basis 1) IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
    (e:real^3->A)(&4 / &3 % basis 1) IN topspace top DIFF IMAGE e (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[connected_component_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:A->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `connected_in (subtopology top
                (topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)))) D` THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  SUBGOAL_THEN `locally_path_connected_space (top:A topology)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
      GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C0 = connected_component_of top ((e:real^3->A)(&3 / &4 % basis 1))` THEN
  SUBGOAL_THEN
   `open_in top (C0:A->bool) /\ C0 SUBSET topspace top /\
    (e:real^3->A)(&3 / &4 % basis 1) IN C0 /\
    simply_connected_space (subtopology top C0) /\
    locally_path_connected_space (subtopology top C0) /\
    D SUBSET C0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in top (C0:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "C0" THEN
      MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE THEN
      ASM_SIMP_TAC[LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->A)(&3 / &4 % basis 1) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(e:real^3->A)(&3 / &4 % basis 1) IN
                   topspace top DIFF IMAGE e (sphere(vec 0,&1))` THEN
      SIMP_TAC[IN_DIFF];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "C0" THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE];
      EXPAND_TAC "C0" THEN REWRITE_TAC[IN] THEN
      ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
      USE_THEN "sc" MATCH_MP_TAC THEN EXPAND_TAC "C0" THEN
      ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF];
      MATCH_MP_TAC LOCALLY_PATH_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "C0" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the lift of the winding map on the component *)
  SUBGOAL_THEN
   `?k:A->complex.
        continuous_map (subtopology top C0,euclidean) k /\
        k((e:real^3->A)(&3 / &4 % basis 1)) = smt_wind(&3 / &4 % basis 1:real^3) /\
        (!z. z IN topspace top INTER C0 ==> cexp(k z) = g z)`
  (X_CHOOSE_THEN `k:A->complex` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "klift")))) THENL
   [MP_TAC(ISPECL [`subtopology euclidean (:complex)`;
                   `subtopology euclidean ((:complex) DIFF {Cx(&0)})`; `cexp`;
                   `subtopology top (C0:A->bool)`; `g:A->complex`;
                   `(e:real^3->A)(&3 / &4 % basis 1)`;
                   `smt_wind(&3 / &4 % basis 1:real^3)`] COVERING_MAP_LIFT_STRONG) THEN
    REWRITE_TAC[SMT_CEXP_COVERING; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_UNIV;
                TOPSPACE_SUBTOPOLOGY; SUBTOPOLOGY_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                    IN_DIFF; IN_UNIV; IN_SING] THEN
        ASM_SIMP_TAC[]];
      UNDISCH_TAC `(e:real^3->A)(&3 / &4 % basis 1) IN
                   topspace top DIFF IMAGE e (sphere(vec 0,&1))` THEN
      SIMP_TAC[IN_DIFF];
      USE_THEN "gneck" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  (* the radial path stays in the component *)
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (interval[vec 0:real^1,vec 1]),top)
      (\s. (e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\s. (e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1)) =
      e o (\s:real^1. (&3 / &4 + &7 / &12 * drop s) % basis 1)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SMT_RADIAL_PATH_CONTINUOUS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SMT_RADIAL_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN interval[vec 0:real^1,vec 1]
        ==> (e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1) IN C0`
  (LABEL_TAC "pathC0") THENL
   [SUBGOAL_THEN
     `IMAGE (\s. (e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1))
            (interval[vec 0:real^1,vec 1]) SUBSET C0`
     (fun th -> REWRITE_TAC[REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] th]) THEN
    EXPAND_TAC "C0" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (interval[vec 0:real^1,vec 1])` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEAN;
                      CONNECTED_INTERVAL];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID; IN_INTERVAL_1] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the lift and the logarithm differ by a constant on D *)
  SUBGOAL_THEN
   `(k:A->complex)((e:real^3->A)(&3 / &4 % basis 1)) -
    (h0:A->complex)(e(&3 / &4 % basis 1)) =
    k(e(&4 / &3 % basis 1)) - h0(e(&4 / &3 % basis 1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `D:A->bool`;
                   `\y. (k:A->complex) y - (h0:A->complex) y`;
                   `(e:real^3->A)(&3 / &4 % basis 1)`;
                   `(e:real^3->A)(&4 / &3 % basis 1)`] SMT_CEXP_ONE_CONSTANT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN `subtopology top (D:A->bool) = subtopology (subtopology top C0) D`
        SUBST1_TAC THENL
         [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `(D:A->bool) SUBSET C0` THEN SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
        SUBGOAL_THEN
         `subtopology top (D:A->bool) =
          subtopology (subtopology top
            (topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)))) D`
        SUBST1_TAC THENL
         [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `(D:A->bool) SUBSET
                       topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
          SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]]];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[CEXP_SUB] THEN
      SUBGOAL_THEN
       `(y:A) IN topspace top INTER C0 /\
        y IN topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(D:A->bool) SUBSET C0` THEN
        UNDISCH_TAC `(D:A->bool) SUBSET
                     topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
        UNDISCH_TAC `(y:A) IN D` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "klift" (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_THEN "hlog" (fun th -> ASM_SIMP_TAC[th]) THEN
      MATCH_MP_TAC COMPLEX_DIV_REFL THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y:A. y IN topspace top ==> ~((g:A->complex) y = Cx(&0))`)
            (concl th))) THEN
      UNDISCH_TAC `(y:A) IN topspace top INTER C0` THEN SIMP_TAC[IN_INTER]];
    ALL_TAC] THEN
  (* along the radial path the lift is the explicit angle *)
  SUBGOAL_THEN
   `(k:A->complex)((e:real^3->A)(&3 / &4 % basis 1)) -
    smt_wind(&3 / &4 % basis 1:real^3) =
    k(e(&4 / &3 % basis 1)) - smt_wind(&4 / &3 % basis 1:real^3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^1)topology`; `interval[vec 0:real^1,vec 1]`;
      `\s:real^1. (k:A->complex)((e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1)) -
                  smt_wind((&3 / &4 + &7 / &12 * drop s) % basis 1:real^3)`;
      `vec 0:real^1`; `vec 1:real^1`] SMT_CEXP_ONE_CONSTANT) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
                REAL_ARITH `&3 / &4 + &7 / &12 = &4 / &3`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CONNECTED_IN_EUCLIDEAN; CONNECTED_INTERVAL; IN_INTERVAL_1; DROP_VEC;
                REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\s:real^1. (k:A->complex)((e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1))) =
          k o (\s. e((&3 / &4 + &7 / &12 * drop s) % basis 1))`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC `subtopology top (C0:A->bool)` THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
        USE_THEN "pathC0" (fun th -> SIMP_TAC[th]);
        SUBGOAL_THEN
         `(\s:real^1. smt_wind((&3 / &4 + &7 / &12 * drop s) % basis 1:real^3)) =
          smt_wind o (\s:real^1. (&3 / &4 + &7 / &12 * drop s) % basis 1:real^3)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MP_TAC(ISPECL [`smt_wind o (\s:real^1. (&3 / &4 + &7 / &12 * drop s) % basis 1:real^3)`;
                       `interval[vec 0:real^1,vec 1]`; `(:complex)`]
          CONTINUOUS_MAP_EUCLIDEAN2) THEN
        REWRITE_TAC[SUBTOPOLOGY_UNIV; SUBSET_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC[SMT_RADIAL_PATH_CONTINUOUS] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[SUBSET_UNIV; SMT_WIND_CONTINUOUS]];
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[CEXP_SUB] THEN
      SUBGOAL_THEN `(s:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(e:real^3->A)((&3 / &4 + &7 / &12 * drop s) % basis 1) IN topspace top INTER C0`
      ASSUME_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
          MP_TAC(SPEC `s:real^1` SMT_RADIAL_PATH) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          USE_THEN "pathC0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "klift" (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_THEN "gneck" (fun th -> ASM_SIMP_TAC[th; SMT_RADIAL_PATH]) THEN
      MATCH_MP_TAC COMPLEX_DIV_REFL THEN REWRITE_TAC[CEXP_NZ]];
    ALL_TAC] THEN
  (* the contradiction *)
  SUBGOAL_THEN
   `(h0:A->complex)((e:real^3->A)(&3 / &4 % basis 1)) = smt_wind(&3 / &4 % basis 1:real^3) /\
    h0(e(&4 / &3 % basis 1)) = smt_wind(&4 / &3 % basis 1:real^3) - Cx(&2 * pi) * ii`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "hin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "hout" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&2 * pi) * ii = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `(k:A->complex)((e:real^3->A)(&3 / &4 % basis 1)) -
    (h0:A->complex)(e(&3 / &4 % basis 1)) =
    k(e(&4 / &3 % basis 1)) - h0(e(&4 / &3 % basis 1))` THEN
  UNDISCH_TAC
   `(k:A->complex)((e:real^3->A)(&3 / &4 % basis 1)) -
    smt_wind(&3 / &4 % basis 1:real^3) =
    k(e(&4 / &3 % basis 1)) - smt_wind(&4 / &3 % basis 1:real^3)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

