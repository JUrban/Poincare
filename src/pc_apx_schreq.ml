(* ========================================================================= *)
(* pc_apx_schreq: the one Schoenflies-type statement that the Appendix needs *)
(* (MT Prop A.25 and A.21(1)-(2); the end of MT's Case I of A.21, p. 513,    *)
(* uses Alexander's theorem without citing it): a neck-chart sphere inside   *)
(* the open unit ball of a ball chart bounds, on the side away from the      *)
(* boundary of that ball, the closed unit ball of a ball chart that extends  *)
(* the neck chart or its inversion on the annulus 3/4 < |x| < 2.  This is    *)
(* the smooth Schoenflies theorem in R^3 (Alexander) in the form the gluing  *)
(* of two caps needs; it is used only when the cores of two caps overlap so  *)
(* deeply that no radial gluing exists.  Statement constants and sanity      *)
(* theorems only.                                                            *)
(*                                                                           *)
(* A variant APX_SCHOENFLIES_REQ_V1_STATEMENT that asks for agreement on all *)
(* of annulus(1/2,2) is FALSE (APX_SCHREQ_V1_FALSE): the inner end of a neck *)
(* chart may collapse, e.g. e0 x = (1/2 - 1/(4|x|)) x maps annulus(1/2,2)    *)
(* onto the punctured ball of radius 3/4.  It is included, with its          *)
(* refutation, as a documented pitfall.                                      *)
(* ========================================================================= *)

needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statements.  b is a ball chart (a parametrization of                  *)
(* ball(0,2)), e a neck chart (a parametrization of annulus(1/2,2)) whose    *)
(* image lies in b(ball(0,1)).  In b-coordinates the sphere e(sphere 1)      *)
(* bounds a region D inside ball(0,1).  The conclusion: a ball chart c with  *)
(* c(cball(0,1)) inside b(ball(0,1)) (so c(ball(0,1)) is D) which is e on    *)
(* annulus(3/4,2) when the inner side of e lies in D, or e composed with the *)
(* inversion x / |x|^2 when the outer side does.  The agreement still covers *)
(* both collars of the central sphere |x| = 1.                               *)
(* ------------------------------------------------------------------------- *)

let APX_SCHOENFLIES_REQ_STATEMENT = new_definition
 `APX_SCHOENFLIES_REQ_STATEMENT (u:A->bool) <=>
    !top atlas b e.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_ball_chart top atlas b /\ mfd_neck_chart top atlas e /\
        IMAGE e (annulus (&1 / &2) (&2)) SUBSET IMAGE b (ball(vec 0,&1))
        ==> ?c. mfd_ball_chart top atlas c /\
                IMAGE c (cball(vec 0,&1)) SUBSET IMAGE b (ball(vec 0,&1)) /\
                ((!x. x IN annulus (&3 / &4) (&2) ==> c x = e x) \/
                 (!x. x IN annulus (&3 / &4) (&2)
                      ==> c x = e(inv(norm x pow 2) % x)))`;;

(* The variant V1 (agreement on all of annulus(1/2,2)) is FALSE, see         *)
(* APX_SCHREQ_V1_FALSE below.                                                *)

let APX_SCHOENFLIES_REQ_V1_STATEMENT = new_definition
 `APX_SCHOENFLIES_REQ_V1_STATEMENT (u:A->bool) <=>
    !top atlas b e.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_ball_chart top atlas b /\ mfd_neck_chart top atlas e /\
        IMAGE e (annulus (&1 / &2) (&2)) SUBSET IMAGE b (ball(vec 0,&1))
        ==> ?c. mfd_ball_chart top atlas c /\
                IMAGE c (cball(vec 0,&1)) SUBSET IMAGE b (ball(vec 0,&1)) /\
                ((!x. x IN annulus (&1 / &2) (&2) ==> c x = e x) \/
                 (!x. x IN annulus (&1 / &2) (&2)
                      ==> c x = e(inv(norm x pow 2) % x)))`;;

(* ------------------------------------------------------------------------- *)
(* Sanity theorems in R^3 with the identity atlas.  (1) The hypotheses are   *)
(* satisfiable and the conclusion then holds (b the identity, e and c the    *)
(* scaling by 1/2), for the statement (APX_SCHREQ_INSTANCE) and for V1       *)
(* (APX_SCHREQ_V1_INSTANCE).  (2) Teeth: for the scaling by 4, whose image   *)
(* leaves b(ball(0,1)), no c exists, so the containment hypothesis is needed *)
(* and the conclusion is a real constraint (APX_SCHREQ_TEETH,                *)
(* APX_SCHREQ_V1_TEETH).                                                     *)
(* ------------------------------------------------------------------------- *)

let APX_SCHREQ_EUCLIDEAN = prove
 (`hausdorff_space (euclidean:(real^3)topology) /\
   smooth_manifold_atlas (euclidean:(real^3)topology) (open_set_atlas (:real^3))`,
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN
  MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let APX_SCHREQ_PARAM = prove
 (`!s t (f:real^3->real^3) g.
        diffeomorphism_on s t f g
        ==> mfd_param euclidean (open_set_atlas (:real^3)) s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_param; MFD_DIFFEO_EUCLIDEAN] THEN
  EXISTS_TAC `g:real^3->real^3` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              REWRITE_RULE[diffeomorphism_on]) THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let APX_SCHREQ_HALF = prove
 (`mfd_ball_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. inv(&2) % x) /\
   mfd_neck_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. inv(&2) % x)`,
  REWRITE_TAC[mfd_ball_chart; mfd_neck_chart] THEN CONJ_TAC THEN
  MATCH_MP_TAC APX_SCHREQ_PARAM THENL
   [MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,inv(&2) * &2)`; `\x:real^3. inv(inv(&2)) % x`] THEN
    MATCH_MP_TAC SMT_DIFFEO_SCALING_BALL;
    MAP_EVERY EXISTS_TAC [`annulus (inv(&2) * &1 / &2) (inv(&2) * &2):real^3->bool`;
                          `\x:real^3. inv(inv(&2)) % x`] THEN
    MATCH_MP_TAC SMT_DIFFEO_SCALING_ANNULUS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let APX_SCHREQ_V1_INSTANCE = prove
 (`hausdorff_space (euclidean:(real^3)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
   mfd_ball_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. x) /\
   mfd_neck_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. inv(&2) % x) /\
   IMAGE (\x:real^3. inv(&2) % x) (annulus (&1 / &2) (&2)) SUBSET
   IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
   ?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
       IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
       ((!x. x IN annulus (&1 / &2) (&2) ==> c x = (\x:real^3. inv(&2) % x) x) \/
        (!x. x IN annulus (&1 / &2) (&2)
             ==> c x = (\x:real^3. inv(&2) % x)(inv(norm x pow 2) % x)))`,
  REWRITE_TAC[APX_SCHREQ_EUCLIDEAN; APX_SCHREQ_HALF; IMAGE_ID] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `\x:real^3. x`] THEN
    SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM; IN_BALL_0; NORM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^3. inv(&2) % x` THEN REWRITE_TAC[APX_SCHREQ_HALF] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; IN_BALL_0; NORM_MUL] THEN
  REAL_ARITH_TAC);;

let APX_SCHREQ_V1_TEETH = prove
 (`mfd_neck_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. &4 % x) /\
   ~(?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
         IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
         ((!x. x IN annulus (&1 / &2) (&2) ==> c x = (\x:real^3. &4 % x) x) \/
          (!x. x IN annulus (&1 / &2) (&2)
               ==> c x = (\x:real^3. &4 % x)(inv(norm x pow 2) % x))))`,
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`annulus (&4 * &1 / &2) (&4 * &2):real^3->bool`;
                          `\x:real^3. inv(&4) % x`] THEN
    MATCH_MP_TAC SMT_DIFFEO_SCALING_ANNULUS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID; NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^3->real^3` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "sub")
    (LABEL_TAC "dis"))) THEN
  SUBGOAL_THEN `norm(&3 / &4 % basis 1:real^3) = &3 / &4` (LABEL_TAC "n") THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sub" (MP_TAC o SPEC `&3 / &4 % basis 1:real^3`) THEN
  USE_THEN "n" (fun th -> REWRITE_TAC[IN_CBALL_0; IN_BALL_0; th]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&3 / &4 % basis 1:real^3) IN annulus (&1 / &2) (&2)` (LABEL_TAC "a") THENL
   [USE_THEN "n" (fun th -> REWRITE_TAC[annulus; IN_ELIM_THM; th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dis" (DISJ_CASES_THEN (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `(&3 / &4 % basis 1:real^3) IN annulus (&1 / &2) (&2)`)))) THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `norm((c:real^3->real^3)(&3 / &4 % basis 1)) < &1` THEN
                       REWRITE_TAC[th]) THEN
  USE_THEN "n" (fun th -> REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The instance for the statement APX_SCHOENFLIES_REQ_STATEMENT. *)

let APX_SCHREQ_INSTANCE = prove
 (`hausdorff_space (euclidean:(real^3)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
   mfd_ball_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. x) /\
   mfd_neck_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. inv(&2) % x) /\
   IMAGE (\x:real^3. inv(&2) % x) (annulus (&1 / &2) (&2)) SUBSET
   IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
   ?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
       IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
       ((!x. x IN annulus (&3 / &4) (&2) ==> c x = (\x:real^3. inv(&2) % x) x) \/
        (!x. x IN annulus (&3 / &4) (&2)
             ==> c x = (\x:real^3. inv(&2) % x)(inv(norm x pow 2) % x)))`,
  REWRITE_TAC[APX_SCHREQ_EUCLIDEAN; APX_SCHREQ_HALF; IMAGE_ID] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `\x:real^3. x`] THEN
    SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM; IN_BALL_0; NORM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^3. inv(&2) % x` THEN REWRITE_TAC[APX_SCHREQ_HALF] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; IN_BALL_0; NORM_MUL] THEN
  REAL_ARITH_TAC);;

let APX_SCHREQ_TEETH = prove
 (`mfd_neck_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. &4 % x) /\
   ~(?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
         IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
         ((!x. x IN annulus (&3 / &4) (&2) ==> c x = (\x:real^3. &4 % x) x) \/
          (!x. x IN annulus (&3 / &4) (&2)
               ==> c x = (\x:real^3. &4 % x)(inv(norm x pow 2) % x))))`,
  CONJ_TAC THENL [REWRITE_TAC[CONJUNCT1 APX_SCHREQ_V1_TEETH]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID; NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^3->real^3` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "sub")
    (LABEL_TAC "dis"))) THEN
  SUBGOAL_THEN `norm(&7 / &8 % basis 1:real^3) = &7 / &8` (LABEL_TAC "n") THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sub" (MP_TAC o SPEC `&7 / &8 % basis 1:real^3`) THEN
  USE_THEN "n" (fun th -> REWRITE_TAC[IN_CBALL_0; IN_BALL_0; th]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&7 / &8 % basis 1:real^3) IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
   [USE_THEN "n" (fun th -> REWRITE_TAC[annulus; IN_ELIM_THM; th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dis" (DISJ_CASES_THEN (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `(&7 / &8 % basis 1:real^3) IN annulus (&3 / &4) (&2)`)))) THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `norm((c:real^3->real^3)(&7 / &8 % basis 1)) < &1` THEN
                       REWRITE_TAC[th]) THEN
  USE_THEN "n" (fun th -> REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The inversion alternative is needed (shown for V1, whose agreement      *)
(* annulus is annulus(1/2,2); APX_SCHOENFLIES_REQ_STATEMENT has the same   *)
(* disjunct).                                                              *)

let APX_SCHREQ_INV_DIFFEO = prove
 (`diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 / &4) (&1))
     (\x:real^3. inv(&2) % inv(norm x pow 2) % x)
     ((\x. inv(norm x pow 2) % x) o (\x:real^3. inv(inv(&2)) % x))`,
  SUBGOAL_THEN `(\x:real^3. inv(&2) % inv(norm x pow 2) % x) =
                (\x. inv(&2) % x) o (\x:real^3. inv(norm x pow 2) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (inv(&2)) (inv(&1 / &2)):real^3->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEO_INVERSION_ANNULUS THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `annulus (&1 / &4) (&1):real^3->bool =
                  annulus (inv(&2) * inv(&2)) (inv(&2) * inv(&1 / &2))`
    SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REFL_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMT_DIFFEO_SCALING_ANNULUS THEN REAL_ARITH_TAC]);;

let APX_SCHREQ_V1_INVERTED = prove
 (`mfd_neck_chart euclidean (open_set_atlas (:real^3))
     (\x:real^3. inv(&2) % inv(norm x pow 2) % x) /\
   IMAGE (\x:real^3. inv(&2) % inv(norm x pow 2) % x) (annulus (&1 / &2) (&2)) SUBSET
   IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
   (?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
        IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
        (!x. x IN annulus (&1 / &2) (&2)
             ==> c x = (\x:real^3. inv(&2) % inv(norm x pow 2) % x)
                         (inv(norm x pow 2) % x))) /\
   ~(?c. mfd_ball_chart euclidean (open_set_atlas (:real^3)) c /\
         IMAGE c (cball(vec 0,&1)) SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1)) /\
         (!x. x IN annulus (&1 / &2) (&2)
              ==> c x = (\x:real^3. inv(&2) % inv(norm x pow 2) % x) x))`,
  REWRITE_TAC[IMAGE_ID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC
     [`annulus (&1 / &4) (&1):real^3->bool`;
      `(\x. inv(norm x pow 2) % x) o (\x:real^3. inv(inv(&2)) % x)`] THEN
    REWRITE_TAC[APX_SCHREQ_INV_DIFFEO];
    MP_TAC APX_SCHREQ_INV_DIFFEO THEN REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
    EXISTS_TAC `\x:real^3. inv(&2) % x` THEN REWRITE_TAC[APX_SCHREQ_HALF] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; IN_BALL_0; NORM_MUL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^3->real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[mfd_ball_chart; mfd_param; MFD_DIFFEO_EUCLIDEAN; diffeomorphism_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^3->real^3) continuous_on ball(vec 0,&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure(annulus (&1 / &2) (&1):real^3->bool) SUBSET
                cball(vec 0,&1) DIFF ball(vec 0,&1 / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    SIMP_TAC[CLOSED_DIFF; CLOSED_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(INST [`annulus (&1 / &2) (&1):real^3->bool`,`s:real^3->bool`]
    (ISPECL [`c:real^3->real^3`; `\x:real^3. inv(&2) % inv(norm x pow 2) % x`]
            (INST_TYPE [`:3`,`:M`; `:3`,`:N`] CONTINUOUS_AGREE_ON_CLOSURE))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(vec 0:real^3,&1) DIFF ball(vec 0,&1 / &2)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        REWRITE_TAC[SMOOTH_MAP_ON_INVERSION];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `cball(vec 0:real^3,&1) DIFF ball(vec 0,&1 / &2)` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `norm(vec 0:real^3) <= &1 /\ ~(norm(vec 0:real^3) < &1 / &2)` THEN
        REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2 % basis 1:real^3`) THEN ANTS_TAC THENL
   [REWRITE_TAC[CLOSURE_APPROACHABLE; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(&1 / &2 + min d (&1 / &4) / &2) % basis 1:real^3` THEN
    SIMP_TAC[dist; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; GSYM VECTOR_SUB_RDISTRIB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^3. inv(&2) % inv(norm x pow 2) % x) (&1 / &2 % basis 1) =
                basis 1` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1)) SUBSET ball(vec 0,&1)` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2 % basis 1:real^3`) THEN
  ASM_REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The refutation of V1.  The degenerate neck chart e0 x = (1/2 - 1/(4|x|))  *)
(* x maps annulus(1/2,2) diffeomorphically onto the punctured ball           *)
(* annulus(0,3/4).  No ball chart agrees with e0 on all of annulus(1/2,2)    *)
(* (it would collapse sphere(1/2) to the origin), and none agrees with e0 o  *)
(* inversion there (its values on ball(0,1/2) would have to avoid the        *)
(* punctured ball of radius 3/4 while |c| is at most 3/4 on cball(0,1/2)).   *)
(* APX_SCHREQ_COUNTER_HYPS: e0 satisfies all hypotheses of                   *)
(* APX_SCHOENFLIES_REQ_STATEMENT, so that statement avoids the               *)
(* counterexample by its weaker agreement clause, not by a vacuous           *)
(* restriction of its hypotheses.                                            *)
(* ------------------------------------------------------------------------- *)

let APX_SCHREQ_CE_SMOOTH1 = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0)} (\x. (inv(&2) - inv(&4 * norm x)) % x)`,
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`;
                 `\x:real^3. lift(inv(&2) - inv(&4 * norm x))`;
                 `\x:real^3. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\x:real^3. lift(inv(&2))`;
                 `\x:real^3. lift(inv(&4 * norm x))`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\x:real^3. lift(&4 * norm x)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `&4`; `\x:real^3. lift(norm x)`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO];
    REWRITE_TAC[REAL_ENTIRE; NORM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ]]);;

let APX_SCHREQ_CE_SMOOTH2 = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0)} (\y. (&2 + inv(&2 * norm y)) % y)`,
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`;
                 `\y:real^3. lift(&2 + inv(&2 * norm y))`;
                 `\y:real^3. y`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\y:real^3. lift(&2)`;
                 `\y:real^3. lift(inv(&2 * norm y))`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\y:real^3. lift(&2 * norm y)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `&2`; `\y:real^3. lift(norm y)`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO];
    REWRITE_TAC[REAL_ENTIRE; NORM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ]]);;

let APX_SCHREQ_CE_NORM1 = prove
 (`!x:real^3. &1 / &2 < norm x
              ==> norm((inv(&2) - inv(&4 * norm x)) % x) = norm x / &2 - &1 / &4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < inv(&2) - inv(&4 * norm(x:real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let APX_SCHREQ_CE_NORM2 = prove
 (`!y:real^3. &0 < norm y
              ==> norm((&2 + inv(&2 * norm y)) % y) = &2 * norm y + &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < &2 + inv(&2 * norm(y:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < &2 + b`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let APX_SCHREQ_CE_DIFFEO = prove
 (`diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&0) (&3 / &4))
     (\x:real^3. (inv(&2) - inv(&4 * norm x)) % x)
     (\y. (&2 + inv(&2 * norm y)) % y)`,
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN REWRITE_TAC[APX_SCHREQ_CE_SMOOTH1] THEN
    MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN REWRITE_TAC[APX_SCHREQ_CE_SMOOTH2] THEN
    MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[APX_SCHREQ_CE_NORM1] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(x:real^3) = &0) /\ ~(&2 * norm(x:real^3) - &1 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[APX_SCHREQ_CE_NORM2] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &0) /\ ~(&4 * norm(y:real^3) + &1 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let APX_SCHREQ_HALF_SPHERE_CLOSURE = prove
 (`!y:real^3. norm y = &1 / &2 ==> y IN closure(annulus (&1 / &2) (&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(&1 + min d (&1 / &2)) % y:real^3` THEN
  REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH `(&1 + t) % y - y:real^N = t % y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_SCHREQ_HALF_CLOSURE_SUBSET = prove
 (`closure(annulus (&1 / &2) (&1)) SUBSET
   {x:real^3 | ~(x = vec 0)} INTER ball(vec 0,&2)`,
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `cball(vec 0:real^3,&1) DIFF ball(vec 0,&1 / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    SIMP_TAC[CLOSED_DIFF; CLOSED_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(norm(vec 0:real^3) < &1 / &2)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let APX_SCHREQ_CE_INV_SMOOTH = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0)}
     (\x. (inv(&2) - inv(&4 * norm(inv(norm x pow 2) % x))) % (inv(norm x pow 2) % x))`,
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `{x:real^3 | ~(x = vec 0)}`;
                 `\x:real^3. inv(norm x pow 2) % x`;
                 `\x:real^3. (inv(&2) - inv(&4 * norm x)) % x`]
    SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_INVERSION; APX_SCHREQ_CE_SMOOTH1; o_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0]);;

let APX_SCHREQ_CE_INV_HALF = prove
 (`!y:real^3. norm y = &1 / &2
              ==> (inv(&2) - inv(&4 * norm(inv(norm y pow 2) % y))) %
                  (inv(norm y pow 2) % y) = &3 / &2 % y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1 / &2` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_INVERSION_NORM; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let APX_SCHREQ_CE_COVER = prove
 (`!w:real^3. w IN annulus (&0) (&3 / &4)
              ==> ?x. x IN annulus (&1 / &2) (&2) /\
                      (inv(&2) - inv(&4 * norm(inv(norm x pow 2) % x))) %
                      (inv(norm x pow 2) % x) = w`,
  REPEAT STRIP_TAC THEN MP_TAC APX_SCHREQ_CE_DIFFEO THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `v:real^3 = (&2 + inv(&2 * norm w)) % w` THEN
  SUBGOAL_THEN `(v:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(inv(&2) - inv(&4 * norm(v:real^3))) % v = w` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(vec 0:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(norm v pow 2) % v:real^3` THEN
  ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION] THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[diffeomorphism_on] THEN
  STRIP_TAC THEN ASM SET_TAC[]);;

(* Ball charts of real^3 with the identity atlas. *)

let APX_SCHREQ_EUCLID_BALL_CHART = prove
 (`!c:real^3->real^3.
        mfd_ball_chart euclidean (open_set_atlas (:real^3)) c
        ==> c continuous_on ball(vec 0,&2) /\
            (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y
                   ==> x = y) /\
            (!u. open u /\ u SUBSET ball(vec 0,&2) ==> open(IMAGE c u))`,
  GEN_TAC THEN
  REWRITE_TAC[mfd_ball_chart; mfd_param; MFD_DIFFEO_EUCLIDEAN; diffeomorphism_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->real^3` STRIP_ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (c:real^3->real^3) u =
                  {y | y IN IMAGE c (ball(vec 0,&2)) /\ c' y IN u}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[SUBSET];
        STRIP_TAC THEN EXISTS_TAC `(c':real^3->real^3) y` THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]]]);;

let APX_SCHREQ_V1_CASE_A = prove
 (`!c:real^3->real^3.
        mfd_ball_chart euclidean (open_set_atlas (:real^3)) c
        ==> ~(!x. x IN annulus (&1 / &2) (&2)
                  ==> c x = (inv(&2) - inv(&4 * norm x)) % x)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INJ")
    ASSUME_TAC) o MATCH_MP APX_SCHREQ_EUCLID_BALL_CHART) THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  MP_TAC(INST [`annulus (&1 / &2) (&1):real^3->bool`,`s:real^3->bool`]
    (ISPECL [`c:real^3->real^3`; `\x:real^3. (inv(&2) - inv(&4 * norm x)) % x`]
            (INST_TYPE [`:3`,`:M`; `:3`,`:N`] CONTINUOUS_AGREE_ON_CLOSURE))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC APX_SCHREQ_HALF_CLOSURE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[APX_SCHREQ_CE_SMOOTH1];
        MP_TAC APX_SCHREQ_HALF_CLOSURE_SUBSET THEN SET_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      USE_THEN "H" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "AC") THEN
  SUBGOAL_THEN `norm(&1 / &2 % basis 1:real^3) = &1 / &2 /\
                norm(--(&1 / &2 % basis 1):real^3) = &1 / &2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_NEG] THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3)(&1 / &2 % basis 1) = vec 0 /\
                (c:real^3->real^3)(--(&1 / &2 % basis 1)) = vec 0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    USE_THEN "AC" (fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(lhand w)) th))) THEN
    ASM_SIMP_TAC[APX_SCHREQ_HALF_SPHERE_CLOSURE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  USE_THEN "INJ" (MP_TAC o SPECL [`&1 / &2 % basis 1:real^3`;
                                  `--(&1 / &2 % basis 1):real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `a:real^N = --a <=> a = vec 0`; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let APX_SCHREQ_V1_CASE_B = prove
 (`!c:real^3->real^3.
        mfd_ball_chart euclidean (open_set_atlas (:real^3)) c
        ==> ~(!x. x IN annulus (&1 / &2) (&2)
                  ==> c x = (inv(&2) - inv(&4 * norm(inv(norm x pow 2) % x))) %
                            (inv(norm x pow 2) % x))`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INJ")
    (LABEL_TAC "OPEN2")) o MATCH_MP APX_SCHREQ_EUCLID_BALL_CHART) THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  (* Step 1: c = 3/2 % y on sphere(1/2), by continuity. *)
  SUBGOAL_THEN `!y:real^3. norm y = &1 / &2 ==> (c:real^3->real^3) y = &3 / &2 % y`
  (LABEL_TAC "SPH") THENL
   [MP_TAC(INST [`annulus (&1 / &2) (&1):real^3->bool`,`s:real^3->bool`]
      (ISPECL [`c:real^3->real^3`;
               `\x:real^3. (inv(&2) - inv(&4 * norm(inv(norm x pow 2) % x))) %
                           (inv(norm x pow 2) % x)`]
              (INST_TYPE [`:3`,`:M`; `:3`,`:N`] CONTINUOUS_AGREE_ON_CLOSURE))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
        ASM_REWRITE_TAC[] THEN MP_TAC APX_SCHREQ_HALF_CLOSURE_SUBSET THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[APX_SCHREQ_CE_INV_SMOOTH];
          MP_TAC APX_SCHREQ_HALF_CLOSURE_SUBSET THEN SET_TAC[]];
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
        USE_THEN "H" MATCH_MP_TAC THEN
        UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN
    ASM_SIMP_TAC[APX_SCHREQ_HALF_SPHERE_CLOSURE; APX_SCHREQ_CE_INV_HALF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. open u /\ u SUBSET ball(vec 0,&1 / &2)
                    ==> open(IMAGE (c:real^3->real^3) u)` (LABEL_TAC "OPEN") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "OPEN2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN IMAGE (c:real^3->real^3) (ball(vec 0,&1 / &2))
                    ==> ?e. &0 < e /\ ball(z,e) SUBSET IMAGE c (ball(vec 0,&1 / &2))`
  (LABEL_TAC "NBHD") THENL
   [USE_THEN "OPEN" (MP_TAC o SPEC `ball(vec 0:real^3,&1 / &2)`) THEN
    REWRITE_TAC[OPEN_BALL; SUBSET_REFL] THEN REWRITE_TAC[OPEN_CONTAINS_BALL];
    ALL_TAC] THEN
  (* Step 2: |c| attains its maximum on cball(0,1/2). *)
  MP_TAC(ISPECL [`\x:real^3. norm((c:real^3->real^3) x)`; `cball(vec 0:real^3,&1 / &2)`]
    CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MAX"))) THEN
  (* Step 3: the maximum is at least 3/4. *)
  SUBGOAL_THEN `&3 / &4 <= norm((c:real^3->real^3) x1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(&1 / &2 % basis 1:real^3) = &1 / &2` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((c:real^3->real^3)(&1 / &2 % basis 1))` THEN CONJ_TAC THENL
     [USE_THEN "SPH" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `norm(&1 / &2 % basis 1:real^3) = &1 / &2`)]) THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      USE_THEN "MAX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* Step 4: it is attained on sphere(1/2), so it equals 3/4. *)
  SUBGOAL_THEN `norm(x1:real^3) = &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a /\ ~(x < a) ==> x = a`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "NBHD" (MP_TAC o SPEC `(c:real^3->real^3) x1`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `n = norm((c:real^3->real^3) x1)` THEN
    SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((&1 + r / (&2 * n)) % (c:real^3->real^3) x1) IN
                  IMAGE c (ball(vec 0,&1 / &2))` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist;
        VECTOR_ARITH `x - (&1 + t) % x:real^N = --(t % x)`; NORM_NEG; NORM_MUL] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs(r / (&2 * n)) * n = r / &2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`;
                     REAL_ARITH `abs(&2) = &2`] THEN
        UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "MAX" (MP_TAC o SPEC `x':real^3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[NORM_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < r / (&2 * n)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs(&1 + t) = &1 + t`] THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < b ==> a < a + b`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((c:real^3->real^3) x1) = &3 / &4` ASSUME_TAC THENL
   [USE_THEN "SPH" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `norm(x1:real^3) = &1 / &2`)]) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. norm y <= &1 / &2 ==> norm((c:real^3->real^3) y) <= &3 / &4`
  (LABEL_TAC "BD") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((c:real^3->real^3) x1)` THEN CONJ_TAC THENL
     [USE_THEN "MAX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* Step 5: c(0) is the centre of a ball inside IMAGE c ball(0,1/2) that meets *)
  (* the punctured ball annulus(0,3/4) = c(annulus(1/2,2)).                      *)
  USE_THEN "NBHD" (MP_TAC o SPEC `(c:real^3->real^3)(vec 0)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm((c:real^3->real^3)(vec 0)) <= &3 / &4` ASSUME_TAC THENL
   [USE_THEN "BD" MATCH_MP_TAC THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. w IN ball((c:real^3->real^3)(vec 0),r) /\
                           w IN annulus (&0) (&3 / &4)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(c:real^3->real^3)(vec 0) = vec 0` THENL
     [EXISTS_TAC `(min r (&1 / &2) / &2) % basis 1:real^3` THEN
      ASM_REWRITE_TAC[IN_BALL; annulus; IN_ELIM_THM; DIST_0] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((c:real^3->real^3)(vec 0))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ABBREV_TAC `t = min (r / (&2 * norm((c:real^3->real^3)(vec 0)))) (&1 / &2)` THEN
    SUBGOAL_THEN `&0 < t /\ t <= &1 / &2 /\
                  t * norm((c:real^3->real^3)(vec 0)) <= r / &2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `r / (&2 * norm((c:real^3->real^3)(vec 0))) *
                    norm((c:real^3->real^3)(vec 0))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < norm((c:real^3->real^3)(vec 0))` THEN
          CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    EXISTS_TAC `(&1 - t) % (c:real^3->real^3)(vec 0)` THEN
    REWRITE_TAC[IN_BALL; annulus; IN_ELIM_THM; dist;
      VECTOR_ARITH `z - (&1 - t) % z:real^N = t % z`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`;
                 REAL_ARITH `t <= &1 / &2 ==> abs(&1 - t) = &1 - t`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `norm((c:real^3->real^3)(vec 0))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < t * n ==> (&1 - t) * n < n`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN IMAGE (c:real^3->real^3) (ball(vec 0,&1 / &2))` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP APX_SCHREQ_CE_COVER (ASSUME `(w:real^3) IN annulus (&0) (&3 / &4)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x'':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^3->real^3) x'' = w` ASSUME_TAC THENL
   [USE_THEN "H" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(x'':real^3) IN annulus (&1 / &2) (&2)`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `(x'':real^3) IN annulus (&1 / &2) (&2)`) THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "INJ" (MP_TAC o SPECL [`x':real^3`; `x'':real^3`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC]);;

let APX_SCHREQ_V1_FALSE = prove
 (`!u:real^3->bool. ~(APX_SCHOENFLIES_REQ_V1_STATEMENT u)`,
  GEN_TAC THEN REWRITE_TAC[APX_SCHOENFLIES_REQ_V1_STATEMENT; NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY EXISTS_TAC
   [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `\x:real^3. x`;
    `\x:real^3. (inv(&2) - inv(&4 * norm x)) % x`] THEN
  REWRITE_TAC[APX_SCHREQ_EUCLIDEAN; IMAGE_ID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `\x:real^3. x`] THEN
    SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_BALL];
    REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`annulus (&0) (&3 / &4):real^3->bool`;
                          `\y:real^3. (&2 + inv(&2 * norm y)) % y`] THEN
    REWRITE_TAC[APX_SCHREQ_CE_DIFFEO];
    MP_TAC APX_SCHREQ_CE_DIFFEO THEN REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^3->real^3` THEN
    STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
     [ASM_MESON_TAC[APX_SCHREQ_V1_CASE_A]; ASM_MESON_TAC[APX_SCHREQ_V1_CASE_B]]]);;

let APX_SCHREQ_COUNTER_HYPS = prove
 (`hausdorff_space (euclidean:(real^3)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
   mfd_ball_chart euclidean (open_set_atlas (:real^3)) (\x:real^3. x) /\
   mfd_neck_chart euclidean (open_set_atlas (:real^3))
     (\x:real^3. (inv(&2) - inv(&4 * norm x)) % x) /\
   IMAGE (\x:real^3. (inv(&2) - inv(&4 * norm x)) % x) (annulus (&1 / &2) (&2))
   SUBSET IMAGE (\x:real^3. x) (ball(vec 0,&1))`,
  REWRITE_TAC[APX_SCHREQ_EUCLIDEAN; IMAGE_ID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `\x:real^3. x`] THEN
    SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_BALL];
    REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC APX_SCHREQ_PARAM THEN
    MAP_EVERY EXISTS_TAC [`annulus (&0) (&3 / &4):real^3->bool`;
                          `\y:real^3. (&2 + inv(&2 * norm y)) % y`] THEN
    REWRITE_TAC[APX_SCHREQ_CE_DIFFEO];
    MP_TAC APX_SCHREQ_CE_DIFFEO THEN REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC]);;

