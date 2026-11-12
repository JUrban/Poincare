(* ========================================================================= *)
(* pc_moi_s31_rev: solid tori of revolution, the input of 30.7 and 30.8 in  *)
(* Moise 31.1 and 31.4 (GTM 47, printed p.220).  Main theorem REV_SHELL :   *)
(* |- MOI_S31_REV_SHELL (statement of pc_moi_s3032_stmt).  Route:           *)
(* revolution X is the image of X PCROSS the unit circle under rot; for a   *)
(* disk chart f of dd the sets h(rev f(cball(0,r))) are homeomorphic images *)
(* of cball PCROSS sphere, so solid tori whose interiors and frontiers are  *)
(* read off from the model of pc_moi_s30_tor_a                              *)
(* (MOI_S3TA_SOLID_TORUS_INTERIOR); the annulus between radii r and 1 gives *)
(* the toroidal shell; the spine case re-centres the chart by               *)
(* HOMEOMORPHISM_MOVING_POINT_EXISTS.                                       *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s30_tor_a.ml";;   (* MOI_S3TA_SOLID_TORUS_INTERIOR *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the rotation about the x2 axis, revolution as the image of       *)
(* X PCROSS the unit circle for X in the half plane x3 = 0, 0 < x1, its     *)
(* injectivity there, continuity, and monotonicity of revolution.           *)
(* ========================================================================= *)

let moi_s3rv_rot = new_definition
 `moi_s3rv_rot (q:real^3) (z:real^2) =
    vector[q$1 * z$1; q$2; q$1 * z$2]:real^3`;;

let MOI_S3RV_ROT_COMPONENTS = prove
 (`!(q:real^3) (z:real^2).
     moi_s3rv_rot q z$1 = q$1 * z$1 /\ moi_s3rv_rot q z$2 = q$2 /\
     moi_s3rv_rot q z$3 = q$1 * z$2`,
  REWRITE_TAC[moi_s3rv_rot; VECTOR_3]);;

let MOI_S3RV_UNIT2 = prove
 (`!z:real^2. norm z = &1 <=> z$1 pow 2 + z$2 pow 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_1; DOT_2] THEN REAL_ARITH_TAC);;

let MOI_S3RV_REV_IMAGE = prove
 (`!x:real^3->bool.
     x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}
     ==> revolution x =
         IMAGE (\p:real^(3,2)finite_sum. moi_s3rv_rot (fstcart p) (sndcart p))
               (x PCROSS sphere(vec 0:real^2,&1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; revolution; IN_ELIM_THM; IN_IMAGE; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; IN_SPHERE_0] THEN
  X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < (q:real^3)$1` ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^3) IN x` THEN
      UNDISCH_TAC `x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`q:real^3`; `vector[(p:real^3)$1 / (q:real^3)$1; p$3 / q$1]:real^2`] THEN
    ASM_REWRITE_TAC[MOI_S3RV_UNIT2; VECTOR_2] THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_S3RV_ROT_COMPONENTS; VECTOR_2] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < (q:real^3)$1` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `(q:real^3)$1 pow 2 = (p:real^3)$1 pow 2 + p$3 pow 2` THEN
      UNDISCH_TAC `&0 < (q:real^3)$1` THEN CONV_TAC REAL_FIELD];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:real^3`; `z:real^2`] THEN STRIP_TAC THEN
    EXISTS_TAC `q:real^3` THEN
    SUBGOAL_THEN `(q:real^3)$3 = &0 /\ &0 < q$1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^3) IN x` THEN
      UNDISCH_TAC `x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_S3RV_ROT_COMPONENTS] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `norm(z:real^2) = &1` THEN REWRITE_TAC[MOI_S3RV_UNIT2] THEN
      CONV_TAC REAL_RING]]);;

let MOI_S3RV_ROT_INJ = prove
 (`!(q:real^3) (z:real^2) (q':real^3) (z':real^2).
     q$3 = &0 /\ &0 < q$1 /\ q'$3 = &0 /\ &0 < q'$1 /\
     norm z = &1 /\ norm z' = &1 /\ moi_s3rv_rot q z = moi_s3rv_rot q' z'
     ==> q = q' /\ z = z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3RV_UNIT2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CART_EQ; DIMINDEX_3; FORALL_3;
    MOI_S3RV_ROT_COMPONENTS]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3)$1 = (q':real^3)$1` ASSUME_TAC THENL
   [SUBGOAL_THEN `((q:real^3)$1) pow 2 = ((q':real^3)$1) pow 2` MP_TAC THENL
     [SUBGOAL_THEN
       `((q:real^3)$1) pow 2 = (q$1 * (z:real^2)$1) pow 2 + (q$1 * z$2) pow 2 /\
        ((q':real^3)$1) pow 2 = (q'$1 * (z':real^2)$1) pow 2 + (q'$1 * z'$2) pow 2`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(z:real^2)$1 pow 2 + z$2 pow 2 = &1`;
          UNDISCH_TAC `(z':real^2)$1 pow 2 + z'$2 pow 2 = &1`] THEN
        CONV_TAC REAL_RING;
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    MAP_EVERY UNDISCH_TAC
     [`(q:real^3)$1 * (z:real^2)$1 = (q':real^3)$1 * (z':real^2)$1`;
      `(q:real^3)$1 * (z:real^2)$2 = (q':real^3)$1 * (z':real^2)$2`;
      `(q:real^3)$1 = (q':real^3)$1`; `&0 < (q:real^3)$1`] THEN
    CONV_TAC REAL_FIELD]);;

let MOI_S3RV_ROT_CONTINUOUS = prove
 (`!s. (\p:real^(3,2)finite_sum. moi_s3rv_rot (fstcart p) (sndcart p)) continuous_on s`,
  GEN_TAC THEN GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN
   `(\x:real^(3,2)finite_sum. lift(fstcart x$1)) continuous_on s /\
    (\x:real^(3,2)finite_sum. lift(fstcart x$2)) continuous_on s /\
    (\x:real^(3,2)finite_sum. lift(sndcart x$1)) continuous_on s /\
    (\x:real^(3,2)finite_sum. lift(sndcart x$2)) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOI_S3RV_ROT_COMPONENTS; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let MOI_S3RV_REV_MONO = prove
 (`!x y:real^3->bool. x SUBSET y ==> revolution x SUBSET revolution y`,
  REWRITE_TAC[SUBSET; revolution; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3RV_HALF_PLANE_SUBSET = prove
 (`!x y:real^3->bool.
     x SUBSET y /\ y SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}
     ==> x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}`,
  SET_TAC[]);;

(* ========================================================================= *)
(* Part 2: the chart lemma.  For a disk chart (f,g) of dd in the half       *)
(* plane and an embedding h of revolution dd, the set                        *)
(* h(rev f(cball(0,r))) (0 < r <= 1) is the homeomorphic image of           *)
(* cball(0,1) PCROSS sphere(0,1) under (v,z) -> h(rot(f(r v),z)); hence it  *)
(* is a solid torus, its interior is h(rev f(ball(0,r)))                    *)
(* (MOI_S3TA_SOLID_TORUS_INTERIOR of pc_moi_s30_tor_a) and its frontier     *)
(* h(rev f(sphere(0,r))).                                                   *)
(* ========================================================================= *)

let MOI_S3RV_SCALE_IMAGES = prove
 (`!r. &0 < r
       ==> IMAGE (\x:real^2. r % x) (cball(vec 0,&1)) = cball(vec 0,r) /\
           IMAGE (\x:real^2. r % x) (ball(vec 0,&1)) = ball(vec 0,r) /\
           IMAGE (\x:real^2. r % x) (sphere(vec 0,&1)) = sphere(vec 0,r)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] (MATCH_MP CBALL_SCALING (ASSUME `&0 < r`))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] (MATCH_MP BALL_SCALING (ASSUME `&0 < r`))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] (MATCH_MP SPHERE_SCALING (ASSUME `&0 < r`))) THEN
  REWRITE_TAC[REAL_MUL_RID; VECTOR_MUL_RZERO] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[]);;

let MOI_S3RV_SCALE_CBALL = prove
 (`!r (v:real^2). &0 <= r /\ r <= &1 /\ v IN cball(vec 0,&1) ==> r % v IN cball(vec 0,&1)`,
  REWRITE_TAC[IN_CBALL_0; NORM_MUL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The parametrisation and its images. *)

let MOI_S3RV_PHI_IMAGE = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r a.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     &0 <= r /\ r <= &1 /\ a SUBSET cball(vec 0:real^2,&1)
     ==> IMAGE (\p:real^(2,2)finite_sum.
                  h(moi_s3rv_rot (f(r % fstcart p)) (sndcart p)))
               (a PCROSS sphere(vec 0:real^2,&1)) =
         IMAGE h (revolution (IMAGE f (IMAGE (\x:real^2. r % x) a)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) (IMAGE (\x:real^2. r % x) a) SUBSET
                {q:real^3 | q$3 = &0 /\ &0 < q$1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `dd:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) (cball(vec 0,&1)) = dd` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S3RV_SCALE_CBALL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN a` THEN UNDISCH_TAC `a SUBSET cball(vec 0:real^2,&1)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3RV_REV_IMAGE] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

(* Points of the parametrisation lie in revolution dd. *)

let MOI_S3RV_PHI_IN = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g r v z.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     &0 <= r /\ r <= &1 /\ v IN cball(vec 0:real^2,&1) /\ z IN sphere(vec 0:real^2,&1)
     ==> r % v IN cball(vec 0:real^2,&1) /\ f(r % v) IN dd /\
         moi_s3rv_rot (f(r % v)) z IN revolution dd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r % v IN cball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3RV_SCALE_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^3)(r % v) IN dd` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^3) (cball(vec 0,&1)) = dd` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `dd:real^3->bool` MOI_S3RV_REV_IMAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART] THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^3) (r % v)`; `z:real^2`] THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS]);;

let MOI_S3RV_PHI_CONTINUOUS = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\ &0 <= r /\ r <= &1
     ==> (\p:real^(2,2)finite_sum. h(moi_s3rv_rot (f(r % fstcart p)) (sndcart p)))
         continuous_on (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. h(moi_s3rv_rot (f(r % fstcart p)) (sndcart p))) =
    (h:real^3->real^3) o
    ((\p:real^(3,2)finite_sum. moi_s3rv_rot (fstcart p) (sndcart p)) o
     ((\p:real^(2,2)finite_sum. pastecart ((f:real^2->real^3)(r % fstcart p)) (sndcart p))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. pastecart ((f:real^2->real^3)(r % fstcart p)) (sndcart p))
    continuous_on (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\p:real^(2,2)finite_sum. (f:real^2->real^3)(r % fstcart p)) =
                    f o (\p. r % fstcart p)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `cball(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3RV_SCALE_CBALL THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[MOI_S3RV_ROT_CONTINUOUS];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `revolution dd:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; FORALL_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`v:real^2`; `z:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`; `r:real`;
                   `v:real^2`; `z:real^2`] MOI_S3RV_PHI_IN) THEN
    ASM_SIMP_TAC[]]);;

let MOI_S3RV_PHI_INJ = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r v z v' z'.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     &0 < r /\ r <= &1 /\
     v IN cball(vec 0:real^2,&1) /\ z IN sphere(vec 0:real^2,&1) /\
     v' IN cball(vec 0:real^2,&1) /\ z' IN sphere(vec 0:real^2,&1) /\
     h(moi_s3rv_rot (f(r % v)) z) = h(moi_s3rv_rot (f(r % v')) z')
     ==> v = v' /\ z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`; `r:real`;
                 `v:real^2`; `z:real^2`] MOI_S3RV_PHI_IN) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`; `r:real`;
                 `v':real^2`; `z':real^2`] MOI_S3RV_PHI_IN) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3rv_rot ((f:real^2->real^3)(r % v)) z = moi_s3rv_rot (f(r % v')) z'`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `h:real^3->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^2->real^3)(r % v)`; `z:real^2`; `(f:real^2->real^3)(r % v')`;
                 `z':real^2`] MOI_S3RV_ROT_INJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM IN_SPHERE_0] THEN
    MAP_EVERY UNDISCH_TAC [`(f:real^2->real^3)(r % v) IN dd`;
                           `(f:real^2->real^3)(r % v') IN dd`;
                           `dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1}`] THEN
    SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `r % v:real^2 = r % v'` MP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MP_TAC(MP (SPEC `r % v:real^2` (ASSUME
      `!x:real^2. x IN cball(vec 0,&1) ==> (g:real^3->real^2) (f x) = x`))
      (ASSUME `r % v IN cball(vec 0:real^2,&1)`)) THEN
    MP_TAC(MP (SPEC `r % v':real^2` (ASSUME
      `!x:real^2. x IN cball(vec 0,&1) ==> (g:real^3->real^2) (f x) = x`))
      (ASSUME `r % v' IN cball(vec 0:real^2,&1)`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]]);;

let MOI_S3RV_CHART_HOMEO = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     &0 < r /\ r <= &1
     ==> ?psi. homeomorphism
                 (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),
                  IMAGE h (revolution (IMAGE f (cball(vec 0,r)))))
                 ((\p:real^(2,2)finite_sum.
                     h(moi_s3rv_rot (f(r % fstcart p)) (sndcart p))),psi)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE];
    MATCH_MP_TAC MOI_S3RV_PHI_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`dd:real^3->bool`; `g:real^3->real^2`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                   `h:real^3->real^3`; `r:real`; `cball(vec 0:real^2,&1)`]
      MOI_S3RV_PHI_IMAGE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SUBSET_REFL; MOI_S3RV_SCALE_IMAGES];
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3RV_PHI_INJ THEN
    MAP_EVERY EXISTS_TAC [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                          `h:real^3->real^3`; `r:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* The solid torus of a chart and radius, its interior, frontier and spines. *)

let MOI_S3RV_IMAGE_DIFF_INJ = prove
 (`!(f:A->B) g s t u.
     (!x. x IN s ==> g (f x) = x) /\ t SUBSET s /\ u SUBSET s
     ==> IMAGE f t DIFF IMAGE f u = IMAGE f (t DIFF u)`,
  SET_TAC[]);;

let MOI_S3RV_CHART_FACTS = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     &0 < r /\ r <= &1
     ==> solid_torus (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))) /\
         compact (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))) /\
         interior (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))) =
         IMAGE h (revolution (IMAGE f (ball(vec 0,r)))) /\
         frontier (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))) =
         IMAGE h (revolution (IMAGE f (sphere(vec 0,r)))) /\
         (!p. p IN ball(vec 0:real^2,&1)
              ==> spine (IMAGE h (revolution {f(r % p)}))
                        (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^(2,2)finite_sum` ASSUME_TAC) THEN
  ABBREV_TAC `phi = \p:real^(2,2)finite_sum.
                      (h:real^3->real^3)(moi_s3rv_rot ((f:real^2->real^3)(r % fstcart p))
                                                      (sndcart p))` THEN
  SUBGOAL_THEN
   `!a. a SUBSET cball(vec 0:real^2,&1)
        ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
            IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3)
                                                   (IMAGE (\x:real^2. r % x) a)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "phi" THEN MATCH_MP_TAC MOI_S3RV_PHI_IMAGE THEN
    EXISTS_TAC `dd:real^3->bool` THEN EXISTS_TAC `g:real^3->real^2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S3RV_SCALE_IMAGES (ASSUME `&0 < r`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (phi:real^(2,2)finite_sum->real^3) (ball(vec 0:real^2,&1) PCROSS sphere(vec 0,&1)) =
    IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) (ball(vec 0,r)))) /\
    IMAGE (phi:real^(2,2)finite_sum->real^3) (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0,&1)) =
    IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) (sphere(vec 0,r))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `ball(vec 0:real^2,&1)` th) THEN
                            MP_TAC(SPEC `sphere(vec 0:real^2,&1)` th) THEN
                            ASSUME_TAC th) THEN
    REWRITE_TAC[BALL_SUBSET_CBALL; SPHERE_SUBSET_CBALL] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (find_term ((=) `psi:real^3->real^(2,2)finite_sum`)) (concl th))) THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3)
                                                        (cball(vec 0,r)))))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && can (find_term ((=) `phi:real^(2,2)finite_sum->real^3`))
        (lhs (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (lhs (concl th)))) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior (IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3)
                                              (cball(vec 0,r))))) =
    IMAGE h (revolution (IMAGE f (ball(vec 0,r))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3)
                                                  (cball(vec 0,r))))`;
                   `phi:real^(2,2)finite_sum->real^3`;
                   `psi:real^3->real^(2,2)finite_sum`] MOI_S3TA_SOLID_TORUS_INTERIOR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[solid_torus] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`phi:real^(2,2)finite_sum->real^3`;
                          `psi:real^3->real^(2,2)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    (* the frontier *)
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^(2,2)finite_sum->real^3)
                  (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF
                IMAGE phi (ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^(2,2)finite_sum->real^3)
                  (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) =
      (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF
      (ball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CBALL_DIFF_BALL] THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; PASTECART_IN_PCROSS] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3RV_IMAGE_DIFF_INJ THEN
    EXISTS_TAC `psi:real^3->real^(2,2)finite_sum` THEN
    EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
    (* spines *)
    X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN REWRITE_TAC[spine] THEN
    MAP_EVERY EXISTS_TAC [`phi:real^(2,2)finite_sum->real^3`;
                          `psi:real^3->real^(2,2)finite_sum`; `p:real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `{p:real^2}` (ASSUME
     `!a. a SUBSET cball(vec 0:real^2,&1)
          ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
              IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3)
                                                     (IMAGE (\x:real^2. r % x) a)))`)) THEN
    REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]]);;

(* ========================================================================= *)
(* Part 3: the toroidal shell between h(rev f(cball(0,r))) and              *)
(* h(rev dd) (0 < r < 1): the annulus cball(0,1) DIFF ball(0,r) of the     *)
(* chart, parametrised by (sphere PCROSS sphere) PCROSS [0,1], is the       *)
(* closure of the difference, and its two ends are the two frontiers.       *)
(* ========================================================================= *)

(* The closure of a planar annulus (the 2D version of                      *)
(* MOI_S4C_ANNULUS_CLOSURE, pc_moi_s34_cellnba, with the same proof).      *)

let MOI_S3RV_ANNULUS_CLOSURE = prove
 (`!r. &0 < r /\ r < &1
       ==> closure (cball(vec 0:real^2,&1) DIFF cball(vec 0,r)) =
           cball(vec 0,&1) DIFF ball(vec 0,r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_CBALL; OPEN_BALL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(y:real^2) = r` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `t = min (e / &2) ((&1 - r) / &2)` THEN
  SUBGOAL_THEN `&0 < t /\ t < e /\ r + t < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `((r + t) / r) % (y:real^2)` THEN
  REWRITE_TAC[IN_DIFF; IN_CBALL_0; NORM_MUL; dist] THEN
  SUBGOAL_THEN `abs((r + t) / r) * norm(y:real^2) = r + t` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (r + t) / r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `((r + t) / r) % (y:real^2) - y = (t / r) % y` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a % y - y:real^N = (a - &1) % y`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(t / r) * r = t` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < t / r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[CBALL_DIFF_BALL] THEN ASM_REAL_ARITH_TAC]);;

(* The closure of a homeomorphic image inside a compact domain. *)

let MOI_S3RV_CLOSURE_HOMEO_IMAGE = prove
 (`!(f:real^M->real^N) g s t b.
     homeomorphism (s,t) (f,g) /\ compact s /\ b SUBSET s
     ==> closure (IMAGE f b) = IMAGE f (closure b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure b SUBSET (s:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on closure b` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET]]);;

(* The annulus map of the chart: ((u,z),t) -> ((r + t (1 - r)) u, z). *)

let moi_s3rv_ann = new_definition
 `moi_s3rv_ann (r:real) (w:real^((2,2)finite_sum,1)finite_sum) =
    pastecart ((r + drop(sndcart w) * (&1 - r)) % fstcart(fstcart w))
              (sndcart(fstcart w)):real^(2,2)finite_sum`;;

let MOI_S3RV_ANN_CONTINUOUS = prove
 (`!r s. moi_s3rv_ann r continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s3rv_ann r =
    (\w:real^((2,2)finite_sum,1)finite_sum.
       pastecart ((r + drop(sndcart w) * (&1 - r)) % fstcart(fstcart w))
                 (sndcart(fstcart w)):real^(2,2)finite_sum)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3rv_ann]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
      SUBGOAL_THEN `(\w:real^((2,2)finite_sum,1)finite_sum. fstcart(fstcart w):real^2) =
                    fstcart o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART]];
    SUBGOAL_THEN `(\w:real^((2,2)finite_sum,1)finite_sum. sndcart(fstcart w):real^2) =
                  sndcart o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART]]);;

let MOI_S3RV_UNIT_DIR = prove
 (`!v:real^2. ~(v = vec 0) ==> norm(inv(norm v) % v) = &1 /\ norm v % inv(norm v) % v = v`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(v:real^2) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; VECTOR_MUL_ASSOC;
               REAL_MUL_RINV; VECTOR_MUL_LID]);;

let MOI_S3RV_ANN_FACTS = prove
 (`!r. &0 < r /\ r < &1
       ==> IMAGE (moi_s3rv_ann r)
             ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
              interval[vec 0:real^1,vec 1]) =
           (cball(vec 0:real^2,&1) DIFF ball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1) /\
           IMAGE (moi_s3rv_ann r)
             ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
              {vec 0:real^1}) =
           sphere(vec 0:real^2,r) PCROSS sphere(vec 0:real^2,&1) /\
           IMAGE (moi_s3rv_ann r)
             ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
              {vec 1:real^1}) =
           sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
           (!w w'. w IN (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                        interval[vec 0:real^1,vec 1] /\
                   w' IN (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                         interval[vec 0:real^1,vec 1] /\
                   moi_s3rv_ann r w = moi_s3rv_ann r w'
                   ==> w = w')`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; FORALL_PASTECART;
              PASTECART_IN_PCROSS; moi_s3rv_ann; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ; IN_SPHERE_0; IN_CBALL_0; IN_BALL_0; IN_DIFF;
              IN_INTERVAL_1; DROP_VEC; IN_SING] THEN
  SUBGOAL_THEN `!t:real^1. &0 <= drop t /\ drop t <= &1
                  ==> &0 <= drop t * (&1 - r) /\ drop t * (&1 - r) <= &1 - r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x * a <= &1 * a ==> x * a <= a`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the image of the whole parameter space is the annulus *)
    MAP_EVERY X_GEN_TAC [`v:real^2`; `z:real^2`] THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^2`; `z':real^2`; `t:real^1`] THEN STRIP_TAC THEN
      MP_TAC(MP (SPEC `t:real^1` (ASSUME
       `!t:real^1. &0 <= drop t /\ drop t <= &1
                   ==> &0 <= drop t * (&1 - r) /\ drop t * (&1 - r) <= &1 - r`))
       (CONJ (ASSUME `&0 <= drop(t:real^1)`) (ASSUME `drop(t:real^1) <= &1`))) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      SUBGOAL_THEN `~(v:real^2 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(norm(v:real^2) < r)` THEN
        ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`inv(norm v) % v:real^2`; `z:real^2`;
                            `lift((norm(v:real^2) - r) / (&1 - r))`] THEN
      ASM_SIMP_TAC[MOI_S3RV_UNIT_DIR; LIFT_DROP] THEN
      SUBGOAL_THEN `r + (norm(v:real^2) - r) / (&1 - r) * (&1 - r) = norm v`
      SUBST1_TAC THENL
       [UNDISCH_TAC `r < &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_S3RV_UNIT_DIR] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC]];
    (* the end t = 0 *)
    MAP_EVERY X_GEN_TAC [`v:real^2`; `z:real^2`] THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^2`; `z':real^2`; `t:real^1`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LZERO; REAL_ADD_RID; NORM_MUL; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`inv r % v:real^2`; `z:real^2`; `vec 0:real^1`] THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LZERO; REAL_ADD_RID; NORM_MUL; VECTOR_MUL_ASSOC;
                      REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                   REAL_ARITH `&0 < r ==> abs r = r`]];
    (* the end t = 1 *)
    MAP_EVERY X_GEN_TAC [`v:real^2`; `z:real^2`] THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^2`; `z':real^2`; `t:real^1`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LID; REAL_ARITH `r + (&1 - r) = &1`;
                      VECTOR_MUL_LID];
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`v:real^2`; `z:real^2`; `vec 1:real^1`] THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LID; REAL_ARITH `r + (&1 - r) = &1`;
                      VECTOR_MUL_LID]];
    (* injectivity *)
    MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real^2`; `t:real^1`;
                         `u':real^2`; `z':real^2`; `t':real^1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(MP (SPEC `t:real^1` (ASSUME
     `!t:real^1. &0 <= drop t /\ drop t <= &1
                 ==> &0 <= drop t * (&1 - r) /\ drop t * (&1 - r) <= &1 - r`))
     (CONJ (ASSUME `&0 <= drop(t:real^1)`) (ASSUME `drop(t:real^1) <= &1`))) THEN
    MP_TAC(MP (SPEC `t':real^1` (ASSUME
     `!t:real^1. &0 <= drop t /\ drop t <= &1
                 ==> &0 <= drop t * (&1 - r) /\ drop t * (&1 - r) <= &1 - r`))
     (CONJ (ASSUME `&0 <= drop(t':real^1)`) (ASSUME `drop(t':real^1) <= &1`))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `drop t * (&1 - r) = drop t' * (&1 - r)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^2->real` o check (fun th ->
        is_eq (concl th) && is_comb (lhs (concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "%")) (concl th))) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `drop t = drop t'` ASSUME_TAC THENL
     [UNDISCH_TAC `drop t * (&1 - r) = drop t' * (&1 - r)` THEN
      REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[GSYM DROP_EQ]] THEN
    UNDISCH_TAC `(r + drop t * (&1 - r)) % u = (r + drop t' * (&1 - r)) % (u':real^2)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
    MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN ASM_REAL_ARITH_TAC]);;

(* The shell lemma. *)

let MOI_S3RV_SHELL = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) r.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     &0 < r /\ r < &1
     ==> IMAGE h (revolution (IMAGE f (cball(vec 0,r)))) SUBSET
         interior (IMAGE h (revolution dd)) /\
         toroidal_shell
           (closure (IMAGE h (revolution dd) DIFF
                     IMAGE h (revolution (IMAGE f (cball(vec 0,r))))))
           (frontier (IMAGE h (revolution (IMAGE f (cball(vec 0,r))))))
           (frontier (IMAGE h (revolution dd)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `&1`] MOI_S3RV_CHART_FACTS) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `&1`] MOI_S3RV_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^(2,2)finite_sum` ASSUME_TAC) THEN
  ABBREV_TAC `phi = \p:real^(2,2)finite_sum.
                      (h:real^3->real^3)(moi_s3rv_rot ((f:real^2->real^3)(&1 % fstcart p))
                                                      (sndcart p))` THEN
  SUBGOAL_THEN
   `!a. a SUBSET cball(vec 0:real^2,&1)
        ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
            IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "phi" THEN
    MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                   `h:real^3->real^3`; `&1`; `a:real^2->bool`] MOI_S3RV_PHI_IMAGE) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID; IMAGE_ID];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (find_term ((=) `psi:real^3->real^(2,2)finite_sum`)) (concl th))) THEN
  SUBGOAL_THEN `cball(vec 0:real^2,r) SUBSET cball(vec 0,&1) /\
                cball(vec 0:real^2,r) SUBSET ball(vec 0,&1) /\
                sphere(vec 0:real^2,r) SUBSET cball(vec 0,&1) /\
                sphere(vec 0:real^2,&1) SUBSET cball(vec 0,&1) /\
                cball(vec 0:real^2,&1) DIFF ball(vec 0,r) SUBSET cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0; IN_SPHERE_0; IN_DIFF] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (t,u) -> MP_TAC(MP (SPEC t (ASSUME
    `!a. a SUBSET cball(vec 0:real^2,&1)
          ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
              IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) a))`))
      (ASSUME u)) THEN DISCH_TAC)
   [`cball(vec 0:real^2,r)`, `cball(vec 0:real^2,r) SUBSET cball(vec 0,&1)`;
    `sphere(vec 0:real^2,r)`, `sphere(vec 0:real^2,r) SUBSET cball(vec 0,&1)`;
    `sphere(vec 0:real^2,&1)`, `sphere(vec 0:real^2,&1) SUBSET cball(vec 0,&1)`] THEN
  CONJ_TAC THENL
   [(* the inner torus lies in the interior *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC MOI_S3RV_REV_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the closure of the difference *)
  SUBGOAL_THEN
   `closure (IMAGE (h:real^3->real^3) (revolution dd) DIFF
             IMAGE h (revolution (IMAGE (f:real^2->real^3) (cball(vec 0,r))))) =
    IMAGE (phi:real^(2,2)finite_sum->real^3)
          ((cball(vec 0:real^2,&1) DIFF ball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (h:real^3->real^3) (revolution dd) DIFF
      IMAGE h (revolution (IMAGE (f:real^2->real^3) (cball(vec 0,r)))) =
      IMAGE (phi:real^(2,2)finite_sum->real^3)
            ((cball(vec 0:real^2,&1) DIFF cball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[SYM(ASSUME
        `IMAGE (phi:real^(2,2)finite_sum->real^3)
           (cball(vec 0:real^2,r) PCROSS sphere(vec 0:real^2,&1)) =
         IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) (cball(vec 0,r))))`);
                   SYM(ASSUME
        `IMAGE (phi:real^(2,2)finite_sum->real^3)
           (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) =
         IMAGE (h:real^3->real^3) (revolution dd)`)] THEN
      SUBGOAL_THEN
       `(cball(vec 0:real^2,&1) DIFF cball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1) =
        (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF
        (cball(vec 0:real^2,r) PCROSS sphere(vec 0:real^2,&1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; PASTECART_IN_PCROSS] THEN
        CONV_TAC TAUT;
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_S3RV_IMAGE_DIFF_INJ THEN
      EXISTS_TAC `psi:real^3->real^(2,2)finite_sum` THEN
      EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      UNDISCH_TAC `cball(vec 0:real^2,r) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`phi:real^(2,2)finite_sum->real^3`; `psi:real^3->real^(2,2)finite_sum`;
                   `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                   `IMAGE (h:real^3->real^3) (revolution dd)`;
                   `(cball(vec 0:real^2,&1) DIFF cball(vec 0,r)) PCROSS
                    sphere(vec 0:real^2,&1)`] MOI_S3RV_CLOSURE_HOMEO_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DIFF] THEN
      SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[CLOSURE_PCROSS; MOI_S3RV_ANNULUS_CLOSURE; CLOSURE_CLOSED; CLOSED_SPHERE];
    ALL_TAC] THEN
  (* the shell parametrisation *)
  MP_TAC(MATCH_MP MOI_S3RV_ANN_FACTS (CONJ (ASSUME `&0 < r`) (ASSUME `r < &1`))) THEN
  STRIP_TAC THEN
  REWRITE_TAC[toroidal_shell] THEN
  MP_TAC(ISPECL
   [`(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
     interval[vec 0:real^1,vec 1]`;
    `(phi:real^(2,2)finite_sum->real^3) o moi_s3rv_ann r`;
    `IMAGE (phi:real^(2,2)finite_sum->real^3)
           ((cball(vec 0:real^2,&1) DIFF ball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1))`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_INTERVAL];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[MOI_S3RV_ANN_CONTINUOUS] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DIFF] THEN
      SIMP_TAC[];
      ASM_REWRITE_TAC[IMAGE_o];
      MAP_EVERY X_GEN_TAC [`w:real^((2,2)finite_sum,1)finite_sum`;
                           `w':real^((2,2)finite_sum,1)finite_sum`] THEN
      REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s3rv_ann"))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_s3rv_ann r w IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0,&1) /\
                    moi_s3rv_ann r w' IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0,&1)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
         `!s t. IMAGE (f:A->B) s = t /\ t SUBSET u /\ x IN s ==> f x IN u`) THEN
        MAP_EVERY EXISTS_TAC
         [`(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
           interval[vec 0:real^1,vec 1]`;
          `(cball(vec 0:real^2,&1) DIFF ball(vec 0,r)) PCROSS sphere(vec 0:real^2,&1)`] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DIFF] THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(MP (SPEC `moi_s3rv_ann r w` (ASSUME
       `!x. x IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
            ==> (psi:real^3->real^(2,2)finite_sum) ((phi:real^(2,2)finite_sum->real^3) x) =
                x`))
       (ASSUME `moi_s3rv_ann r w IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0,&1)`)) THEN
      MP_TAC(MP (SPEC `moi_s3rv_ann r w'` (ASSUME
       `!x. x IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
            ==> (psi:real^3->real^(2,2)finite_sum) ((phi:real^(2,2)finite_sum->real^3) x) =
                x`))
       (ASSUME `moi_s3rv_ann r w' IN cball(vec 0:real^2,&1) PCROSS sphere(vec 0,&1)`)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `gg:real^3->real^((2,2)finite_sum,1)finite_sum`)] THEN
  MAP_EVERY EXISTS_TAC [`(phi:real^(2,2)finite_sum->real^3) o moi_s3rv_ann r`;
                        `gg:real^3->real^((2,2)finite_sum,1)finite_sum`] THEN
  ASM_REWRITE_TAC[IMAGE_o]);;

(* ========================================================================= *)
(* Part 4: the relative interior of dd is the image of the open ball        *)
(* under any disk chart, compact subsets of the open unit ball lie in a     *)
(* smaller ball, and clause 2 of REV_SHELL for a chart.                     *)
(* ========================================================================= *)

let MOI_S3RV_RELINT = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd DIFF relative_interior dd = IMAGE f (sphere(vec 0,&1))
     ==> relative_interior dd = IMAGE f (ball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPEC `dd:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN DISCH_TAC THEN
  SUBGOAL_THEN `relative_interior dd = dd DIFF (dd DIFF relative_interior (dd:real^3->bool))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `relative_interior dd SUBSET (dd:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3) (cball(vec 0,&1)) = dd` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN
  MATCH_MP_TAC MOI_S3RV_IMAGE_DIFF_INJ THEN
  EXISTS_TAC `g:real^3->real^2` THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SPHERE_SUBSET_CBALL]);;

let MOI_S3RV_COMPACT_IN_BALL = prove
 (`!k:real^2->bool.
     compact k /\ k SUBSET ball(vec 0,&1)
     ==> ?r. &0 < r /\ r < &1 /\ k SUBSET ball(vec 0,r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:real^2->bool = {}` THENL
   [EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`norm:real^2->real`; `k:real^2->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(x:real^2) < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN k` THEN UNDISCH_TAC `k SUBSET ball(vec 0:real^2,&1)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(norm(x:real^2) + &1) / &2` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `x:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(x:real^2)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]]);;

(* Clause 2 for a chart. *)

let MOI_S3RV_CLAUSE2 = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) k.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     compact k /\ k SUBSET IMAGE f (ball(vec 0,&1))
     ==> ?s1. solid_torus s1 /\ IMAGE h (revolution k) SUBSET interior s1 /\
              s1 SUBSET interior (IMAGE h (revolution dd)) /\
              toroidal_shell (closure (IMAGE h (revolution dd) DIFF s1))
                             (frontier s1)
                             (frontier (IMAGE h (revolution dd)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET dd` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:real^2->real^3) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) (cball(vec 0,&1)) = dd` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^2) k SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (f:real^2->real^3) (ball(vec 0,&1))` MP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN k` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET IMAGE (f:real^2->real^3) (ball(vec 0,&1))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real^3->real^2) ((f:real^2->real^3) y) = y` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x:real^2. x IN cball(vec 0,&1) ==> (g:real^3->real^2) (f x) = x`) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (g:real^3->real^2) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dd:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (g:real^3->real^2) k` MOI_S3RV_COMPACT_IN_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (h:real^3->real^3) (revolution (IMAGE (f:real^2->real^3) (cball(vec 0,r))))` THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_SHELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC MOI_S3RV_REV_MONO THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `(g:real^3->real^2) x` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ASSUME `!y:real^3. y IN dd ==> (f:real^2->real^3) (g y) = y`) THEN
    UNDISCH_TAC `(x:real^3) IN k` THEN UNDISCH_TAC `(k:real^3->bool) SUBSET dd` THEN SET_TAC[];
    UNDISCH_TAC `(x:real^3) IN k` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^2) k SUBSET ball(vec 0,r)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* Part 5: clause 3 (a small solid torus with the circle of q as a spine):  *)
(* re-centre the chart by HOMEOMORPHISM_MOVING_POINT_EXISTS so that it      *)
(* sends 0 to q, then take a small radius by uniform continuity; and the    *)
(* theorem REV_SHELL.                                                       *)
(* ========================================================================= *)

let MOI_S3RV_RECENTRE = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g q.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     q IN IMAGE f (ball(vec 0,&1))
     ==> ?f' g'. homeomorphism (cball(vec 0:real^2,&1),dd) (f',g') /\ f'(vec 0) = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(q:real^3) IN IMAGE (f:real^2->real^3) (ball(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `cball(vec 0:real^2,&1)`; `vec 0:real^2`;
                 `c:real^2`] HOMEOMORPHISM_MOVING_POINT_EXISTS) THEN
  SUBGOAL_THEN `affine hull ball(vec 0:real^2,&1) = (:real^2)` SUBST1_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_OPEN THEN REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL; BALL_SUBSET_CBALL; SUBSET_UNIV;
                  CONNECTED_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_THEN `g0:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^3) o (f0:real^2->real^2)`;
                        `(g0:real^2->real^2) o (g:real^3->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[o_THM]]);;

let MOI_S3RV_CLAUSE3 = prove
 (`!(dd:real^3->bool) (f:real^2->real^3) g (h:real^3->real^3) q w.
     homeomorphism (cball(vec 0:real^2,&1),dd) (f,g) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y) /\
     q IN IMAGE f (ball(vec 0,&1)) /\ open w /\ IMAGE h (revolution {q}) SUBSET w
     ==> ?s1. solid_torus s1 /\ spine (IMAGE h (revolution {q})) s1 /\
              s1 SUBSET w INTER interior (IMAGE h (revolution dd)) /\
              toroidal_shell (closure (IMAGE h (revolution dd) DIFF s1))
                             (frontier s1)
                             (frontier (IMAGE h (revolution dd)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`; `q:real^3`]
    MOI_S3RV_RECENTRE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^2->real^3` (X_CHOOSE_THEN `g':real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `phi = \p:real^(2,2)finite_sum.
                      (h:real^3->real^3)(moi_s3rv_rot ((f':real^2->real^3)(&1 % fstcart p))
                                                      (sndcart p))` THEN
  SUBGOAL_THEN
   `!a. a SUBSET cball(vec 0:real^2,&1)
        ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
            IMAGE (h:real^3->real^3) (revolution (IMAGE (f':real^2->real^3) a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "phi" THEN
    MP_TAC(ISPECL [`dd:real^3->bool`; `f':real^2->real^3`; `g':real^3->real^2`;
                   `h:real^3->real^3`; `&1`; `a:real^2->bool`] MOI_S3RV_PHI_IMAGE) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID; IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^(2,2)finite_sum->real^3) continuous_on
                (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN MATCH_MP_TAC MOI_S3RV_PHI_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`dd:real^3->bool`; `g':real^3->real^2`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  (* the circle of q *)
  SUBGOAL_THEN `{vec 0:real^2} SUBSET cball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SING_SUBSET; CENTRE_IN_CBALL; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (phi:real^(2,2)finite_sum->real^3) ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1)) =
    IMAGE (h:real^3->real^3) (revolution {q:real^3})`
  ASSUME_TAC THENL
   [MP_TAC(MP (SPEC `{vec 0:real^2}` (ASSUME
     `!a. a SUBSET cball(vec 0:real^2,&1)
          ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
              IMAGE (h:real^3->real^3) (revolution (IMAGE (f':real^2->real^3) a))`))
     (ASSUME `{vec 0:real^2} SUBSET cball(vec 0,&1)`)) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (revolution {q:real^3}))` ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (phi:real^(2,2)finite_sum->real^3) ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1)) =
      IMAGE (h:real^3->real^3) (revolution {q:real^3})` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      SIMP_TAC[CENTRE_IN_CBALL; REAL_POS];
      SIMP_TAC[COMPACT_PCROSS; COMPACT_SING; COMPACT_SPHERE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (revolution {q:real^3})`; `(:real^3) DIFF w`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {q:real^3}) SUBSET w` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`phi:real^(2,2)finite_sum->real^3`;
                 `cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `dl:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min (ep / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < r /\ r < &1 /\ r < ep` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (h:real^3->real^3) (revolution (IMAGE (f':real^2->real^3) (cball(vec 0,r))))` THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f':real^2->real^3`; `g':real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f':real^2->real^3`; `g':real^3->real^2`;
                 `h:real^3->real^3`; `r:real`] MOI_S3RV_SHELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* the spine *)
    MP_TAC(SPEC `vec 0:real^2` (ASSUME
     `!p. p IN ball(vec 0:real^2,&1)
          ==> spine (IMAGE (h:real^3->real^3) (revolution {(f':real^2->real^3)(r % p)}))
                    (IMAGE h (revolution (IMAGE f' (cball(vec 0,r)))))`)) THEN
    REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01; VECTOR_MUL_RZERO] THEN ASM_REWRITE_TAC[];
    (* inside w and inside the interior *)
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (h:real^3->real^3) (revolution (IMAGE (f':real^2->real^3) (cball(vec 0,r)))) =
      IMAGE (phi:real^(2,2)finite_sum->real^3)
            (cball(vec 0:real^2,r) PCROSS sphere(vec 0:real^2,&1))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC(ASSUME
       `!a. a SUBSET cball(vec 0:real^2,&1)
          ==> IMAGE (phi:real^(2,2)finite_sum->real^3) (a PCROSS sphere(vec 0:real^2,&1)) =
              IMAGE (h:real^3->real^3) (revolution (IMAGE (f':real^2->real^3) a))`) THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`v:real^2`; `z:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(phi:real^(2,2)finite_sum->real^3) (pastecart (vec 0) z) IN
                  IMAGE (h:real^3->real^3) (revolution {q:real^3})`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `IMAGE (phi:real^(2,2)finite_sum->real^3) ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1)) =
        IMAGE (h:real^3->real^3) (revolution {q:real^3})` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `dl <= dist((phi:real^(2,2)finite_sum->real^3) (pastecart (vec 0) z),
                             phi (pastecart v z))`
    MP_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x y. x IN IMAGE (h:real^3->real^3) (revolution {q:real^3}) /\ y IN (:real^3) DIFF w
              ==> dl <= dist(x,y)`) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `ep:real`)) (concl th))) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; DIST_PASTECART_CANCEL; DIST_0; CENTRE_IN_CBALL;
                REAL_POS] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^2) IN cball(vec 0,r)` THEN REWRITE_TAC[IN_CBALL_0] THEN
    ASM_REAL_ARITH_TAC]);;

(* The theorem REV_SHELL. *)

let REV_SHELL = prove
 (MOI_S31_REV_SHELL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `disk_with_boundary (dd:real^3->bool) (dd DIFF relative_interior dd)` THEN
  REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`]
    MOI_S3RV_RELINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`dd:real^3->bool`; `f:real^2->real^3`; `g:real^3->real^2`;
                   `h:real^3->real^3`; `&1`] MOI_S3RV_CHART_FACTS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphism"))
        (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN SIMP_TAC[];
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3RV_CLAUSE2 THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `g:real^3->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET relative_interior dd` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`q:real^3`; `w:real^3->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3RV_CLAUSE3 THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `g:real^3->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^3) IN relative_interior dd` THEN ASM_REWRITE_TAC[]]);;

