(* ========================================================================= *)
(* pc_smt_sphere: the sphere end of the Smale chain.  S1 (Smale's theorem in *)
(* radial form) from S2 (every diffeomorphism of S^2 is isotopic to an       *)
(* orthogonal map); S2 from S7 (pole normalisation), S3 (planar isotopies)   *)
(* and S8 (stereographic transport).                                         *)
(*                                                                           *)
(* S1 from S2.  The extension is radial_ext of the isotopy at                *)
(* time beta |x|, beta = 0 for |x| <= 1/4 and 1 for |x| >= 1/2: it is the    *)
(* orthogonal map Q near 0 and radial_ext f for |x| >= 1/2.                  *)
(* ========================================================================= *)

needs "src/pc_smt_defs.ml";;
needs "src/ns_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

let OPEN_NONZERO = prove
 (`open {x:real^N | ~(x = vec 0)}`,
  REWRITE_TAC[SET_RULE `{x:real^N | ~(x = a)} = (:real^N) DELETE a`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let SMT_NORMALIZE_SPHERE = prove
 (`!x:real^N. ~(x = vec 0) ==> inv(norm x) % x IN sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0]);;

let SMOOTH_MAP_ON_LIFT_NORM_NONZERO = prove
 (`smooth_map_on {x:real^N | ~(x = vec 0)} (\x. lift(norm x))`,
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. x`]
    SMOOTH_MAP_ON_LIFT_NORM) THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN
  SIMP_TAC[ETA_AX]);;

let SMOOTH_MAP_ON_NORMALIZE = prove
 (`smooth_map_on {x:real^N | ~(x = vec 0)} (\x. inv(norm x) % x)`,
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(inv(norm x))`;
                 `\x:real^N. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP; IN_ELIM_THM; NORM_EQ_0; OPEN_NONZERO;
              SMOOTH_MAP_ON_LIFT_NORM_NONZERO]);;

(* Radial extension of a smooth family of maps near the sphere, at the time  *)
(* beta(|x|), is smooth away from 0.                                         *)

let SMT_RADIAL_FAMILY_SMOOTH = prove
 (`!u (J:real->real^N->real^N) (beta:real->real).
        open u /\ sphere(vec 0,&1) SUBSET u /\ smooth_family u J /\
        smooth_map_on (:real^1) (lift o beta o drop)
        ==> smooth_map_on {x | ~(x = vec 0)}
                          (\x. radial_ext (J (beta(norm x))) x)`,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC SMOOTH_MAP_ON_LIFT_NORM_NONZERO THEN
  ASSUME_TAC SMOOTH_MAP_ON_NORMALIZE THEN
  SUBGOAL_THEN `smooth_map_on {x:real^N | ~(x = vec 0)} (\x. lift(beta(norm x)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `(:real^1)`;
                   `\x:real^N. lift(norm x)`; `beta:real->real`]
      SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; LIFT_DROP; OPEN_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {x:real^N | ~(x = vec 0)}
      (\x. (J:real->real^N->real^N) (beta(norm x)) (inv(norm x) % x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^N. (J:real->real^N->real^N) (beta(norm x)) (inv(norm x) % x)) =
      (\z. J (drop(fstcart z)) (sndcart z)) o
      (\x. pastecart (lift(beta(norm x))) (inv(norm x) % x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                  LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^1) PCROSS (u:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_PASTECART_OPEN; OPEN_NONZERO] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS;
                  IN_UNIV] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
      UNDISCH_TAC `smooth_family u (J:real->real^N->real^N)` THEN
      REWRITE_TAC[smooth_family]];
    ALL_TAC] THEN
  REWRITE_TAC[radial_ext] THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x)`;
                 `\x:real^N. (J:real->real^N->real^N) (beta(norm x)) (inv(norm x) % x)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP; OPEN_NONZERO]);;

(* Elementary facts on radial extensions. *)

let SMT_RADIAL_EXT_0 = prove
 (`!FF:real^N->real^N. radial_ext FF (vec 0) = vec 0`,
  REWRITE_TAC[radial_ext; NORM_0; VECTOR_MUL_LZERO]);;

let SMT_RADIAL_EXT_EQ = prove
 (`!(FF:real^N->real^N) GG x.
        (!y. y IN sphere(vec 0,&1) ==> FF y = GG y)
        ==> radial_ext FF x = radial_ext GG x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[SMT_RADIAL_EXT_0];
    ASM_SIMP_TAC[radial_ext; SMT_NORMALIZE_SPHERE]]);;

let SMT_RADIAL_EXT_LINEAR = prove
 (`!(L:real^N->real^N) x. linear L ==> radial_ext L x = L x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_0) THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP LINEAR_CMUL) THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[SMT_RADIAL_EXT_0];
    ASM_REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]]);;

let SMT_RADIAL_EXT_NORM = prove
 (`!(FF:real^N->real^N) x.
        (!y. y IN sphere(vec 0,&1) ==> FF y IN sphere(vec 0,&1))
        ==> norm(radial_ext FF x) = norm x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[SMT_RADIAL_EXT_0] THEN
  REWRITE_TAC[radial_ext; NORM_MUL; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `norm((FF:real^N->real^N)(inv(norm x) % x)) = &1`
   (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
  REWRITE_TAC[GSYM IN_SPHERE_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE]);;

let SMT_RADIAL_EXT_INVERSE = prove
 (`!(FF:real^N->real^N) GG x.
        (!y. y IN sphere(vec 0,&1) ==> FF y IN sphere(vec 0,&1) /\ GG(FF y) = y)
        ==> radial_ext GG (radial_ext FF x) = x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[SMT_RADIAL_EXT_0] THEN
  SUBGOAL_THEN `norm(radial_ext (FF:real^N->real^N) x) = norm x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [radial_ext] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(norm x) % radial_ext (FF:real^N->real^N) x = FF(inv(norm x) % x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
               VECTOR_MUL_LID]);;

(* The time function beta(r) = smooth_step(4 r - 1). *)

let SMT_BETA_QUARTER = prove
 (`smooth_map_on (:real^1) (lift o (\r. smooth_step(&4 * r - &1)) o drop) /\
   (!r. r <= &1 / &4 ==> smooth_step(&4 * r - &1) = &0) /\
   (!r. &1 / &2 <= r ==> smooth_step(&4 * r - &1) = &1)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&4 * drop x - &1)`]
      SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&4 * drop x)`;
                   `\x:real^1. lift(&1)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^1)`; `&4`; `\x:real^1. x`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_ID];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

(* The radial extension of a smooth family at time beta |x|, equal to a      *)
(* linear map at time 0, is smooth on R^N.                                   *)

let SMT_RADIAL_ISOTOPY_SMOOTH = prove
 (`!u (J:real->real^N->real^N) L.
        open u /\ sphere(vec 0,&1) SUBSET u /\ smooth_family u J /\ linear L /\
        (!y. y IN sphere(vec 0,&1) ==> J (&0) y = L y)
        ==> smooth_map_on (:real^N)
              (\x. radial_ext (J (smooth_step(&4 * norm x - &1))) x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [EXISTS_TAC `ball(vec 0:real^N,&1 / &4)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `L:real^N->real^N` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `smooth_step(&4 * norm(y:real^N) - &1) = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC EQ_TRANS `radial_ext (L:real^N->real^N) y` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMT_RADIAL_EXT_EQ THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[SMT_RADIAL_EXT_LINEAR]];
      MP_TAC(ISPECL [`ball(vec 0:real^N,&1 / &4)`; `\x:real^N. x`; `L:real^N->real^N`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
      REWRITE_TAC[o_DEF; ETA_AX]];
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `J:real->real^N->real^N`;
                   `\r. smooth_step(&4 * r - &1)`] SMT_RADIAL_FAMILY_SMOOTH) THEN
    ASM_REWRITE_TAC[SMT_BETA_QUARTER]]);;

(* A sphere isotopy from an orthogonal map Q to f gives a norm-preserving    *)
(* diffeomorphism of R^N equal to radial_ext f for |x| >= 1/2.               *)

let SMT_RADIAL_ISOTOPY_EXTENSION = prove
 (`!(J:real->real^N->real^N) J' Q f.
        sphere_isotopy J J' /\ orthogonal_transformation Q /\
        (!t x. t <= &0 /\ x IN sphere(vec 0,&1) ==> J t x = Q x) /\
        (!t x. &1 <= t /\ x IN sphere(vec 0,&1) ==> J t x = f x)
        ==> ?h k. diffeomorphism_on (:real^N) (:real^N) h k /\
                  (!x. norm(h x) = norm x) /\
                  (!x. &1 / &2 <= norm x ==> h x = radial_ext f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
                     (LABEL_TAC "sph"))
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "J0") (LABEL_TAC "J1")))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Q':real^N->real^N` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  SUBGOAL_THEN `!y:real^N. y IN sphere(vec 0,&1)
                ==> (J':real->real^N->real^N) (&0) y = (Q':real^N->real^N) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Q':real^N->real^N) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
      UNDISCH_TAC `orthogonal_transformation (Q':real^N->real^N)` THEN
      SIMP_TAC[ORTHOGONAL_TRANSFORMATION];
      ALL_TAC] THEN
    SUBGOAL_THEN `y = (J:real->real^N->real^N) (&0) (Q' y)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [USE_THEN "J0" (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]); ALL_TAC] THEN
    USE_THEN "sph" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^N. norm(radial_ext ((J:real->real^N->real^N)
                   (smooth_step(&4 * norm x - &1))) x) = norm x) /\
    (!x:real^N. norm(radial_ext ((J':real->real^N->real^N)
                   (smooth_step(&4 * norm x - &1))) x) = norm x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN
    USE_THEN "sph" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^N. radial_ext ((J':real->real^N->real^N) (smooth_step(&4 * norm x - &1)))
                  (radial_ext (J (smooth_step(&4 * norm x - &1))) x) = x) /\
    (!x:real^N. radial_ext ((J:real->real^N->real^N) (smooth_step(&4 * norm x - &1)))
                  (radial_ext (J' (smooth_step(&4 * norm x - &1))) x) = x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN
    USE_THEN "sph" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. radial_ext ((J:real->real^N->real^N)
                  (smooth_step(&4 * norm x - &1))) x`;
    `\x:real^N. radial_ext ((J':real->real^N->real^N)
                  (smooth_step(&4 * norm x - &1))) x`] THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `radial_ext ((J':real->real^N->real^N)
                  (smooth_step(&4 * norm y - &1))) y` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `radial_ext ((J:real->real^N->real^N)
                  (smooth_step(&4 * norm y - &1))) y` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMT_RADIAL_ISOTOPY_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `Q:real^N->real^N`] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    REPEAT STRIP_TAC THEN USE_THEN "J0" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC SMT_RADIAL_ISOTOPY_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `Q':real^N->real^N`] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step(&4 * norm(x:real^N) - &1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMT_RADIAL_EXT_EQ THEN REPEAT STRIP_TAC THEN
    USE_THEN "J1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* S1 from S2. *)

let SMT_SMALE_FROM_ISOTOPY = prove
 (`SMT_SPHERE_ISOTOPY_STATEMENT ==> SMT_SMALE_RADIAL_STATEMENT`,
  REWRITE_TAC[SMT_SPHERE_ISOTOPY_STATEMENT; SMT_SMALE_RADIAL_STATEMENT] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^3->real^3`; `g:real^3->real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->real^3->real^3` (X_CHOOSE_THEN
    `J':real->real^3->real^3` (X_CHOOSE_THEN `Q:real^3->real^3`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`J:real->real^3->real^3`; `J':real->real^3->real^3`;
                 `Q:real^3->real^3`; `f:real^3->real^3`]
                SMT_RADIAL_ISOTOPY_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Calculus of sphere isotopies (time reparametrization,                     *)
(* composition with an orthogonal map, concatenation).                       *)
(* ------------------------------------------------------------------------- *)

let OPEN_R_PCROSS_NONZERO = prove
 (`open ((:real^1) PCROSS {x:real^N | ~(x = vec 0)})`,
  SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_NONZERO]);;

(* Smooth families composed with a time change. *)

let SMT_FAMILY_REPARAM = prove
 (`!u (J:real->real^M->real^N) (phi:real->real).
        open u /\ smooth_family u J /\ smooth_map_on (:real^1) (lift o phi o drop)
        ==> smooth_family u (\t. J (phi t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_family] THEN
  SUBGOAL_THEN `open ((:real^1) PCROSS (u:real^M->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (J:real->real^M->real^N) (phi(drop(fstcart z))) (sndcart z)) =
    (\z. J (drop(fstcart z)) (sndcart z)) o
    (\z:real^(1,M)finite_sum. pastecart (lift(phi(drop(fstcart z)))) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^1) PCROSS (u:real^M->bool)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC;
    UNDISCH_TAC `smooth_family u (J:real->real^M->real^N)` THEN
    REWRITE_TAC[smooth_family]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^1) PCROSS (u:real^M->bool)`; `(:real^1)`;
                   `fstcart:real^(1,M)finite_sum->real^1`; `phi:real->real`]
      SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REWRITE_TAC[ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^1) PCROSS (u:real^M->bool)`;
                   `\z:real^(1,M)finite_sum. z`] SMOOTH_MAP_ON_FSTCART_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    MP_TAC(ISPECL [`(:real^1) PCROSS (u:real^M->bool)`;
                   `\z:real^(1,M)finite_sum. z`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]]);;

(* Smooth families near the sphere, time-changed and composed with the       *)
(* radial projection x / |x|: smooth on R x (R^N minus 0).                   *)

let SMT_FAMILY_NORMAL_REPARAM = prove
 (`!u (J:real->real^N->real^N) (phi:real->real).
        open u /\ sphere(vec 0,&1) SUBSET u /\ smooth_family u J /\
        smooth_map_on (:real^1) (lift o phi o drop)
        ==> smooth_family {x | ~(x = vec 0)}
                          (\t x. J (phi t) (inv(norm x) % x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `J:real->real^N->real^N`; `phi:real->real`]
    SMT_FAMILY_REPARAM) THEN
  ASM_REWRITE_TAC[smooth_family] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. (J:real->real^N->real^N) (phi(drop(fstcart z)))
          (inv(norm(sndcart z:real^N)) % sndcart z)) =
    (\z. J (phi(drop(fstcart z))) (sndcart z)) o
    (\z:real^(1,N)finite_sum. pastecart (fstcart z)
                                         (inv(norm(sndcart z)) % sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^1) PCROSS (u:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_R_PCROSS_NONZERO] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_UNIV; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  REWRITE_TAC[OPEN_R_PCROSS_NONZERO] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^1) PCROSS {x:real^N | ~(x = vec 0)}`;
                   `\z:real^(1,N)finite_sum. z`] SMOOTH_MAP_ON_FSTCART_OPEN) THEN
    REWRITE_TAC[OPEN_R_PCROSS_NONZERO; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. inv(norm(sndcart z)) % sndcart z) =
    (\x. inv(norm x) % x) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
  REWRITE_TAC[OPEN_R_PCROSS_NONZERO; OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART; IN_ELIM_THM] THEN MESON_TAC[];
    MP_TAC(ISPECL [`(:real^1) PCROSS {x:real^N | ~(x = vec 0)}`;
                   `\z:real^(1,N)finite_sum. z`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    REWRITE_TAC[OPEN_R_PCROSS_NONZERO; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]]);;

let SMOOTH_STEP_AFFINE_SMOOTH = prove
 (`!a b. smooth_map_on (:real^1) (lift o (\t. smooth_step(a * t - b)) o drop)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(a * drop x - b)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(a * drop x)`;
                 `\x:real^1. lift b`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `a:real`; `\x:real^1. x`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let SMT_NORMALIZE_SPHERE_ID = prove
 (`!x:real^N. x IN sphere(vec 0,&1) ==> inv(norm x) % x = x`,
  SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

(* Gluing two smooth maps on R x s along the time 1/2, when they agree for   *)
(* times in (1/3,2/3).                                                       *)

let SMT_TIME_GLUE_SMOOTH = prove
 (`!s (F1:real^(1,M)finite_sum->real^N) F2.
        open s /\
        smooth_map_on ((:real^1) PCROSS s) F1 /\
        smooth_map_on ((:real^1) PCROSS s) F2 /\
        (!t x. &1 / &3 < drop t /\ drop t < &2 / &3 /\ x IN s
               ==> F1(pastecart t x) = F2(pastecart t x))
        ==> smooth_map_on ((:real^1) PCROSS s)
              (\z. if drop(fstcart z) <= &1 / &2 then F1 z else F2 z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `open ({t:real^1 | drop t < &2 / &3} PCROSS (s:real^M->bool)) /\
    open ({t:real^1 | &1 / &3 < drop t} PCROSS (s:real^M->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[drop] THENL
     [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
      REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `drop t < &2 / &3` THENL
   [EXISTS_TAC `{t:real^1 | drop t < &2 / &3} PCROSS (s:real^M->bool)` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `F1:real^(1,M)finite_sum->real^N` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^M`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^1) PCROSS (s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
      SIMP_TAC[]];
    EXISTS_TAC `{t:real^1 | &1 / &3 < drop t} PCROSS (s:real^M->bool)` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `F2:real^(1,M)finite_sum->real^N` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^M`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^1) PCROSS (s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
      SIMP_TAC[]]]);;

(* Concatenation: an isotopy from a to b followed by one from b to c gives   *)
(* one from a to c, stationary outside [0,1] (each piece is run at time      *)
(* smooth_step(3t), resp. smooth_step(3t - 2), and composed with x / |x|).   *)

let SMT_SPHERE_ISOTOPY_CONCAT = prove
 (`!(J1:real->real^N->real^N) J1' J2 J2' a b c.
        sphere_isotopy J1 J1' /\ sphere_isotopy J2 J2' /\
        (!x. x IN sphere(vec 0,&1)
             ==> J1 (&0) x = a x /\ J1 (&1) x = b x /\
                 J2 (&0) x = b x /\ J2 (&1) x = c x)
        ==> ?J J'. sphere_isotopy J J' /\
                   (!t x. t <= &0 /\ x IN sphere(vec 0,&1) ==> J t x = a x) /\
                   (!t x. &1 <= t /\ x IN sphere(vec 0,&1) ==> J t x = c x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real^N->bool` STRIP_ASSUME_TAC)
                     (LABEL_TAC "s1"))
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC)
                       (LABEL_TAC "s2"))
      (LABEL_TAC "ends"))) THEN
  SUBGOAL_THEN `!y:real^N. y IN sphere(vec 0,&1)
                           ==> (J1':real->real^N->real^N) (&1) y = J2' (&0) y`
  (LABEL_TAC "junc") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(J2':real->real^N->real^N) (&0) y IN sphere(vec 0,&1)`
    ASSUME_TAC THENL [USE_THEN "s2" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN
     `(J1:real->real^N->real^N) (&1) ((J2':real->real^N->real^N) (&0) y) = y`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(J2:real->real^N->real^N) (&0) ((J2':real->real^N->real^N) (&0) y)` THEN
      CONJ_TAC THENL
       [USE_THEN "ends" (MP_TAC o SPEC `(J2':real->real^N->real^N) (&0) y`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        USE_THEN "s2" (MP_TAC o SPECL [`&0`; `y:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    USE_THEN "s1" (MP_TAC o SPECL
      [`&1`; `(J2':real->real^N->real^N) (&0) y`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u1:real^N->bool`; `J1:real->real^N->real^N`;
                 `\t. smooth_step(&3 * t - &0)`] SMT_FAMILY_NORMAL_REPARAM) THEN
  ASM_REWRITE_TAC[SMOOTH_STEP_AFFINE_SMOOTH; REAL_SUB_RZERO; smooth_family] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`u1:real^N->bool`; `J1':real->real^N->real^N`;
                 `\t. smooth_step(&3 * t - &0)`] SMT_FAMILY_NORMAL_REPARAM) THEN
  ASM_REWRITE_TAC[SMOOTH_STEP_AFFINE_SMOOTH; REAL_SUB_RZERO; smooth_family] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`u2:real^N->bool`; `J2:real->real^N->real^N`;
                 `\t. smooth_step(&3 * t - &2)`] SMT_FAMILY_NORMAL_REPARAM) THEN
  ASM_REWRITE_TAC[SMOOTH_STEP_AFFINE_SMOOTH; smooth_family] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`u2:real^N->bool`; `J2':real->real^N->real^N`;
                 `\t. smooth_step(&3 * t - &2)`] SMT_FAMILY_NORMAL_REPARAM) THEN
  ASM_REWRITE_TAC[SMOOTH_STEP_AFFINE_SMOOTH; smooth_family] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. &1 / &3 < t /\ t < &2 / &3
        ==> smooth_step(&3 * t) = &1 /\ smooth_step(&3 * t - &2) = &0`
  (LABEL_TAC "mid") THENL
   [REPEAT STRIP_TAC THENL [MATCH_MP_TAC SMOOTH_STEP_1; MATCH_MP_TAC SMOOTH_STEP_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\t x. if t <= &1 / &2
           then (J1:real->real^N->real^N) (smooth_step(&3 * t)) (inv(norm x) % x)
           else J2 (smooth_step(&3 * t - &2)) (inv(norm x) % x)`;
    `\t x. if t <= &1 / &2
           then (J1':real->real^N->real^N) (smooth_step(&3 * t)) (inv(norm x) % x)
           else J2' (smooth_step(&3 * t - &2)) (inv(norm x) % x)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    REWRITE_TAC[OPEN_NONZERO; smooth_family] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`;
        `\z:real^(1,N)finite_sum. (J1:real->real^N->real^N)
           (smooth_step(&3 * drop(fstcart z))) (inv(norm(sndcart z)) % sndcart z)`;
        `\z:real^(1,N)finite_sum. (J2:real->real^N->real^N)
           (smooth_step(&3 * drop(fstcart z) - &2)) (inv(norm(sndcart z)) % sndcart z)`]
        SMT_TIME_GLUE_SMOOTH) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; FSTCART_PASTECART; SNDCART_PASTECART;
                      IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "mid" (MP_TAC o SPEC `drop t`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      USE_THEN "ends" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE]);
      MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`;
        `\z:real^(1,N)finite_sum. (J1':real->real^N->real^N)
           (smooth_step(&3 * drop(fstcart z))) (inv(norm(sndcart z)) % sndcart z)`;
        `\z:real^(1,N)finite_sum. (J2':real->real^N->real^N)
           (smooth_step(&3 * drop(fstcart z) - &2)) (inv(norm(sndcart z)) % sndcart z)`]
        SMT_TIME_GLUE_SMOOTH) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; FSTCART_PASTECART; SNDCART_PASTECART;
                      IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "mid" (MP_TAC o SPEC `drop t`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      USE_THEN "junc" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE])];
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "s1" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE_ID]);
      USE_THEN "s2" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE_ID])];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t <= &1 / &2 /\ smooth_step(&3 * t) = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    USE_THEN "ends" (fun th -> ASM_SIMP_TAC[th]);
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(t <= &1 / &2) /\ smooth_step(&3 * t - &2) = &1` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    USE_THEN "ends" (fun th -> ASM_SIMP_TAC[th])]);;

(* Time changes and orthogonal post-composition of sphere isotopies. *)

let SMT_SPHERE_ISOTOPY_REPARAM = prove
 (`!(J:real->real^N->real^N) J' phi.
        sphere_isotopy J J' /\ smooth_map_on (:real^1) (lift o phi o drop)
        ==> sphere_isotopy (\t. J (phi t)) (\t. J' (phi t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMT_FAMILY_REPARAM THEN ASM_REWRITE_TAC[]);;

let SMT_SPHERE_ISOTOPY_ORTHO = prove
 (`!(J:real->real^N->real^N) J' Q.
        sphere_isotopy J J' /\ orthogonal_transformation Q
        ==> ?K'. sphere_isotopy (\t x. Q(J t x)) K'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
                     (LABEL_TAC "s"))
    ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Q':real^N->real^N` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  SUBGOAL_THEN `(!v:real^N. norm((Q:real^N->real^N) v) = norm v) /\
                (!v:real^N. norm((Q':real^N->real^N) v) = norm v) /\
                linear (Q:real^N->real^N) /\ linear (Q':real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `orthogonal_transformation (Q:real^N->real^N)` THEN
      SIMP_TAC[ORTHOGONAL_TRANSFORMATION];
      UNDISCH_TAC `orthogonal_transformation (Q':real^N->real^N)` THEN
      SIMP_TAC[ORTHOGONAL_TRANSFORMATION];
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN sphere(vec 0,&1)
                           ==> (Q:real^N->real^N) x IN sphere(vec 0,&1) /\
                               (Q':real^N->real^N) x IN sphere(vec 0,&1)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_SPHERE_0] THEN SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\t x. (J':real->real^N->real^N) t ((Q':real^N->real^N) x)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "s" (fun th -> ASM_SIMP_TAC[th])] THEN
  EXISTS_TAC `u INTER {x:real^N | (Q':real^N->real^N) x IN u}` THEN
  SUBGOAL_THEN `open (u INTER {x:real^N | (Q':real^N->real^N) x IN u})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[smooth_family] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^1) PCROSS (u:real^N->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTER] THEN
      SIMP_TAC[];
      MP_TAC(ISPECL [`(:real^1) PCROSS (u:real^N->bool)`;
                     `\z:real^(1,N)finite_sum. (J:real->real^N->real^N)
                         (drop(fstcart z)) (sndcart z)`;
                     `Q:real^N->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; o_DEF] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `smooth_family u (J:real->real^N->real^N)` THEN
      REWRITE_TAC[smooth_family]];
    SUBGOAL_THEN
     `(\z. (J':real->real^N->real^N) (drop(fstcart z))
             ((Q':real^N->real^N) (sndcart z))) =
      (\z. J' (drop(fstcart z)) (sndcart z)) o
      (\z:real^(1,N)finite_sum. pastecart (fstcart z) (Q'(sndcart z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^1) PCROSS (u:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTER; IN_ELIM_THM;
                  IN_UNIV] THEN
      SIMP_TAC[];
      MP_TAC(ISPECL [`(:real^1) PCROSS (u INTER {x:real^N | (Q':real^N->real^N) x IN u})`;
                     `\z:real^(1,N)finite_sum. z`;
                     `\z:real^(1,N)finite_sum. pastecart (fstcart z)
                                                ((Q':real^N->real^N) (sndcart z))`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LINEAR_PASTECART THEN
      REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_FSTCART] THEN
      MP_TAC(ISPECL [`sndcart:real^(1,N)finite_sum->real^N`; `Q':real^N->real^N`]
        LINEAR_COMPOSE) THEN
      ASM_REWRITE_TAC[LINEAR_SNDCART; o_DEF];
      UNDISCH_TAC `smooth_family u (J':real->real^N->real^N)` THEN
      REWRITE_TAC[smooth_family]]]);;

(* ------------------------------------------------------------------------- *)
(* S2 from S7 (pole normalisation), S3 (planar isotopies) and                *)
(* S8 (stereographic transport).  The diffeomorphism f1 of S^2, equal to the *)
(* identity near the north pole basis 3, is conjugated by stereo2_n to a     *)
(* compactly supported diffeomorphism of R^2.                                *)
(* ------------------------------------------------------------------------- *)

let SMT_STEREO2_INV_NEAR_POLE = prove
 (`!y. norm(stereo2_n_inv y - basis 3) pow 2 = &4 / (norm y pow 2 + &1)`,
  GEN_TAC THEN
  SIMP_TAC[NORM_POW_2; DOT_3; DOT_2; VECTOR_SUB_COMPONENT;
           STEX_STEREO2_N_INV_COMPONENTS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  MP_TAC(SPEC `(y:real^2)$1` REAL_LE_SQUARE) THEN
  MP_TAC(SPEC `(y:real^2)$2` REAL_LE_SQUARE) THEN
  CONV_TAC REAL_FIELD);;

let SMT_STEREO2_INV_CLOSE = prove
 (`!e y. &0 < e /\ &2 / e <= norm y ==> norm(stereo2_n_inv y - basis 3) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(stereo2_n_inv y - basis 3) pow 2 < e pow 2` MP_TAC THENL
   [REWRITE_TAC[SMT_STEREO2_INV_NEAR_POLE] THEN
    SUBGOAL_THEN `&0 < norm(y:real^2) pow 2 + &1` ASSUME_TAC THENL
     [MP_TAC(SPEC `norm(y:real^2)` REAL_LE_SQUARE) THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `&2 <= norm(y:real^2) * e` ASSUME_TAC THENL
     [UNDISCH_TAC `&2 / e <= norm(y:real^2)` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 pow 2 <= (norm(y:real^2) * e) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS; REAL_ABS_NORM] THEN ASM_REAL_ARITH_TAC]);;

(* Conjugation by stereographic projection from the north pole. *)

let SMT_STEREO_CONJ_SMOOTH = prove
 (`!f:real^3->real^3.
        smooth_near (sphere(vec 0,&1)) f /\
        (!x. x IN sphere(vec 0,&1) DELETE basis 3
             ==> f x IN sphere(vec 0,&1) DELETE basis 3)
        ==> smooth_map_on (:real^2) (\y. stereo2_n(f(stereo2_n_inv y)))`,
  REWRITE_TAC[smooth_near] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | x IN u /\ (f:real^3->real^3) x IN {x:real^3 | x$3 < &1}}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. stereo2_n((f:real^3->real^3)(stereo2_n_inv y))) =
                (stereo2_n o f) o stereo2_n_inv` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | x IN u /\ (f:real^3->real^3) x IN {x:real^3 | x$3 < &1}}` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^2` THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET u` THEN
      UNDISCH_TAC `stereo2_n_inv y IN sphere(vec 0:real^3,&1) DELETE basis 3` THEN
      SET_TAC[];
      MP_TAC STEX_STEREO2_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; STEX_STEREO2_N_SMOOTH] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let SMT_PLANAR_CONJUGATE = prove
 (`!f1 g1:real^3->real^3 e.
        sphere_diffeo f1 g1 /\ &0 < e /\
        (!x. x IN sphere(vec 0,&1) /\ norm(x - basis 3) < e ==> f1 x = x)
        ==> (!x. x IN sphere(vec 0,&1) DELETE basis 3
                 ==> f1 x IN sphere(vec 0,&1) DELETE basis 3 /\
                     g1 x IN sphere(vec 0,&1) DELETE basis 3) /\
            f1(basis 3) = basis 3 /\
            diffeomorphism_on (:real^2) (:real^2)
              (\y. stereo2_n(f1(stereo2_n_inv y)))
              (\y. stereo2_n(g1(stereo2_n_inv y))) /\
            (!y. &2 / e <= norm y ==> stereo2_n(f1(stereo2_n_inv y)) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fg")))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real^3->real^3)(basis 3) = basis 3` ASSUME_TAC THENL
   [USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^3->real^3)(basis 3) = basis 3` ASSUME_TAC THENL
   [USE_THEN "fg" (MP_TAC o SPEC `basis 3:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) DELETE basis 3
        ==> (f1:real^3->real^3) x IN sphere(vec 0,&1) DELETE basis 3 /\
            (g1:real^3->real^3) x IN sphere(vec 0,&1) DELETE basis 3`
  (LABEL_TAC "del") THENL
   [REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "fg" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x:real^3 = basis 3)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. stereo2_n((g1:real^3->real^3)(stereo2_n_inv(stereo2_n
            ((f1:real^3->real^3)(stereo2_n_inv y))))) = y) /\
    (!y. stereo2_n((f1:real^3->real^3)(stereo2_n_inv(stereo2_n
            ((g1:real^3->real^3)(stereo2_n_inv y))))) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN DISCH_TAC THEN
    USE_THEN "del" (MP_TAC o SPEC `stereo2_n_inv y`) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[STEX_STEREO2_N_LEFT] THEN
    USE_THEN "fg" (MP_TAC o SPEC `stereo2_n_inv y`) THEN
    (ANTS_TAC THENL [UNDISCH_TAC `stereo2_n_inv y IN sphere(vec 0:real^3,&1) DELETE basis 3` THEN
                     SIMP_TAC[IN_DELETE]; ALL_TAC]) THEN
    SIMP_TAC[STEX_STEREO2_N_RIGHT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
      EXISTS_TAC `stereo2_n((g1:real^3->real^3)(stereo2_n_inv y))` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
      EXISTS_TAC `stereo2_n((f1:real^3->real^3)(stereo2_n_inv y))` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMT_STEREO_CONJ_SMOOTH THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMT_STEREO_CONJ_SMOOTH THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f1:real^3->real^3)(stereo2_n_inv y) = stereo2_n_inv y`
     (fun th -> REWRITE_TAC[th; STEX_STEREO2_N_RIGHT]) THEN
    USE_THEN "near" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMT_STEREO2_INV_CLOSE] THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN SIMP_TAC[IN_DELETE]]);;

let SMT_REVERSE_TIME_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o (\t. &1 - t) o drop)`,
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1)`; `\x:real^1. x`]
    SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

(* S2 from S7, S3 and S8: f ~ Q o f1 (S7, reversed), Q o f1 ~ Q (S3 for the  *)
(* stereographic conjugate of f1, transported back by S8, composed with Q,  *)
(* reversed), concatenated.                                                  *)

let SMT_SPHERE_ISOTOPY_FROM_PARTS = prove
 (`SMT_SPHERE_POLE_STATEMENT /\ SMT_PLANAR_ISOTOPY_STATEMENT /\
   SMT_STEREO_TRANSPORT_STATEMENT
   ==> SMT_SPHERE_ISOTOPY_STATEMENT`,
  REWRITE_TAC[SMT_SPHERE_POLE_STATEMENT; SMT_PLANAR_ISOTOPY_STATEMENT;
              SMT_STEREO_TRANSPORT_STATEMENT; SMT_SPHERE_ISOTOPY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "S7")
    (CONJUNCTS_THEN2 (LABEL_TAC "S3") (LABEL_TAC "S8"))) THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN DISCH_TAC THEN
  USE_THEN "S7" (MP_TAC o SPECL [`f:real^3->real^3`; `g:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J1:real->real^3->real^3` (X_CHOOSE_THEN
    `J1':real->real^3->real^3` (X_CHOOSE_THEN `Q:real^3->real^3`
    (X_CHOOSE_THEN `f1:real^3->real^3` (X_CHOOSE_THEN `g1:real^3->real^3`
    (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "J1a") (CONJUNCTS_THEN2 (LABEL_TAC "J1b")
       (LABEL_TAC "near"))))))))))))) THEN
  MP_TAC(ISPECL [`f1:real^3->real^3`; `g1:real^3->real^3`; `e:real`]
    SMT_PLANAR_CONJUGATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "del") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "supp")))) THEN
  USE_THEN "S3" (MP_TAC o SPECL
   [`\y. stereo2_n((f1:real^3->real^3)(stereo2_n_inv y))`;
    `\y. stereo2_n((g1:real^3->real^3)(stereo2_n_inv y))`; `&2 / e`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real^2->real^2` (X_CHOOSE_THEN
    `K:real->real^2->real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H0") (CONJUNCTS_THEN2 (LABEL_TAC "H1")
      (X_CHOOSE_TAC `R:real`)))))) THEN
  USE_THEN "S8" (MP_TAC o SPECL
   [`H:real->real^2->real^2`; `K:real->real^2->real^2`; `R:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J2:real->real^3->real^3` (X_CHOOSE_THEN
    `J2':real->real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "J2def") (LABEL_TAC "J2N"))))) THEN
  (* the end values of the transported isotopy *)
  SUBGOAL_THEN `!x. x IN sphere(vec 0,&1)
                    ==> (J2:real->real^3->real^3) (&0) x = f1 x /\ J2 (&1) x = x`
  (LABEL_TAC "J2ends") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^3 = basis 3` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN sphere(vec 0,&1) DELETE basis 3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    USE_THEN "J2def" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "H0" (MP_TAC o SPECL [`&0`; `stereo2_n x`]) THEN
    USE_THEN "H1" (MP_TAC o SPECL [`&1`; `stereo2_n x`]) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[STEX_STEREO2_N_LEFT] THEN
    USE_THEN "del" (MP_TAC o SPEC `x:real^3`) THEN
    ASM_SIMP_TAC[STEX_STEREO2_N_LEFT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J2:real->real^3->real^3`; `J2':real->real^3->real^3`;
                 `Q:real^3->real^3`] SMT_SPHERE_ISOTOPY_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K2:real->real^3->real^3`) THEN
  MP_TAC(ISPECL [`\t x. (Q:real^3->real^3)((J2:real->real^3->real^3) t x)`;
                 `K2:real->real^3->real^3`; `\t. &1 - t`]
    SMT_SPHERE_ISOTOPY_REPARAM) THEN
  ASM_REWRITE_TAC[SMT_REVERSE_TIME_SMOOTH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J1:real->real^3->real^3`; `J1':real->real^3->real^3`;
                 `\t. &1 - t`] SMT_SPHERE_ISOTOPY_REPARAM) THEN
  ASM_REWRITE_TAC[SMT_REVERSE_TIME_SMOOTH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. (\t x. (Q:real^3->real^3)((J2:real->real^3->real^3) t x)) (&1 - t)`;
    `\t. (K2:real->real^3->real^3) (&1 - t)`;
    `\t. (J1:real->real^3->real^3) (&1 - t)`;
    `\t. (J1':real->real^3->real^3) (&1 - t)`;
    `Q:real^3->real^3`; `(Q:real^3->real^3) o (f1:real^3->real^3)`;
    `f:real^3->real^3`] SMT_SPHERE_ISOTOPY_CONCAT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; o_THM] THEN
    USE_THEN "J2ends" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "J1a" (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]) THEN
    USE_THEN "J1b" (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->real^3->real^3` (X_CHOOSE_THEN
    `J':real->real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`J:real->real^3->real^3`; `J':real->real^3->real^3`; `Q:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let SMT_SMALE_FROM_PARTS = prove
 (`SMT_SPHERE_POLE_STATEMENT /\ SMT_PLANAR_ISOTOPY_STATEMENT /\
   SMT_STEREO_TRANSPORT_STATEMENT
   ==> SMT_SMALE_RADIAL_STATEMENT`,
  MESON_TAC[SMT_SPHERE_ISOTOPY_FROM_PARTS; SMT_SMALE_FROM_ISOTOPY]);;

(* ------------------------------------------------------------------------- *)
(* S8, stereographic transport of compactly supported planar                 *)
(* isotopies to sphere isotopies fixing the north pole.  The transported     *)
(* family is extended to R^3 minus 0 through x / |x|; near the pole it is   *)
(* the radial projection itself.                                             *)
(* ------------------------------------------------------------------------- *)

let SMT_SPHERE_POLE_CRITERION = prove
 (`!x:real^3. x IN sphere(vec 0,&1) ==> (x$3 < &1 <=> ~(x = basis 3))`,
  REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] STEX_SPHERE_COMPONENT_POLE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Near the pole, stereographic projection is far from the origin. *)

let SMT_STEREO2_FAR = prove
 (`!R p. p IN sphere(vec 0,&1) /\ &1 - inv(R pow 2 + &2) < p$3 /\ p$3 < &1
         ==> R <= norm(stereo2_n p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p IN sphere(vec 0:real^3,&1) DELETE basis 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[SMT_SPHERE_POLE_CRITERION];
    ALL_TAC] THEN
  MP_TAC(SPEC `p:real^3` STEX_STEREO2_N_NORM2) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `R <= &0` THENL
   [MP_TAC(ISPEC `stereo2_n p` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs R <= abs n /\ &0 <= n ==> R <= n`) THEN
  REWRITE_TAC[NORM_POS_LE; REAL_LE_SQUARE_ABS] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &1 - (p:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 < R pow 2 + &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `R:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - (p:real^3)$3) * (R pow 2 + &2) < &1` MP_TAC THENL
   [SUBGOAL_THEN `inv(R pow 2 + &2) * (R pow 2 + &2) = &1`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `R:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `&0 < &1 - (p:real^3)$3` THEN CONV_TAC REAL_ARITH);;

let SMT_OPEN_NORMALIZED_HALFSPACES = prove
 (`!a. open {x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < a} /\
       open {x:real^3 | ~(x = vec 0) /\ a < (inv(norm x) % x)$3}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^3. inv(norm x) % x`; `{x:real^3 | ~(x = vec 0)}`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_NORMALIZE; OPEN_NONZERO] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `{y:real^3 | y$3 < a}` th) THEN
    MP_TAC(SPEC `{y:real^3 | y$3 > a}` th)) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT;
              IN_ELIM_THM; real_gt] THEN
  SIMP_TAC[]);;

let SMT_STEREO_NORMALIZED_SMOOTH = prove
 (`smooth_map_on {x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}
                 (\x. stereo2_n(inv(norm x) % x))`,
  SUBGOAL_THEN `(\x:real^3. stereo2_n(inv(norm x) % x)) =
                stereo2_n o (\x. inv(norm x) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
  REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; OPEN_HALFSPACE_COMPONENT_LT;
              STEX_STEREO2_N_SMOOTH] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE] THEN SET_TAC[]]);;

let SMT_STEREO_FAMILY_SMOOTH = prove
 (`!(H:real->real^2->real^2) R.
        smooth_family (:real^2) H /\ (!t x. R <= norm x ==> H t x = x)
        ==> smooth_family {x:real^3 | ~(x = vec 0)}
              (\t x. if (inv(norm x) % x)$3 < &1
                     then stereo2_n_inv(H t (stereo2_n(inv(norm x) % x)))
                     else inv(norm x) % x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "supp")) THEN
  REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN DISCH_TAC THEN
  ABBREV_TAC `W1 = {x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
  ABBREV_TAC `W2 = {x:real^3 | ~(x = vec 0) /\
                               &1 - inv(R pow 2 + &2) < (inv(norm x) % x)$3}` THEN
  SUBGOAL_THEN `open (W1:real^3->bool) /\ open (W2:real^3->bool)` STRIP_ASSUME_TAC
  THENL [MAP_EVERY EXPAND_TAC ["W1"; "W2"] THEN
         REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES]; ALL_TAC] THEN
  (* the piece away from the pole *)
  SUBGOAL_THEN
   `smooth_map_on ((:real^1) PCROSS (W1:real^3->bool))
      (\z:real^(1,3)finite_sum. stereo2_n_inv((H:real->real^2->real^2) (drop(fstcart z))
             (stereo2_n(inv(norm(sndcart z)) % sndcart z))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. stereo2_n_inv((H:real->real^2->real^2) (drop(fstcart z))
             (stereo2_n(inv(norm(sndcart z)) % sndcart z)))) =
      stereo2_n_inv o (\w. H (drop(fstcart w)) (sndcart w)) o
      (\z:real^(1,3)finite_sum.
           pastecart (fstcart z) (stereo2_n(inv(norm(sndcart z)) % sndcart z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SUBSET_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^(1,2)finite_sum)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1) PCROSS (W1:real^3->bool)`;
                     `\z:real^(1,3)finite_sum. z`] SMOOTH_MAP_ON_FSTCART_OPEN) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. stereo2_n(inv(norm(sndcart z)) % sndcart z)) =
      (\x. stereo2_n(inv(norm x) % x)) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W1:real^3->bool` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`(:real^1) PCROSS (W1:real^3->bool)`;
                     `\z:real^(1,3)finite_sum. z`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      EXPAND_TAC "W1" THEN REWRITE_TAC[SMT_STEREO_NORMALIZED_SMOOTH]];
    ALL_TAC] THEN
  (* the piece near the pole is the radial projection *)
  SUBGOAL_THEN
   `smooth_map_on ((:real^1) PCROSS (W2:real^3->bool))
      (\z:real^(1,3)finite_sum. inv(norm(sndcart z)) % sndcart z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. inv(norm(sndcart z)) % sndcart z) =
      (\x. inv(norm x) % x) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W2" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART; IN_ELIM_THM] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`(:real^1) PCROSS (W2:real^3->bool)`;
                     `\z:real^(1,3)finite_sum. z`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_R_PCROSS_NONZERO] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^3`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(inv(norm x) % x:real^3)$3 < &1` THENL
   [EXISTS_TAC `(:real^1) PCROSS (W1:real^3->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
    CONJ_TAC THENL [EXPAND_TAC "W1" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z:real^(1,3)finite_sum. stereo2_n_inv((H:real->real^2->real^2) (drop(fstcart z))
            (stereo2_n(inv(norm(sndcart z)) % sndcart z)))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W1" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    EXISTS_TAC `(:real^1) PCROSS (W2:real^3->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W2" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ ~(a < &1) ==> &1 - e < a`) THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
      MP_TAC(SPEC `R:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,3)finite_sum. inv(norm(sndcart z)) % sndcart z` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W2" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^3`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(norm y) % y IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE]; ALL_TAC] THEN
    SUBGOAL_THEN `R <= norm(stereo2_n(inv(norm y) % (y:real^3)))` ASSUME_TAC THENL
     [MATCH_MP_TAC SMT_STEREO2_FAR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "supp" (fun th -> ASM_SIMP_TAC[th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[SMT_SPHERE_POLE_CRITERION]]);;

(* S8. *)

let SMT_STEREO_TRANSPORT = prove
 (`SMT_STEREO_TRANSPORT_STATEMENT`,
  REWRITE_TAC[SMT_STEREO_TRANSPORT_STATEMENT; diffeo_isotopy] THEN
  MAP_EVERY X_GEN_TAC
   [`H:real->real^2->real^2`; `K:real->real^2->real^2`; `R:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dH")))
    (LABEL_TAC "supp")) THEN
  SUBGOAL_THEN `!t:real. (!y:real^2. (K:real->real^2->real^2) t (H t y) = y) /\
                         (!y. H t (K t y) = y)` (LABEL_TAC "inv") THENL
   [GEN_TAC THEN USE_THEN "dH" (MP_TAC o SPEC `t:real`) THEN
    SIMP_TAC[diffeomorphism_on; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t y. R <= norm y ==> (K:real->real^2->real^2) t y = y`
  (LABEL_TAC "suppK") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(H:real->real^2->real^2) t y = y` ASSUME_TAC THENL
     [USE_THEN "supp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. stereo2_n_inv y IN sphere(vec 0,&1) /\
                           (stereo2_n_inv y)$3 < &1 /\
                           stereo2_n_inv y IN sphere(vec 0,&1) DELETE basis 3`
  (LABEL_TAC "sinv") THENL
   [GEN_TAC THEN MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `stereo2_n_inv y` SMT_SPHERE_POLE_CRITERION) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\t x. if (inv(norm x) % x)$3 < &1
           then stereo2_n_inv((H:real->real^2->real^2) t (stereo2_n(inv(norm x) % x)))
           else inv(norm x) % x`;
    `\t x. if (inv(norm x) % x)$3 < &1
           then stereo2_n_inv((K:real->real^2->real^2) t (stereo2_n(inv(norm x) % x)))
           else inv(norm x) % x`] THEN
  REWRITE_TAC[sphere_isotopy] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN REWRITE_TAC[OPEN_NONZERO] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMT_STEREO_FAMILY_SMOOTH THEN EXISTS_TAC `R:real` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMT_STEREO_FAMILY_SMOOTH THEN EXISTS_TAC `R:real` THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(x:real^3) IN sphere(vec 0,&1) DELETE basis 3` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_DELETE] THEN
        MP_TAC(SPEC `x:real^3` SMT_SPHERE_POLE_CRITERION) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "sinv" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE_ID;
                                              STEX_STEREO2_N_RIGHT]) THEN
      USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[STEX_STEREO2_N_LEFT];
      ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    SUBGOAL_THEN `(x:real^3)$3 < &1` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `x:real^3` SMT_SPHERE_POLE_CRITERION) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    SUBGOAL_THEN `~((basis 3:real^3)$3 < &1)` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `basis 3:real^3` SMT_SPHERE_POLE_CRITERION) THEN ASM_REWRITE_TAC[]]);;

(* Smale's theorem in radial form from S7 and S3. *)

let SMT_SMALE_FROM_POLE_PLANAR = prove
 (`SMT_SPHERE_POLE_STATEMENT /\ SMT_PLANAR_ISOTOPY_STATEMENT
   ==> SMT_SMALE_RADIAL_STATEMENT`,
  MESON_TAC[SMT_SMALE_FROM_PARTS; SMT_STEREO_TRANSPORT]);;

