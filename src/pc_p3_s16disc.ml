(* ========================================================================= *)
(* Unit pc_p3_s16disc (Part 3 proofs; MT Ch 16, Claim 16.10 for Prop 16.5,   *)
(* repairing a gap of MT's proof): an event removes the image of a ball      *)
(* close to the standard solution whole or not at all.  P3N_INNER_NECK: a    *)
(* level set of the distance from the tip is the central sphere of an        *)
(* eps-neck of the slice.  P3N_SLICE_DISC: no central sphere of a            *)
(* short-scale neck meets the ball.  P3N_DISC: the history form at an event, *)
(* with the dichotomy kept whole or discarded whole.                         *)
(*                                                                           *)
(* Contents: the event dichotomy; the power map and the nc coordinates of    *)
(* the shrinking cylinder; the inner neck; curves, scales and the neck       *)
(* containment; the slice form; the history form.                            *)
(* ========================================================================= *)

needs "src/pc_p3_s16cap0.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;


let P3N_EVENT_DICHOTOMY = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev (B:A->bool).
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     B SUBSET topspace topX /\ connected_in topX B /\
     DISJOINT B (mfd_cut_spheres (ev_index ev) (ev_neck ev))
     ==> B SUBSET topspace topY \/ DISJOINT B (topspace topY)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok; mfd_cut_cap; mfd_diffeo] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_in (ev_ztop (ev:(A)rfs_event)) B` ASSUME_TAC THENL
   [SUBGOAL_THEN `connected_in
                   (subtopology (ev_ztop (ev:(A)rfs_event))
                      (topspace (ev_ztop ev) DIFF
                       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev)))
                   (IMAGE (\x:A. x) B)` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology topX (topspace topX DIFF
                    mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event)))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[homeomorphic_maps]; ALL_TAC] THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; IMAGE_ID] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ev_ztop (ev:(A)rfs_event)`; `B:A->bool`; `ev_disc (ev:(A)rfs_event)`]
         CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(B:A->bool) SUBSET topspace(ev_ztop (ev:(A)rfs_event))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The power map p3n_pw a (|y| -> |y|^a along rays).  For                   *)
(* a^2 = 1 - s it pulls the shrinking cylinder cylinder_flow s back to      *)
(* (1 - s) cylinder_flow 0 (P3N_PW_CYL), so level spheres of the time-s    *)
(* cylinder structure are level spheres of a neck; diffeomorphism between  *)
(* annuli (P3N_PW_DIFFEO).                                                  *)
(* ========================================================================= *)

let p3n_pw = new_definition
 `p3n_pw (a:real) (y:real^3) = (exp(a * log(norm y)) * inv(norm y)) % y`;;

let P3N_PW_NORM = prove
 (`!a y:real^3. ~(y = vec 0)
     ==> norm(p3n_pw a y) = exp(a * log(norm y)) /\ ~(p3n_pw a y = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN
  REWRITE_TAC[p3n_pw; NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  SIMP_TAC[REAL_ABS_EXP] THEN
  SUBGOAL_THEN `(exp(a * log(norm(y:real^3))) * inv(norm y)) * norm y =
                exp(a * log(norm y))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_POS_LT]);;

let P3N_PW_INV = prove
 (`!a y:real^3. &0 < a /\ ~(y = vec 0) ==> p3n_pw (inv a) (p3n_pw a y) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `y:real^3`] P3N_PW_NORM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV) [p3n_pw] THEN ASM_REWRITE_TAC[LOG_EXP] THEN
  REWRITE_TAC[p3n_pw; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `exp(inv a * a * log(norm(y:real^3))) = norm y` SUBST1_TAC THENL
   [SUBGOAL_THEN `inv a * a * log(norm(y:real^3)) = log(norm y)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  MP_TAC(SPEC `a * log(norm(y:real^3))` REAL_EXP_POS_LT) THEN
  UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD);;

let P3N_PW_DERIV = prove
 (`!a y:real^3. ~(y = vec 0)
     ==> (p3n_pw a has_derivative
          (\h. (exp(a * log(norm y)) * inv(norm y)) % h +
               ((a - &1) * exp(a * log(norm y)) * inv(norm y pow 3) * (y dot h)) % y))
         (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p3n_pw a = (\z:real^3. (exp(a * log(norm z)) * inv(norm z)) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3n_pw]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\r. exp(a * log r)`;
    `(a * &1 * inv(norm(y:real^3))) * exp(a * log(norm y))`; `y:real^3`]
    P3S_RADMAP_GEN_DERIV)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(INST [`norm(y:real^3)`,`r:real`]
      (REAL_DIFF_CONV `((\r. exp(a * log r)) has_real_derivative f) (atreal r)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^3` THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD);;

let P3N_OUTER_MUL = prove
 (`!y x:real^3. ((lambda i j. y$i * y$j):real^3^3) ** x = (y dot x) % y`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; FORALL_3; SUM_3;
           dot; VECTOR_MUL_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let P3N_MATRIX_EQ_DOT = prove
 (`!A B:real^3^3. (!v w. w dot (A ** v) = w dot (B ** v)) ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `v:real^3` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
  REWRITE_TAC[DOT_RSUB] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[DOT_LSUB; REAL_SUB_REFL]);;

let P3N_PW_CYL = prove
 (`!a s y:real^3. &0 < a /\ a pow 2 = &1 - s /\ ~(y = vec 0)
     ==> mpullback (p3n_pw a) (cylinder_flow s) y = (&1 - s) %% cylinder_flow (&0) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `y:real^3`] P3N_PW_NORM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `y:real^3`] P3N_PW_DERIV) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f' = (\h:real^3. (exp(a * log(norm y)) * inv(norm y)) % h +
                     ((a - &1) * exp(a * log(norm y)) * inv(norm y pow 3) * (y dot h)) % y)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `linear(f':real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC P3N_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; P3N_OUTER_MUL] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "f'" THEN
  REWRITE_TAC[p3n_pw] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_SQUARE_NORM] THEN
  ABBREV_TAC `e = exp(a * log(norm(y:real^3)))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  ABBREV_TAC `ny = norm(y:real^3)` THEN
  ABBREV_TAC `p = (v:real^3) dot y` THEN ABBREV_TAC `q = (w:real^3) dot y` THEN
  ABBREV_TAC `r = (w:real^3) dot v` THEN
  SUBGOAL_THEN `(y:real^3) dot v = p /\ (y:real^3) dot w = q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 < ny`; `a pow 2 = &1 - s`] THEN
  CONV_TAC REAL_FIELD);;

let P3N_PW_SMOOTH = prove
 (`!a. smooth_map_on ((:real^3) DELETE vec 0) (p3n_pw a)`,
  GEN_TAC THEN
  SUBGOAL_THEN `p3n_pw a = (\x:real^3. drop(lift(exp(a * log(norm x)) * inv(norm x))) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3n_pw; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  SIMP_TAC[SMOOTH_MAP_ON_ID; OPEN_DELETE; OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift((\t. exp((a - &1) * t)) (drop(lift(log(norm x)))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DELETE; IN_UNIV; LIFT_DROP] THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID; real_sub; REAL_EXP_ADD; REAL_EXP_NEG] THEN
    ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_UNIV; P3S_LIFT_LOGNORM_SMOOTH] THEN
  MATCH_MP_TAC P2C_S1_EXP THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_ID; ETA_AX]);;


let P3N_PW_DIFFEO = prove
 (`!a r1 r2. &0 < a /\ &0 < r1 /\ r1 < r2
     ==> diffeomorphism_on (annulus r1 r2)
           (annulus (exp(a * log r1)) (exp(a * log r2)))
           (p3n_pw a) (p3n_pw (inv a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv a` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN annulus r1 r2
      ==> ~(y = vec 0) /\ p3n_pw a y IN annulus (exp(a * log r1)) (exp(a * log r2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3N_PW_NORM; REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `log r1 < log(norm(y:real^3)) /\ log(norm y) < log r2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN annulus (exp(a * log r1)) (exp(a * log r2))
      ==> ~(z = vec 0) /\ p3n_pw (inv a) z IN annulus r1 r2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN MP_TAC(SPEC `a * log r1` REAL_EXP_POS_LT) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3N_PW_NORM] THEN
    SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `a * log r1 < log(norm(z:real^3)) /\ log(norm z) < a * log r2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
        ASM_REWRITE_TAC[REAL_EXP_POS_LT];
        GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `log r1 < inv a * log(norm(z:real^3)) /\ inv a * log(norm z) < log r2`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `log r1 = inv a * (a * log r1) /\ log r2 = inv a * (a * log r2)`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
        ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < r1`))] THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < r2`))] THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `p3n_pw (inv a) (z:real^3)` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`inv a`; `z:real^3`] P3N_PW_INV) THEN ASM_SIMP_TAC[REAL_INV_INV];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `p3n_pw a (y:real^3)` THEN ASM_SIMP_TAC[P3N_PW_INV];
    ASM_MESON_TAC[P3N_PW_INV];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`inv a`; `z:real^3`] P3N_PW_INV) THEN ASM_SIMP_TAC[REAL_INV_INV];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[P3N_PW_SMOOTH] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[P3N_PW_SMOOTH] THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* The radial parametrization psi = ncinv o (c .) o p3n_pw a of              *)
(* the band d0 - a/eps < d < d0 + a/eps of the standard initial metric by    *)
(* the neck domain (P3N_PSI_DIFFEO), mapping the unit sphere onto the       *)
(* distance sphere d = d0 (P3N_PSI_SPHERE); dilation invariance of the      *)
(* shrinking cylinder and the joint scaling of lck_dist2.                    *)
(* ========================================================================= *)

let P3N_CYL_DILATION = prove
 (`!c s y:real^3.
        &0 < c /\ ~(y = vec 0)
        ==> mpullback (\x:real^3. c % x) (cylinder_flow s) y = cylinder_flow s y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^3. c % x) (at y) = (\x. (c %% mat 1) ** x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; TRANSP_MATRIX_CMUL; TRANSP_MAT;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_MUL_RID;
              MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[cylinder_flow; NORM_MUL; MATRIX_CMUL_ADD_LDISTRIB; MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `abs c = c /\ ~(norm(y:real^3) = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((lambda i j. (c % y:real^3)$i * (c % y)$j):real^3^3) =
                (c * c) %% ((lambda i j. y$i * y$j):real^3^3)` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(norm(y:real^3) = &0)` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let P3N_LCK_SCALE_GE1 = prove
 (`!k s (G0:real^N->real^N^N) G c y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ &1 <= c
     ==> lck_dist2 k (\z. c %% G0 z) (\z. c %% G z) y <= lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `c:real`; `y:real^N`] P2B9S_LCK_SCALE_BOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_1_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P3N_DIL_DIFFEO = prove
 (`!c r1 r2. &0 < c
     ==> diffeomorphism_on (annulus r1 r2) (annulus (c * r1) (c * r2))
           (\x:real^3. c % x) (\x. inv c % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. inv c % c % x = x /\ c % inv c % x = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus r1 r2 <=> c % x IN annulus (c * r1) (c * r2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\x:real^3. c % x) = (\x. drop(lift c) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\x:real^3. inv c % x) = (\x. drop(lift(inv c)) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let p3n_psi = new_definition
 `p3n_psi g0 A0 (c:real) (a:real) (y:real^3) = p3s_ncinv g0 A0 (c % p3n_pw a y)`;;

let P3N_PSI_DIFFEO = prove
 (`!g0 A0 c a u.
     p3_std_initial g0 A0 /\ &0 < c /\ &0 < a /\ &0 < u /\
     sqrt(&2) * log c + sqrt(&2) * a * u <= A0 + &4
     ==> diffeomorphism_on (annulus (exp(--u)) (exp u))
           {x | sqrt(&2) * log c - sqrt(&2) * a * u < A0 + &4 - p3_std_dist g0 x /\
                A0 + &4 - p3_std_dist g0 x < sqrt(&2) * log c + sqrt(&2) * a * u}
           (p3n_psi g0 A0 c a)
           (\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `exp(--u)`; `exp u`] P3N_PW_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LOG_EXP] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `exp(a * --u)`; `exp(a * u)`] P3N_DIL_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`;
                `sqrt(&2) * log c - sqrt(&2) * a * u`;
                `sqrt(&2) * log c + sqrt(&2) * a * u`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sqrt(&2) * a * u` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL]; REAL_ARITH_TAC];
    DISCH_THEN(ASSUME_TAC o MATCH_MP DIFFEOMORPHISM_ON_SYM)] THEN
  SUBGOAL_THEN
   `{y:real^3 | exp((sqrt(&2) * log c - sqrt(&2) * a * u) / sqrt(&2)) < norm y /\
                norm y < exp((sqrt(&2) * log c + sqrt(&2) * a * u) / sqrt(&2))} =
    annulus (c * exp(a * --u)) (c * exp(a * u))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[annulus; EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    SUBGOAL_THEN
     `(sqrt(&2) * log c - sqrt(&2) * a * u) / sqrt(&2) = log c + a * --u /\
      (sqrt(&2) * log c + sqrt(&2) * a * u) / sqrt(&2) = log c + a * u`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_EXP_ADD; EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3n_psi g0 A0 c a =
    (p3s_ncinv g0 A0 o (\x:real^3. c % x)) o p3n_pw a /\
    (\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)) =
    p3n_pw (inv a) o ((\x:real^3. inv c % x) o p3_std_nc g0 A0)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; p3n_psi]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (exp(a * --u)) (exp(a * u)):real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (c * exp(a * --u)) (c * exp(a * u)):real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let P3N_PW_SPHERE = prove
 (`!a y:real^3. norm y = &1 ==> p3n_pw a y = y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p3n_pw; LOG_1; REAL_MUL_RZERO; REAL_EXP_0;
                                       REAL_INV_1; REAL_MUL_LID; VECTOR_MUL_LID]);;

let P3N_PSI_SPHERE = prove
 (`!g0 A0 c a lo hi.
     p3_std_initial g0 A0 /\ &0 < c /\ lo < sqrt(&2) * log c /\ sqrt(&2) * log c < hi /\
     hi <= A0 + &4
     ==> IMAGE (p3n_psi g0 A0 c a) (sphere(vec 0,&1)) =
         {x | p3_std_dist g0 x = A0 + &4 - sqrt(&2) * log c}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `lo:real`; `hi:real`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(sqrt(&2) * log c / sqrt(&2)) = c` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) * log c / sqrt(&2) = log c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(lo / sqrt(&2)) < c /\ c < exp(hi / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < c`))] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < c`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[p3n_psi; P3N_PW_SPHERE] THEN
    SUBGOAL_THEN `c % (y:real^3) IN {y:real^3 | exp(lo / sqrt(&2)) < norm y /\
                                               norm y < exp(hi / sqrt(&2))}` ASSUME_TAC
    THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; NORM_MUL; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`];
      ALL_TAC] THEN
    ABBREV_TAC `z = p3s_ncinv g0 A0 (c % (y:real^3))` THEN
    SUBGOAL_THEN `z IN {x:real^3 | lo < A0 + &4 - p3_std_dist g0 x /\
                                  A0 + &4 - p3_std_dist g0 x < hi} /\
                  p3_std_nc g0 A0 z = c % y` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `vec 0 IN {x:real^3 | lo < A0 + &4 - p3_std_dist g0 x /\
                                       A0 + &4 - p3_std_dist g0 x < hi}` THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_NC_NORM) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    REWRITE_TAC[LOG_EXP] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN {x:real^3 | lo < A0 + &4 - p3_std_dist g0 x /\
                                           A0 + &4 - p3_std_dist g0 x < hi}` ASSUME_TAC
    THENL [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `p3_std_dist g0 (vec 0:real^3) = A0 + &4 - sqrt(&2) * log c` THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `inv c % p3_std_nc g0 A0 x` THEN
    SUBGOAL_THEN `norm(inv c % p3_std_nc g0 A0 x) = &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_NC_NORM) THEN
      ASM_REWRITE_TAC[REAL_ARITH `A0 + &4 - (A0 + &4 - t) = t`] THEN
      SUBGOAL_THEN `(sqrt(&2) * log c) / sqrt(&2) = log c` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[EXP_LOG] THEN DISCH_TAC THEN ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p3n_psi] THEN ASM_SIMP_TAC[P3N_PW_SPHERE] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Pullbacks through psi: psi pulls nc^* (cylinder_flow s)                  *)
(* back to (1 - s) cylinder_flow 0 when a^2 = 1 - s (P3N_PSI_CYL), and      *)
(* pullbacks of a manifold metric by Phi o psi (P3N_RFS_PULLBACK_O).        *)
(* ========================================================================= *)

let P3N_MPULLBACK_LOCAL = prove
 (`!(f:real^N->real^N) g G s y.
     open s /\ y IN s /\ (!w. w IN s ==> f w = g w) /\ g differentiable at y
     ==> mpullback f G y = mpullback g G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (f:real^N->real^N) (at y) = frechet_derivative g (at y)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `g:real^N->real^N` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(y:real^N,d) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
    ASM_SIMP_TAC[]]);;

let P3N_MPULLBACK_POINT = prove
 (`!(h:real^N->real^N) G1 G2 y.
     G1 (h y) = G2 (h y) ==> mpullback h G1 y = mpullback h G2 y`,
  SIMP_TAC[mpullback]);;

let P3N_PSI_CYL = prove
 (`!g0 A0 c a u s y.
     p3_std_initial g0 A0 /\ &0 < c /\ &0 < a /\ &0 < u /\
     sqrt(&2) * log c + sqrt(&2) * a * u <= A0 + &4 /\ a pow 2 = &1 - s /\
     y IN annulus (exp(--u)) (exp u)
     ==> mpullback (p3n_psi g0 A0 c a) (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) y =
         (&1 - s) %% cylinder_flow (&0) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  ABBREV_TAC `V = {x:real^3 | sqrt(&2) * log c - sqrt(&2) * a * u <
                              A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x <
                              sqrt(&2) * log c + sqrt(&2) * a * u}` THEN
  SUBGOAL_THEN `~((vec 0:real^3) IN (V:real^3->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `a:real`; `u:real`]
         P3N_PSI_DIFFEO) THEN ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:real^3. w IN annulus (exp(--u)) (exp u)
               ==> p3_std_nc g0 A0 (p3n_psi g0 A0 c a w) = c % p3n_pw a w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3n_psi g0 A0 c a w IN (V:real^3->bool)` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `IMAGE (p3n_psi g0 A0 c a)`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(p3n_psi g0 A0 c a w = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((vec 0:real^3) IN (V:real^3->bool))` THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3n_psi g0 A0 c a w`] P3S_NC_NORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(inv c % p3_std_nc g0 A0 (p3n_psi g0 A0 c a w) = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT; NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT; REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p3n_pw (inv a) (inv c % p3_std_nc g0 A0 (p3n_psi g0 A0 c a w)) = w`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o BETA_RULE o SPEC `w:real^3` o check (fun th ->
        try let b = snd(dest_forall(concl th)) in
            fst(dest_imp b) = `x:real^3 IN annulus (exp(--u)) (exp u)` &&
            can (find_term ((=) `p3n_pw (inv a)`)) b
        with Failure _ -> false)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`inv a`; `inv c % p3_std_nc g0 A0 (p3n_psi g0 A0 c a w)`] P3N_PW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(p3n_psi g0 A0 c a y = vec 0) /\
                ~(p3n_pw a y = vec 0)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(vec 0:real^3) IN annulus (exp(--u)) (exp u)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN
      MP_TAC(SPEC `--u` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3N_PW_NORM] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((vec 0:real^3) IN (V:real^3->bool))` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `IMAGE (p3n_psi g0 A0 c a)`)) (lhs(concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p3n_psi g0 A0 c a) differentiable at (y:real^3) /\
                (p3_std_nc g0 A0) differentiable at (p3n_psi g0 A0 c a y) /\
                (p3n_pw a) differentiable at (y:real^3) /\
                (\x:real^3. c % x) differentiable at (p3n_pw a y)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `annulus (exp(--u)) (exp u):real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[P3S_NC_SMOOTH; OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[P3N_PW_SMOOTH; OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
      MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2A_MPULLBACK_COMPOSE] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((\x:real^3. c % x) o p3n_pw a) (cylinder_flow s) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3N_MPULLBACK_LOCAL THEN
    EXISTS_TAC `annulus (exp(--u)) (exp u):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM P2A_MPULLBACK_COMPOSE] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3n_pw a) (cylinder_flow s) y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3N_MPULLBACK_POINT THEN MATCH_MP_TAC P3N_CYL_DILATION THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3N_PW_CYL THEN ASM_REWRITE_TAC[]]);;

let P3N_RFS_PULLBACK_O = prove
 (`!top atlas (g:A->real^3^3) s (Phi:real^3->A) t (psi:real^3->real^3) psi' y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s Phi /\
     diffeomorphism_on t (IMAGE psi t) psi psi' /\ IMAGE psi t SUBSET s /\ y IN t
     ==> rfs_pullback atlas (Phi o psi) g y = mpullback psi (rfs_pullback atlas Phi g) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^3->real^3) y IN s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `s:real^3->bool`; `Phi:real^3->A`;
                 `(psi:real^3->real^3) y`] APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                      ((Phi:real^3->A) ((psi:real^3->real^3) y))) o Phi) differentiable
                at ((psi:real^3->real^3) y) /\
                (psi:real^3->real^3) differentiable at y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `N:real^3->bool` THEN ASM_MESON_TAC[diffeomorphism_on];
      EXISTS_TAC `t:real^3->bool` THEN ASM_MESON_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_pullback; o_THM] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (psi:real^3->real^3)
                (mpullback (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                  ((Phi:real^3->A) (psi y))) o Phi)
                   (metric_local atlas (chart_at atlas (Phi (psi y))) (g:A->real^3^3))) y` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[P2A_MPULLBACK_COMPOSE; o_ASSOC];
    MATCH_MP_TAC P3N_MPULLBACK_POINT THEN REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The scalar curvature of the round cylinder is 1 away from               *)
(* the axis (P3N_CYL0_SCALAR), and a triangle inequality for the C^k        *)
(* distance with base change (P3N_CLOSE_COMBINE): if C is close to G0 and   *)
(* G0 is close to H in the norms of G0, then C is close to H in the norms   *)
(* of C, with a constant M depending only on k.                             *)
(* ========================================================================= *)

let P3N_CYL0_SCALAR = prove
 (`!y:real^3. ~(y = vec 0) ==> lscalar (cylinder_flow (&0)) y = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&0`; `y:real^3`] CYLINDER_FLOW_SCALAR) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO; REAL_DIV_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV]);;

let P3N_CLOSE_COMBINE = prove
 (`!k. ?M. &0 <= M /\
      !V (C:real^3->real^3^3) G0 H w dd.
        metric_field V C /\ metric_field V G0 /\ metric_field V H /\ w IN V /\
        lck_dist2 k C G0 w < dd pow 2 /\ lck_dist2 k G0 H w < dd pow 2 /\
        &0 < dd /\ dd pow 2 <= &1 / &4
        ==> sqrt(lck_dist2 k C H w) <= dd * (&1 + sqrt M)`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` LRG_CK_BASE_CHANGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `V:real^3->bool`; `C:real^3->real^3^3`; `G0:real^3->real^3^3`;
                 `H:real^3->real^3^3`; `w:real^3`] LCK_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^3->bool`; `C:real^3->real^3^3`;
    `G0:real^3->real^3^3`; `H:real^3->real^3^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 k C (G0:real^3->real^3^3) w) +
              sqrt(lck_dist2 k C (\z. C z + H z - (G0:real^3->real^3^3) z) w)` THEN
  ASM_REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(dd pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(M * lck_dist2 k (G0:real^3->real^3^3) H w)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(M * dd pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The inner parametrisation (P3N_INNER_PARAM).  For a slice                *)
(* parametrisation Phi of the ball of radius m about the tip of the        *)
(* standard initial metric, Phi o psi parametrises the neck domain of       *)
(* scale eps onto the shell d0 - 1/eps < d < d0 + 1/eps, where psi is the   *)
(* nc inverse of a dilated power map, and it carries the unit sphere onto   *)
(* the level set d = d0.                                                     *)
(* ========================================================================= *)

let P3N_INNER_PARAM = prove
 (`!g0 A0 top atlas (Phi:real^3->A) m s eps d0.
     p3_std_initial g0 A0 /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\
     &0 <= s /\ s < &1 /\ &0 < eps /\ inv eps < d0 /\ d0 + inv eps < m
     ==> let a = sqrt(&1 - s) in
         let c = exp((A0 + &4 - d0) / sqrt(&2)) in
         let V = {x | sqrt(&2) * log c - sqrt(&2) * a * inv(sqrt(&2) * eps) <
                      A0 + &4 - p3_std_dist g0 x /\
                      A0 + &4 - p3_std_dist g0 x <
                      sqrt(&2) * log c + sqrt(&2) * a * inv(sqrt(&2) * eps)} in
         &0 < a /\ a pow 2 = &1 - s /\ &0 < c /\
         diffeomorphism_on (rfs_neck_dom eps) V (p3n_psi g0 A0 c a)
           (\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)) /\
         V SUBSET {x | d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps} /\
         V SUBSET {x | p3_std_dist g0 x < m} /\
         mfd_param top atlas (rfs_neck_dom eps) (Phi o p3n_psi g0 A0 c a) /\
         IMAGE (Phi o p3n_psi g0 A0 c a) (sphere(vec 0,&1)) =
         IMAGE Phi {x | p3_std_dist g0 x = d0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = sqrt(&1 - s)` THEN
  ABBREV_TAC `c = exp((A0 + &4 - d0) / sqrt(&2))` THEN
  ABBREV_TAC `u = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < a /\ a <= &1 /\ a pow 2 = &1 - s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[SQRT_1; REAL_LE_REFL]];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c /\ sqrt(&2) * log c = A0 + &4 - d0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN
    UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u /\ sqrt(&2) * a * u = a / eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL];
      MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&2)`; `&0 < eps`] THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `a / eps <= inv eps` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (exp(--u)) (exp u)` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_neck_dom] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `a:real`; `u:real`]
         P3N_PSI_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a / eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = {x:real^3 | (A0 + &4 - d0) - a / eps < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < (A0 + &4 - d0) + a / eps}` THEN
  SUBGOAL_THEN `V SUBSET {x:real^3 | d0 - inv eps < p3_std_dist g0 x /\
                                     p3_std_dist g0 x < d0 + inv eps} /\
                V SUBSET {x:real^3 | p3_std_dist g0 x < m}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_param top atlas {x:real^3 | p3_std_dist g0 x < m} (Phi:real^3->A)` THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN
    EXISTS_TAC `(\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)) o (Phi':A->real^3)` THEN
    SUBGOAL_THEN `IMAGE ((Phi:real^3->A) o p3n_psi g0 A0 c a) (annulus (exp(--u)) (exp u)) =
                  IMAGE Phi V` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN ASM_MESON_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
      `annulus (exp(--u)) (exp u):real^3->bool`; `euclidean:(real^3)topology`;
      `open_set_atlas (:real^3)`; `V:real^3->bool`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `IMAGE (Phi:real^3->A) V`;
      `p3n_psi g0 A0 c a`; `\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)`;
      `Phi:real^3->A`; `Phi':A->real^3`] MFD_DIFFEO_COMPOSE) THEN
    ASM_REWRITE_TAC[P3N_EUCL_ATLAS; MFD_DIFFEO_EUCLIDEAN] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`{x:real^3 | p3_std_dist g0 x < m}`;
                          `IMAGE (Phi:real^3->A) {x:real^3 | p3_std_dist g0 x < m}`] THEN
    ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `a:real`;
                `(A0 + &4 - d0) - a / eps`; `(A0 + &4 - d0) + a / eps`] P3N_PSI_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `A0 + &4 - (A0 + &4 - d0) = d0`]);;

(* ========================================================================= *)
(* The inner neck (P3N_INNER_NECK, used for Claim 16.10).  If               *)
(* the rescaled slice metric is dd-close to a field G0 on the ball of        *)
(* radius m, and G0 is dd-close to the standard solution at time s in nc    *)
(* coordinates on the shell about d0, then the level set d = d0 is the      *)
(* central sphere of an eps-neck of the slice.  The parameter dd0 depends   *)
(* only on eps.                                                              *)
(* ========================================================================= *)

let P3N_INNER_NECK = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd.
             p3_std_initial g0 A0 /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\
             mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
             metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!y. p3_std_dist g0 y < m
                  ==> lck_dist2 (rfs_kreg eps) G0
                        (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2)
             ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                       IMAGE e (sphere(vec 0,&1)) = IMAGE Phi {x | p3_std_dist g0 x = d0}`,
  GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (ISPECL [`K0:real`; `eps / &8`] LCK_CURVATURE_STABILITY)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "STAB"))) THEN
  MP_TAC(SPEC `rfs_kreg eps` P3N_CLOSE_COMBINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "COMB"))) THEN
  ABBREV_TAC `bt = min eta (eps / &8) / &2` THEN
  SUBGOAL_THEN `&0 < bt /\ bt < eta /\ bt <= eps / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bt" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + sqrt M` ASSUME_TAC THENL
   [MP_TAC(SPEC `M:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (bt / (&1 + sqrt M))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `dd pow 2 <= &1 / &4 /\ dd * (&1 + sqrt M) <= bt` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dd <= min (&1 / &2) (bt / (&1 + sqrt M))` THEN
    REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `Phi:real^3->A`; `m:real`;
                 `s:real`; `eps:real`; `d0:real`] P3N_INNER_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `a = sqrt(&1 - s)` THEN
  ABBREV_TAC `c = exp((A0 + &4 - d0) / sqrt(&2))` THEN
  ABBREV_TAC `V = {x:real^3 | sqrt(&2) * log c - sqrt(&2) * a * inv(sqrt(&2) * eps) <
                      A0 + &4 - p3_std_dist g0 x /\
                      A0 + &4 - p3_std_dist g0 x <
                      sqrt(&2) * log c + sqrt(&2) * a * inv(sqrt(&2) * eps)}` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log c = A0 + &4 - d0 /\
                sqrt(&2) * a * inv(sqrt(&2) * eps) = a / eps /\
                &0 < a / eps /\ a / eps <= inv eps /\ a <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `a <= &1` ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
                      REWRITE_TAC[SQRT_1; REAL_LE_REFL]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[LOG_EXP] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&2)`; `&0 < eps`] THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= rfs_kreg eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  ABBREV_TAC `H = \z:real^3. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) g z` THEN
  ABBREV_TAC `C = mpullback (p3_std_nc g0 A0) (cylinder_flow s)` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field V (H:real^3->real^3^3) /\ metric_field V (G0:real^3->real^3^3) /\
                metric_field V (C:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < m}` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "H" THEN MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; REAL_LT_INV_EQ; REAL_POW_LT; ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXPAND_TAC "C" THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC
       [`{y:real^3 | exp((sqrt(&2) * log c - sqrt(&2) * a * inv(sqrt(&2) * eps)) / sqrt(&2))
                     < norm y /\
                     norm y <
                     exp((sqrt(&2) * log c + sqrt(&2) * a * inv(sqrt(&2) * eps)) / sqrt(&2))}`;
        `p3s_ncinv g0 A0`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM annulus; OPEN_ANNULUS];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM NORM_POS_LT] THEN
          MESON_TAC[REAL_EXP_POS_LT; REAL_LT_TRANS]];
        EXPAND_TAC "V" THEN MATCH_MP_TAC P3S_NC_DIFFEO THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN V ==> lck_dist2 k C H w <= bt pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= lck_dist2 k (C:real^3->real^3^3) H w` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (C:real^3->real^3^3) H w) <= bt` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd * (&1 + sqrt M)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "COMB" MATCH_MP_TAC THEN
      EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `G0:real^3->real^3^3` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `lck_dist2 k (C:real^3->real^3^3) H w = sqrt(lck_dist2 k C H w) pow 2`
    SUBST1_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e = (Phi:real^3->A) o p3n_psi g0 A0 c a` THEN
  ABBREV_TAC `X = \z:real^3. (inv(&1 - s) * inv(h pow 2)) %% rfs_pullback atlas (e:real^3->A) g z` THEN
  SUBGOAL_THEN `open(rfs_neck_dom eps) /\
                rfs_neck_dom eps = annulus (exp(--(inv(sqrt(&2) * eps))))
                                           (exp(inv(sqrt(&2) * eps)))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (rfs_pullback atlas (e:real^3->A) g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (X:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (cylinder_flow (&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < inv(&1 - s) * inv(h pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "X" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) X y <= bt pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3n_psi g0 A0 c a y IN (V:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on; FUN_IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `V:real^3->bool`; `rfs_neck_dom eps`; `p3n_psi g0 A0 c a`;
                   `\x. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)`;
                   `C:real^3->real^3^3`; `H:real^3->real^3^3`; `y:real^3`]
                  LCK_DIST2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (p3n_psi g0 A0 c a) (rfs_neck_dom eps) = (V:real^3->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    SUBGOAL_THEN
       `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
          (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y =
        lck_dist2 k (mpullback (p3n_psi g0 A0 c a) C) (mpullback (p3n_psi g0 A0 c a) H) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN EXPAND_TAC "C" THEN MATCH_MP_TAC P3N_PSI_CYL THEN
        EXISTS_TAC `inv(sqrt(&2) * eps)` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
        EXPAND_TAC "H" THEN REWRITE_TAC[P3S_MPULLBACK_CMUL; ETA_AX] THEN AP_TERM_TAC THEN
        EXPAND_TAC "e" THEN MATCH_MP_TAC P3N_RFS_PULLBACK_O THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `{x:real^3 | p3_std_dist g0 x < m}`;
          `rfs_neck_dom eps`; `\x:real^3. p3n_pw (inv a) (inv c % p3_std_nc g0 A0 x)`] THEN
        REWRITE_TAC[ASSUME `IMAGE (p3n_psi g0 A0 c a) (rfs_neck_dom eps) = (V:real^3->bool)`] THEN
        SUBGOAL_THEN `z IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
                   (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y <= bt pow 2`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!w:real^3. w IN (V:real^3->bool)
                             ==> lck_dist2 k (C:real^3->real^3^3) (H:real^3->real^3^3) w
                                 <= bt pow 2`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps`;
                   `\z:real^3. (&1 - s) %% cylinder_flow (&0) z`;
                   `\z:real^3. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z`;
                   `inv(&1 - s)`; `y:real^3`] P3N_LCK_SCALE_GE1) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]];
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z:real^3. inv(&1 - s) %% (&1 - s) %% cylinder_flow (&0) z) = cylinder_flow (&0) /\
                  (\z:real^3. inv(&1 - s) %% inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) = X`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN X_GEN_TAC `w:real^3` THEN
        SUBGOAL_THEN `inv(&1 - s) * (&1 - s) = &1` SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[MATRIX_CMUL_LID]];
        EXPAND_TAC "X" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC]];
      ALL_TAC] THEN
    UNDISCH_TAC `lck_dist2 k (\z:real^3. (&1 - s) %% cylinder_flow (&0) z)
                   (\z. inv(h pow 2) %% rfs_pullback atlas (e:real^3->A) g z) y <= bt pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN rfs_neck_dom eps /\ ~(basis 1:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; NORM_BASIS; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = lscalar (X:real^3->real^3^3) (basis 1)` THEN
  SUBGOAL_THEN `abs(lam - &1) <= eps / &8` ASSUME_TAC THENL
   [SUBGOAL_THEN `lscalar (cylinder_flow (&0)) (basis 1:real^3) = &1` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC P3N_CYL0_SCALAR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXPAND_TAC "lam" THEN
    USE_THEN "STAB" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                     `X:real^3->real^3^3`; `basis 1:real^3`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(ASSUME `!y:real^3. ~(y = vec 0)
                               ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) (basis 1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
          REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `bt pow 2` THEN CONJ_TAC THENL
           [MATCH_MP_TAC(ASSUME `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y <= bt pow 2`) THEN
            FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
            UNDISCH_TAC `&0 < bt` THEN UNDISCH_TAC `bt < eta` THEN REAL_ARITH_TAC]]];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1 + eps / &8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs(lam - &1) <= eps / &8` THEN UNDISCH_TAC `eps <= &1 / &4` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 * (&1 - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    UNDISCH_TAC `s < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) = lam / (h pow 2 * (&1 - s)) /\
    (\y. mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) %% rfs_pullback atlas e g y) =
    (\y. lam %% (X:real^3->real^3^3) y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_pullback atlas (e:real^3->A) g =
                  (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN
      X_GEN_TAC `w:real^3` THEN
      SUBGOAL_THEN `(h pow 2 * (&1 - s)) * inv(&1 - s) * inv(h pow 2) = &1` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(h pow 2 = &0) /\ ~(&1 - s = &0)` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_NZ THEN UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
            UNDISCH_TAC `s < &1` THEN REAL_ARITH_TAC];
          CONV_TAC REAL_FIELD];
        REWRITE_TAC[MATRIX_CMUL_LID]];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) = lam / (h pow 2 * (&1 - s))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `basis 1:real^3`]
                    APX_PULLBACK_SCALAR_GEN) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[ASSUME `rfs_pullback atlas (e:real^3->A) g =
                          (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)`] THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `X:real^3->real^3^3`; `h pow 2 * (&1 - s)`;
                     `basis 1:real^3`] LSCALAR_SCALE) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "lam" THEN REFL_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `rfs_pullback atlas (e:real^3->A) g =
                        (\z. (h pow 2 * (&1 - s)) %% (X:real^3->real^3^3) z)`] THEN
    REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN X_GEN_TAC `w:real^3` THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < h pow 2 * (&1 - s)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y
                      <= eps pow 2 / &4`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps`; `cylinder_flow (&0)`; `X:real^3->real^3^3`;
                   `lam:real`; `y:real^3`] LCK_DIST_RESCALE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) <= bt`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < bt` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(ASSUME `!y:real^3. y IN rfs_neck_dom eps
                  ==> lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y <= bt pow 2`) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y)
                  <= eps / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) +
                  abs(lam - &1) * sqrt(&3)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * (eps / &8) + (eps / &8) * &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `lam <= &1 + eps / &8` THEN UNDISCH_TAC `eps <= &1 / &4` THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
          EXISTS_TAC `rfs_neck_dom eps` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (X:real^3->real^3^3) y) <= bt` THEN
          UNDISCH_TAC `bt <= eps / &8` THEN REAL_ARITH_TAC;
          REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC];
        UNDISCH_TAC `&0 < eps` THEN UNDISCH_TAC `eps <= &1 / &4` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. lam %% (X:real^3->real^3^3) z) y)
                pow 2` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps / &2) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(e:real^3->A) (basis 1)` THEN EXISTS_TAC `e:real^3->A` THEN
  REWRITE_TAC[rfs_neck] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    REWRITE_TAC[ASSUME `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) =
                        lam / (h pow 2 * (&1 - s))`] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `(\y. mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) (basis 1)) %%
                             rfs_pullback atlas e g y) =
                        (\y. lam %% (X:real^3->real^3^3) y)`;
                ASSUME `rfs_kreg eps = k`; rfs_close_on] THEN
    EXISTS_TAC `eps pow 2 / &4` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* Helpers for the slice form of Claim 16.10.  Level sets of                *)
(* the distance from the tip are Euclidean spheres (P3N_STD_SPHERE); the     *)
(* core of a parametrised ball of any radius (P3N_BALL_CORE_GEN, the radius *)
(* form of APX_BALL_CORE_TOP); short curves through a parametrised ball      *)
(* (P3N_PARAM_SEGMENT); scalar curvature and metric bounds transferred from *)
(* a close model field (P3N_DISC_CURV).                                     *)
(* ========================================================================= *)

let P3N_STD_SPHERE = prove
 (`!g0 A0 d0. p3_std_initial g0 A0 /\ &0 < d0
              ==> {x:real^3 | p3_std_dist g0 x = d0} = sphere(vec 0,p3s_rad_rinv g0 d0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d0:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`;
                `p3s_rad_rinv g0 d0`] P3S_RHO_LT_EQ) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 d0`;
                `norm(x:real^3)`] P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

let P3N_STD_RINV_LT = prove
 (`!g0 A0 a b. p3_std_initial g0 A0 /\ &0 < a /\ a < b
               ==> p3s_rad_rinv g0 a < p3s_rad_rinv g0 b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `a:real`] P3S_RINV_FACTS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `b:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < b` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 a`;
                `p3s_rad_rinv g0 b`] P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P3N_BALL_CORE_GEN = prove
 (`!top atlas (b:real^3->A) r R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        &0 < r /\ r < R /\ mfd_param top atlas (ball(vec 0,R)) b
        ==> compact_in top (top closure_of (IMAGE b (ball(vec 0,r)))) /\
            top closure_of (IMAGE b (ball(vec 0,r))) SUBSET IMAGE b (ball(vec 0,R)) /\
            open_in top (IMAGE b (ball(vec 0,r))) /\
            ~(IMAGE b (ball(vec 0,r)) = {}) /\
            top frontier_of (top closure_of (IMAGE b (ball(vec 0,r))))
            SUBSET IMAGE b (sphere(vec 0,r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,R)`; `b:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bi:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r) SUBSET ball(vec 0,R) /\
                ball(vec 0:real^3,r) SUBSET ball(vec 0,R)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN CONJ_TAC THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (b:real^3->A) (cball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,R))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (b:real^3->A) (ball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,R)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (b:real^3->A) (ball(vec 0,r))) SUBSET
                IMAGE b (cball(vec 0,r))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,r))` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,r))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC APX_CORE_FRONTIER THEN
    EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,r))` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,R)`; `cball(vec 0:real^3,r)`;
                   `ball(vec 0:real^3,r)`; `b:real^3->A`] APX_PARAM_IMAGE_DIFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CBALL_DIFF_BALL; SUBSET_REFL]]);;

let P3N_PARAM_SEGMENT = prove
 (`!top atlas (g:A->real^3^3) (e:real^3->A) R C w1 w2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas (ball(vec 0,R)) e /\ &0 <= C /\
     (!y v. y IN ball(vec 0,R)
            ==> v dot (rfs_pullback atlas e g y ** v) <= C * (v dot v)) /\
     w1 IN ball(vec 0,R) /\ w2 IN ball(vec 0,R)
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma (&0) = e w1 /\ gamma (&1) = e w2 /\
                 (!t. &0 <= t /\ t <= &1 ==> gamma t IN IMAGE e (ball(vec 0,R))) /\
                 mfd_length atlas g gamma (&0) (&1) <= sqrt C * dist(w1,w2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^3,R)))
                                      (open_set_atlas (ball(vec 0,R)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[w1:real^3,w2] SUBSET ball(vec 0,R)` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,R)) (rfs_pullback atlas (e:real^3->A) g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,R))`;
                 `open_set_atlas (ball(vec 0:real^3,R))`;
                 `ball(vec 0:real^3,R)`; `\x:real^3. x`; `w1:real^3`; `w2:real^3`]
                GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
  ABBREV_TAC `c = \t. chart_inv (ball(vec 0:real^3,R),(\x:real^3. x)) (w1 + t % (w2 - w1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seg") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (c:real->real^3) t IN ball(vec 0,R)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
    USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^3) (&0) = w1 /\ c (&1) = w2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[] THENL
     [USE_THEN "seg" (MP_TAC o SPEC `&0`); USE_THEN "seg" (MP_TAC o SPEC `&1`)] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    SIMP_TAC[VECTOR_ARITH `w1 + w2 - w1:real^N = w2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,R))`;
                 `open_set_atlas (ball(vec 0:real^3,R))`;
                 `rfs_pullback atlas (e:real^3->A) g`;
                 `ball(vec 0:real^3,R)`; `\x:real^3. x`; `w1:real^3`; `w2:real^3`;
                 `&0`; `C:real`; `ball(vec 0:real^3,R)`] GRGD_SEGMENT_LENGTH_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID; SUBSET_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^3,R)`; `rfs_pullback atlas (e:real^3->A) g`;
                   `z:real^3`] RFB_OPEN_SET_METRIC_LOCAL) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; NORM_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_METRIC_QPOS THEN EXISTS_TAC `ball(vec 0:real^3,R)` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `C:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `ball(vec 0:real^3,R)`; `e:real^3->A`;
                 `rfs_pullback atlas (e:real^3->A) g`;
                 `c:real->real^3`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_pullback];
    STRIP_TAC] THEN
  EXISTS_TAC `(e:real^3->A) o (c:real->real^3)` THEN
  ASM_REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;

let P3N_DISC_CURV = prove
 (`!K. &0 <= K
       ==> ?eta. &0 < eta /\ eta <= &1 / &2 /\
           !top atlas (g:A->real^3^3) U (Phi:real^3->A) h G0 k w.
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              mfd_param top atlas U Phi /\ &0 < h /\ metric_field U G0 /\ w IN U /\
              2 <= k /\
              lck_dist2 k G0 (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) w < eta pow 2 /\
              lrm_deriv_norm2 0 G0 w <= K pow 2 /\ lscalar G0 w <= K
              ==> mfd_scalar atlas g (Phi w) <= (K + &1) / h pow 2 /\
                  (!v. v dot (rfs_pullback atlas Phi g w ** v) <=
                       &2 * h pow 2 * (v dot (G0 w ** v)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (ISPECL [`K:real`; `&1`] LCK_CURVATURE_STABILITY)) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "STAB"))) THEN
  EXISTS_TAC `min eta0 (&1 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `H = \z:real^3. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) z` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (rfs_pullback atlas (Phi:real^3->A) g)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < inv(h pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (H:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas (Phi:real^3->A) g = (\z. h pow 2 %% (H:real^3->real^3^3) z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN GEN_TAC THEN
    SUBGOAL_THEN `h pow 2 * inv(h pow 2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      REWRITE_TAC[MATRIX_CMUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k G0 (H:real^3->real^3^3) w <= (&1 / &2) pow 2 /\
                lck_dist2 2 G0 (H:real^3->real^3^3) w < eta0 pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `min eta0 (&1 / &2) pow 2 <= (&1 / &2) pow 2 /\
                  min eta0 (&1 / &2) pow 2 <= eta0 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lck_dist2 2 G0 (H:real^3->real^3^3) w <= lck_dist2 k G0 H w` MP_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `lck_dist2 k G0 (H:real^3->real^3^3) w < min eta0 (&1 / &2) pow 2` THEN
    UNDISCH_TAC `min eta0 (&1 / &2) pow 2 <= (&1 / &2) pow 2` THEN
    UNDISCH_TAC `min eta0 (&1 / &2) pow 2 <= eta0 pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "STAB" (MP_TAC o SPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
                                     `H:real^3->real^3^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `U:real^3->bool`; `Phi:real^3->A`; `w:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ASSUME `rfs_pullback atlas (Phi:real^3->A) g =
                        (\z. h pow 2 %% (H:real^3->real^3^3) z)`] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `H:real^3->real^3^3`; `h pow 2`; `w:real^3`]
                  LSCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `lscalar G0 (w:real^3) <= K` THEN
      UNDISCH_TAC `abs(lscalar (H:real^3->real^3^3) w - lscalar G0 w) <= &1` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `v:real^3` THEN
    REWRITE_TAC[ASSUME `rfs_pullback atlas (Phi:real^3->A) g =
                        (\z. h pow 2 %% (H:real^3->real^3^3) z)`] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    MP_TAC(ISPECL [`k:num`; `U:real^3->bool`; `G0:real^3->real^3^3`; `H:real^3->real^3^3`;
                   `w:real^3`; `v:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k G0 (H:real^3->real^3^3) w) <= &1 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= v dot ((G0:real^3->real^3^3) w ** v)` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_METRIC_QPOS THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k G0 (H:real^3->real^3^3) w) * (v dot ((G0:real^3->real^3^3) w ** v))
                  <= &1 / &2 * (v dot (G0 w ** v))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `v dot ((H:real^3->real^3^3) w ** v) <= &2 * (v dot ((G0:real^3->real^3^3) w ** v))`
    MP_TAC THENL
     [UNDISCH_TAC `abs(v dot ((H:real^3->real^3^3) w ** v) - v dot ((G0:real^3->real^3^3) w ** v))
                   <= sqrt(lck_dist2 k G0 H w) * (v dot (G0 w ** v))` THEN
      UNDISCH_TAC `sqrt(lck_dist2 k G0 (H:real^3->real^3^3) w) * (v dot ((G0:real^3->real^3^3) w ** v))
                  <= &1 / &2 * (v dot (G0 w ** v))` THEN
      UNDISCH_TAC `&0 <= v dot ((G0:real^3->real^3^3) w ** v)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `h pow 2 * (v dot ((H:real^3->real^3^3) w ** v)) <=
                  h pow 2 * (&2 * (v dot ((G0:real^3->real^3^3) w ** v)))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A set reachable from a point of the central sphere of a                  *)
(* dl-neck by curves much shorter than the neck lies inside the neck        *)
(* (P3N_SET_IN_NECK), with the two numerical facts behind it and behind the *)
(* recentring bound (P3N_EXIT_ARITH, P3N_SVAL_ARITH).                       *)
(* ========================================================================= *)

let P3N_SQRT_MUL_H = prove
 (`!Rc h Q. &0 < Rc /\ &0 < h /\ &0 < Q /\ Rc * h pow 2 <= Q pow 2
            ==> &0 < sqrt Rc /\ sqrt Rc * h <= Q`,
  REPEAT STRIP_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt Rc * h = sqrt(Rc * h pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2; POW_2_SQRT];
    MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P3N_EXIT_ARITH = prove
 (`!Rc h Q ell dl c0.
     &0 < Rc /\ &0 < h /\ &0 < Q /\ &0 <= ell /\ &0 < dl /\ dl <= &1 / &2 /\ &1 <= c0 /\
     Rc * h pow 2 <= Q pow 2 /\ c0 * dl * (&2 * Q * ell + &1) <= &1
     ==> h * ell < sqrt(&1 - dl) * inv(sqrt Rc) * inv dl`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`Rc:real`; `h:real`; `Q:real`] P3N_SQRT_MUL_H) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `dl <= &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dl * (&2 * Q * ell + &1) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * dl * (&2 * Q * ell + &1)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt Rc * h) * (ell * dl) <= Q * (ell * dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * ell * (sqrt Rc * dl) < sqrt(&1 - dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Q * (ell * dl)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(sqrt Rc * h) * (ell * dl) <= Q * (ell * dl)` THEN
      REWRITE_TAC[REAL_MUL_AC];
      UNDISCH_TAC `dl * (&2 * Q * ell + &1) <= &1` THEN
      UNDISCH_TAC `&1 / &2 <= sqrt(&1 - dl)` THEN UNDISCH_TAC `&0 < dl` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - dl) * inv(sqrt Rc) * inv dl = sqrt(&1 - dl) / (sqrt Rc * dl)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL] THEN
  UNDISCH_TAC `h * ell * (sqrt Rc * dl) < sqrt(&1 - dl)` THEN REWRITE_TAC[REAL_MUL_AC]);;

let P3N_SVAL_ARITH = prove
 (`!Rc h Q ell dl c0 a.
     &0 < Rc /\ &0 < h /\ &0 < Q /\ &0 <= ell /\ &0 < dl /\ dl <= &1 / &2 /\ &4 <= c0 /\
     &0 <= a /\ Rc * h pow 2 <= Q pow 2 /\ c0 * dl * (&2 * Q * ell + &1) <= &1 /\
     sqrt(&1 - dl) * inv(sqrt Rc) * a <= h * ell
     ==> a <= &3 / (&4 * dl)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`Rc:real`; `h:real`; `Q:real`] P3N_SQRT_MUL_H) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `dl <= &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (dl * (&2 * Q * ell + &1)) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * dl * (&2 * Q * ell + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - dl) * a <= (h * ell) * sqrt Rc` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 - dl) * a = (sqrt(&1 - dl) * inv(sqrt Rc) * a) * sqrt Rc`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt Rc` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h * ell) * sqrt Rc <= Q * ell` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h * ell) * sqrt Rc = (sqrt Rc * h) * ell` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 * a <= sqrt(&1 - dl) * a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= &2 * Q * ell` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 / &2 * a <= sqrt(&1 - dl) * a` THEN
    UNDISCH_TAC `sqrt(&1 - dl) * a <= (h * ell) * sqrt Rc` THEN
    UNDISCH_TAC `(h * ell) * sqrt Rc <= Q * ell` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a * dl <= (&2 * Q * ell) * dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * dl` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  UNDISCH_TAC `a * dl <= (&2 * Q * ell) * dl` THEN
  UNDISCH_TAC `&4 * (dl * (&2 * Q * ell + &1)) <= &1` THEN
  UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC);;

let P3N_SET_IN_NECK = prove
 (`!top atlas (g:A->real^3^3) dl x (e:real^3->A) u S h ell Q c0.
     hausdorff_space top /\ riemannian_metric atlas g /\ rfs_neck (top,atlas) g dl x e /\
     norm u = &1 /\ &0 < h /\ &0 < Q /\ &0 <= ell /\ dl <= &1 / &2 /\ &1 <= c0 /\
     c0 * dl * (&2 * Q * ell + &1) <= &1 /\ mfd_scalar atlas g x * h pow 2 <= Q pow 2 /\
     (!q. q IN S ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma (&0) = e u /\
                             gamma (&1) = q /\ mfd_length atlas g gamma (&0) (&1) <= h * ell)
     ==> S SUBSET IMAGE e (rfs_neck_dom dl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < dl /\ &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl x (e:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(q:A) IN IMAGE e (rfs_neck_dom dl)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `dl:real`; `x:A`; `e:real^3->A`; `u:real^3`; `gamma:real->A`;
                 `&0`; `&1`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `dl <= &1 / &2` THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN
      ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_ABS_0; REAL_SUB_RZERO] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) x`; `h:real`; `Q:real`; `ell:real`;
                `dl:real`; `c0:real`] P3N_EXIT_ARITH) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) <= h * ell` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Claim 16.10 on one slice (P3N_SLICE_DISC).  If the                      *)
(* rescaled slice metric on the image B of the ball of radius m is close to *)
(* a model field G0 with bounded curvature and metric, and G0 is close to   *)
(* the standard solution at time s in nc coordinates on the shell about     *)
(* d0, then no central sphere of a dl-neck with dl small meets B: such a    *)
(* neck would contain B (its length beats the diameter of B), after         *)
(* recentring on the inner neck sphere d = d0 that sphere would be a        *)
(* section of the neck (APX_SPHERE_NEAR, APX_NECK_SECTION), and a section   *)
(* bounds no compact region of the neck (APX_SECTION_NOT_BOUNDING), but it  *)
(* bounds the core d <= d0 of B.                                            *)
(* ========================================================================= *)

let P3N_SLICE_DISC = prove
 (`?epsd. &0 < epsd /\
   !eps K. &0 < eps /\ eps <= epsd /\ &0 <= K
     ==> ?dd0. &0 < dd0 /\
         !L. &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !g0 A0 top atlas (g:A->real^3^3) Phi m0 m h G0 s d0 dd dl xc ec.
           p3_std_initial g0 A0 /\ hausdorff_space top /\
           smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
           mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\
           &0 < h /\ metric_field (:real^3) G0 /\
           &0 <= s /\ s < &1 /\ inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\
           &0 < dd /\ dd <= dd0 /\
           (!y. p3_std_dist g0 y < m0
                ==> lck_dist2 (rfs_kreg eps) G0
                      (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
           (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                ==> lck_dist2 (rfs_kreg eps)
                      (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
           (!y. p3_std_dist g0 y < m
                ==> mfd_scalar atlas g (Phi y) * h pow 2 <= K /\ norm y <= L /\
                    !w. w dot (rfs_pullback atlas Phi g y ** w) <= (h pow 2 * L) * (w dot w)) /\
           &0 < dl /\ dl <= dl1 /\ rfs_neck (top,atlas) g dl xc (ec:real^3->A)
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                        (IMAGE ec (sphere(vec 0,&1)))`,
  X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0") APX_CYL0_RM_BOUND THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIST"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CURV"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_SECTION_UNCOND) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1s:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEC"))) THEN
  EXISTS_TAC `min (&1 / &40) (min eps1d (min eps1c eps1s))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `K:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &40 /\ eps <= eps1d /\ eps <= eps1c /\ eps <= eps1s`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `eps:real` P3N_INNER_NECK) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ddI:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INNER"))) THEN
  EXISTS_TAC `ddI:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `L:real` THEN DISCH_TAC THEN
  ABBREV_TAC `c0 = &4 + &576 * (&1 + abs K0)` THEN
  ABBREV_TAC `Q = sqrt(&2 * (K + &1))` THEN
  ABBREV_TAC `ell = sqrt(&2 * L) * (&2 * L)` THEN
  SUBGOAL_THEN `&4 <= c0 /\ &0 < Q /\ Q pow 2 = &2 * (K + &1) /\ &0 <= ell`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "c0" THEN REAL_ARITH_TAC;
      EXPAND_TAC "Q" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Q" THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ell" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * Q * ell + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `min eps (inv(&2 * Q * ell + &1)) / c0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `dl:real`;
    `xc:A`; `ec:real^3->A`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `z:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `u0:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 * dl <= eps /\ c0 * dl <= inv(&2 * Q * ell + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c0 * dl <= min eps (inv(&2 * Q * ell + &1))` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * Q * ell + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * dl * (&2 * Q * ell + &1) <= &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c0 * dl`; `inv(&2 * Q * ell + &1)`; `&2 * Q * ell + &1`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl <= c0 * dl` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c0 * dl /\ dl <= &1 / &2 /\ c0 * dl <= &1 / &2 /\ dl <= eps /\
                dl <= eps1c /\ c0 * dl <= eps1d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d0 /\ &0 < m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < inv eps` THEN UNDISCH_TAC `m0 <= m:real` THEN
    UNDISCH_TAC `inv eps < d0` THEN UNDISCH_TAC `d0 + inv eps < m0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 m` THEN
  ABBREV_TAC `rho0 = p3s_rad_rinv g0 d0` THEN
  SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x < m} = ball(vec 0,R) /\
                {x:real^3 | p3_std_dist g0 x = d0} = sphere(vec 0,rho0) /\
                &0 < rho0 /\ rho0 < R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN EXPAND_TAC "rho0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_STD_BALL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_STD_SPHERE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d0:real`] P3S_RINV_FACTS) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P3N_STD_RINV_LT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,R)) (Phi:real^3->A) /\
                (w0:real^3) IN ball(vec 0,R) /\
                (!y:real^3. y IN ball(vec 0,R) ==> p3_std_dist g0 y < m)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top atlas {x:real^3 | p3_std_dist g0 x < m} (Phi:real^3->A)` THEN
    UNDISCH_TAC `(w0:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,R)) G0` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= rfs_kreg eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN ball(vec 0,R)
      ==> mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) y) * h pow 2 <= K + &1 /\
          (!v. v dot (rfs_pullback atlas Phi g y ** v) <= (&2 * h pow 2 * L) * (v dot v))`
  (LABEL_TAC "BND") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3_std_dist g0 (y:real^3) < m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `mfd_scalar:((A->bool)#(A->real^3)->bool)->(A->real^3^3)->A->real`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) y) * h pow 2 <= K` THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `v:real^3` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(h pow 2 * L) * ((v:real^3) dot v)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= &2 * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w1 w2. w1 IN ball(vec 0:real^3,R) /\ w2 IN ball(vec 0,R)
      ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                  gamma (&0) = (Phi:real^3->A) w1 /\ gamma (&1) = Phi w2 /\
                  (!t. &0 <= t /\ t <= &1 ==> gamma t IN IMAGE Phi (ball(vec 0,R))) /\
                  mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) <= h * ell`
  (LABEL_TAC "CURVES") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Phi:real^3->A`; `R:real`; `&2 * h pow 2 * L`; `w1:real^3`; `w2:real^3`]
                  P3N_PARAM_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REPEAT STRIP_TAC THEN USE_THEN "BND" (MP_TAC o SPEC `y:real^3`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&2 * h pow 2 * L) * dist(w1:real^3,w2)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&2 * h pow 2 * L) = h * sqrt(&2 * L)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&2 * h pow 2 * L = h pow 2 * (&2 * L)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &2 * L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXPAND_TAC "ell" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(w1:real^3) <= L /\ norm(w2:real^3) <= L` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(w1:real^3) <= L /\ norm(w2:real^3) <= L
                              ==> dist(w1,w2) <= &2 * L`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) xc /\
                mfd_param top atlas (rfs_neck_dom dl) (ec:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl xc (ec:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(u0:real^3) = &1 /\ u0 IN rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u0:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `dl:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ec:real^3->A) u0 = (Phi:real^3->A) w0` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) = (Phi:real^3->A) w0` THEN
    UNDISCH_TAC `(z:A) = (ec:real^3->A) u0` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) xc * h pow 2 <= Q pow 2` ASSUME_TAC THENL
   [USE_THEN "CURV" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`]
      APX_NECK_SCALAR_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "BND" (MP_TAC o SPEC `w0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `(mfd_scalar atlas (g:A->real^3^3) xc / &2) * h pow 2 <=
                  mfd_scalar atlas g ((Phi:real^3->A) w0) * h pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) ((Phi:real^3->A) w0) * h pow 2 <= K + &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,R)) SUBSET IMAGE ec (rfs_neck_dom dl)`
  (LABEL_TAC "INA") THENL
   [MATCH_MP_TAC P3N_SET_IN_NECK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `xc:A`; `u0:real^3`; `h:real`; `ell:real`; `Q:real`; `c0:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "CURVES" (MP_TAC o SPECL [`w0:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas {x:real^3 | p3_std_dist g0 x < m0} (Phi:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,R)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < m0` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < inv eps` THEN UNDISCH_TAC `inv eps < d0` THEN
      UNDISCH_TAC `d0 + inv eps < m0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m0}` MP_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3N_STD_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < m}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  USE_THEN "INNER" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m0:real`;
    `h:real`; `G0:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xS:A` (X_CHOOSE_THEN `eS:real^3->A` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `w1 = rho0 % (basis 1:real^3)` THEN
  SUBGOAL_THEN `(w1:real^3) IN ball(vec 0,R) /\ w1 IN sphere(vec 0,rho0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN
    SIMP_TAC[IN_BALL_0; IN_SPHERE_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->A) w1 IN IMAGE (eS:real^3->A) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "CURVES" (MP_TAC o SPECL [`w0:real^3`; `w1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `dl:real`; `xc:A`; `ec:real^3->A`; `u0:real^3`; `gamma1:real->A`; `&1`]
    APX_NECK_LIFT_SVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "INA" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(apx_sval v) <= &3 / (&4 * dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_SVAL_ARITH THEN
    MAP_EVERY EXISTS_TAC [`mfd_scalar atlas (g:A->real^3^3) xc`; `h:real`; `Q:real`; `ell:real`;
                          `c0:real`] THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) gamma1 (&0) (&1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `K0:real` APX_NECK_RECENTRE_GEN) THEN
  ANTS_TAC THENL [USE_THEN "K0" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `xc:A`; `ec:real^3->A`; `v:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `e2 = (ec:real^3->A) o (\w. norm(v:real^3) % w)` THEN
  ABBREV_TAC `u2 = inv(norm(v:real^3)) % v` THEN
  SUBGOAL_THEN `norm(u2:real^3) = &1 /\ (e2:real^3->A) u2 = (ec:real^3->A) v` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
     [MP_TAC(SPEC `dl:real` APX_NECK_DOM_NONZERO) THEN
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "e2" THEN EXPAND_TAC "u2" THEN
    ASM_SIMP_TAC[o_THM; NORM_MUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
                 REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((ec:real^3->A) v) * h pow 2 <= Q pow 2`
  ASSUME_TAC THENL
   [USE_THEN "BND" (MP_TAC o SPEC `w1:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,R)) SUBSET IMAGE e2 (rfs_neck_dom (c0 * dl))`
  (LABEL_TAC "INB") THENL
   [MATCH_MP_TAC P3N_SET_IN_NECK THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `(ec:real^3->A) v`; `u2:real^3`; `h:real`; `ell:real`; `Q:real`;
        `&1`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "CURVES" (MP_TAC o SPECL [`w1:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (eS:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e2 (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SPHERE_NEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `c0 * dl`; `xS:A`; `(ec:real^3->A) v`; `u2:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "DIST" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`; `z':real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 + &1 / &2 = &3 / &2`] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "DIST" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `c0 * dl`; `(ec:real^3->A) v`; `e2:real^3->A`; `y:real^3`;
        `z':real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - &1 / &2 = &1 / &2`] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "CURV" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `xS:A`; `eS:real^3->A`; `y:real^3`]
        APX_NECK_SCALAR_COMPARE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (Phi:real^3->A) (ball(vec 0,R))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_section (e2:real^3->A) (exp(--(inv(sqrt(&2) * (c0 * dl)))))
                  (exp(inv(sqrt(&2) * (c0 * dl)))) (IMAGE (eS:real^3->A) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(&2) * eps) <= inv(sqrt(&2) * (c0 * dl))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LE_LMUL_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC APX_SECTION_MONO THEN
    MAP_EVERY EXISTS_TAC [`exp(--(inv(sqrt(&2) * eps)))`; `exp(inv(sqrt(&2) * eps))`] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SEC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `(ec:real^3->A) v`; `xS:A`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `c0 * dl` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Phi:real^3->A`;
                 `rho0:real`; `R:real`] P3N_BALL_CORE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_SECTION_NOT_BOUNDING) THEN
  REWRITE_TAC[APX_SECTION_NOT_BOUNDING_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `e2:real^3->A`; `exp(--(inv(sqrt(&2) * (c0 * dl))))`; `exp(inv(sqrt(&2) * (c0 * dl)))`;
     `IMAGE (eS:real^3->A) (sphere(vec 0,&1))`;
     `top closure_of (IMAGE (Phi:real^3->A) (ball(vec 0,rho0)))`]) THEN
  SUBGOAL_THEN `annulus (exp(--(inv(sqrt(&2) * (c0 * dl))))) (exp(inv(sqrt(&2) * (c0 * dl)))) =
                rfs_neck_dom (c0 * dl) :real^3->bool` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (c0 * dl) ((ec:real^3->A) v) e2` THEN
      SIMP_TAC[rfs_neck];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (Phi:real^3->A) (ball(vec 0,R))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) (ball(vec 0,rho0)) SUBSET {}` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM_REWRITE_TAC[SUBSET_EMPTY]]);;

(* ========================================================================= *)
(* Claim 16.10 for a history (P3N_DISC).  At an event k the                *)
(* surgery necks are strong dl-necks; just before the event they are        *)
(* (kK dl)-necks of the slices (APX_SLICE_NECKS, APX_STRONG_NECK_EARLIER).  *)
(* If on those slices the image B of the ball of radius m is close to a     *)
(* model as in P3N_SLICE_DISC, B misses every cut sphere, so the event      *)
(* keeps B whole or discards it whole (P3N_EVENT_DICHOTOMY).                *)
(* ========================================================================= *)

let P3N_DISC = prove
 (`?epsd. &0 < epsd /\
   !eps K. &0 < eps /\ eps <= epsd /\ &0 <= K
     ==> ?dd0. &0 < dd0 /\
         !L. &0 <= L
             ==> ?dl1. &0 < dl1 /\
         !(hs:(A)rfs_history) C eps' dl hh k g0 A0 Phi m0 m h d1 Gf sf d0 dd.
           rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
           rfs_surgery_ok hs C eps' dl hh k /\
           &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= dl1 /\
           p3_std_initial g0 A0 /\
           mfd_param (hs_top hs (k - 1)) (hs_atlas hs (k - 1))
                     {x | p3_std_dist g0 x < m} Phi /\
           &0 < h /\ &0 < d1 /\ inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= m /\
           &0 < dd /\ dd <= dd0 /\
           (!s. hs_time hs k - d1 < s /\ s < hs_time hs k
                ==> metric_field (:real^3) (Gf s) /\ &0 <= sf s /\ sf s < &1 /\
                    (!y. p3_std_dist g0 y < m0
                         ==> lck_dist2 (rfs_kreg eps) (Gf s)
                               (\z. inv(h pow 2) %%
                                    rfs_pullback (hs_atlas hs (k - 1)) Phi
                                                 (hs_metric hs (k - 1) s) z) y
                             < dd pow 2) /\
                    (!x. d0 - inv eps < p3_std_dist g0 x /\
                         p3_std_dist g0 x < d0 + inv eps
                         ==> lck_dist2 (rfs_kreg eps)
                               (mpullback (p3_std_nc g0 A0) (cylinder_flow (sf s)))
                               (Gf s) x < dd pow 2) /\
                    (!y. p3_std_dist g0 y < m
                         ==> mfd_scalar (hs_atlas hs (k - 1)) (hs_metric hs (k - 1) s) (Phi y) *
                             h pow 2 <= K /\ norm y <= L /\
                             !w. w dot (rfs_pullback (hs_atlas hs (k - 1)) Phi
                                                     (hs_metric hs (k - 1) s) y ** w)
                                 <= (h pow 2 * L) * (w dot w)))
           ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m})
                        (mfd_cut_spheres (ev_index(hs_event hs k)) (ev_neck(hs_event hs k))) /\
               (IMAGE Phi {x | p3_std_dist g0 x < m} SUBSET topspace(hs_top hs k) \/
                DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < m}) (topspace(hs_top hs k)))`,
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD")) P3N_SLICE_DISC THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_STRONG_NECK_EARLIER) THEN
  REWRITE_TAC[APX_STRONG_NECK_EARLIER_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `kK:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N8"))) THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `K:real`] THEN STRIP_TAC THEN
  USE_THEN "SD" (MP_TAC o SPECL [`eps:real`; `K:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD0"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `L:real` THEN DISCH_TAC THEN
  USE_THEN "SD0" (MP_TAC o SPEC `L:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1s:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SD1"))) THEN
  EXISTS_TAC `min (dl1s / kK) (inv(&2 * kK))` THEN
  SUBGOAL_THEN `&0 < kK` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps':real`; `dl:real->real`;
    `hh:real->real`; `k:num`; `g0:real^3->real^3^3`; `A0:real`; `Phi:real^3->A`; `m0:real`;
    `m:real`; `h:real`; `d1:real`; `Gf:real->real^3->real^3^3`; `sf:real->real`; `d0:real`;
    `dd:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < kK * dl(hs_time (hs:(A)rfs_history) k) /\
                kK * dl(hs_time hs k) <= &1 / &2 /\ kK * dl(hs_time hs k) <= dl1s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dl(hs_time (hs:(A)rfs_history) k) <= min (dl1s / kK) (inv(&2 * kK))` THEN
    UNDISCH_TAC `&0 < dl(hs_time (hs:(A)rfs_history) k)` THEN
    SPEC_TAC(`(dl:real->real)(hs_time (hs:(A)rfs_history) k)`,`dk:real`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `inv(&2 * kK) = (&1 / &2) / kK` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < kK` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `dk <= min (dl1s / kK) (inv(&2 * kK))` THEN
    ASM_REWRITE_TAC[REAL_LE_MIN] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (hs_top (hs:(A)rfs_history) (k - 1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "hausdorff_space"))
          (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ev_index(hs_event (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_metric (hs:(A)rfs_history) (k - 1)) (hs_time hs k)
                   (hs_top hs k,hs_atlas hs k) (hs_metric hs k) (hs_event hs k)` THEN
    REWRITE_TAC[rfs_event_ok; mfd_cut_cap] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_surgery_ok (hs:(A)rfs_history) C eps' dl hh k` THEN
  REWRITE_TAC[rfs_surgery_ok] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:num->A` (LABEL_TAC "yy")) THEN
  MP_TAC(ISPECL
   [`ev_index(hs_event (hs:(A)rfs_history) k)`;
    `\i d. !s. hs_time (hs:(A)rfs_history) k - d < s /\ s < hs_time hs k
               ==> rfs_neck (hs_top hs (k - 1),hs_atlas hs (k - 1))
                            (hs_metric hs (k - 1) s) (kK * dl(hs_time hs k))
                            ((yy:num->A) i) (ev_neck(hs_event hs k) i)`]
   APX_FINITE_DELTA) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC APX_SLICE_NECKS THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "yy" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd"))) THEN
  ABBREV_TAC `t' = (max (hs_time (hs:(A)rfs_history) (k - 1))
                        (max (hs_time hs k - d) (hs_time hs k - d1)) + hs_time hs k) / &2` THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < t' /\ hs_time hs k - d < t' /\
                hs_time hs k - d1 < t' /\ t' < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k` THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < d1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas (hs:(A)rfs_history) (k - 1))
                                  (hs_metric hs (k - 1) t')` ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_time hs (k - 1)) (hs_time hs k) (hs_metric (hs:(A)rfs_history) (k - 1))` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < m})
             (mfd_cut_spheres (ev_index(hs_event hs k)) (ev_neck(hs_event hs k)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_cut_spheres;
                SET_RULE `DISJOINT (s:A->bool) (UNIONS f) <=> !t. t IN f ==> DISJOINT s t`;
                FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nd" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(MP_TAC o SPEC `t':real`)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t':real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `sf:real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "SD1" (MP_TAC o SPECL
     [`g0:real^3->real^3^3`; `A0:real`; `hs_top (hs:(A)rfs_history) (k - 1)`;
      `hs_atlas (hs:(A)rfs_history) (k - 1)`; `hs_metric (hs:(A)rfs_history) (k - 1) t'`;
      `Phi:real^3->A`; `m0:real`; `m:real`; `h:real`; `(Gf:real->real^3->real^3^3) t'`;
      `(sf:real->real) t'`; `d0:real`; `dd:real`; `kK * dl(hs_time (hs:(A)rfs_history) k)`;
      `(yy:num->A) i`; `ev_neck(hs_event (hs:(A)rfs_history) k) i`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_EVENT_DICHOTOMY THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`;
    `hs_atlas (hs:(A)rfs_history) (k - 1)`;
    `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
    `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k`;
    `hs_event (hs:(A)rfs_history) k`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `{x:real^3 | p3_std_dist g0 x < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A)rfs_history) (k - 1)`;
                        `{x:real^3 | p3_std_dist g0 x < m}`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `inv eps < d0` THEN UNDISCH_TAC `d0 + inv eps < m0` THEN
    UNDISCH_TAC `m0 <= m:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3N_STD_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONNECTED_BALL]);;

