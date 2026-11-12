(* ========================================================================= *)
(* Unit pc_p2c_stdc4 (Part 2C; MT Ch 12): MT Thm 12.32, the last clause of   *)
(* P2C_STD_PROPS_STATEMENT, for the maximal standard flow Gs, and the main   *)
(* theorem |- !d:real^4->bool. P2C_STD_PROPS_ROUTE_STATEMENT d.              *)
(*  - R(x,t) >= r^-2: Thm 12.28 (STDS_THM_12_28, STDS_CANON_L_GV): a cap or   *)
(*    a neck of length 1 + eps.                                              *)
(*  - R(x,t) < r^-2: t <= theta < 1 by Prop 12.31; far out an evolving neck   *)
(*    back to time 0 (stds_nmap o power map, the cylinder asymptotics); near   *)
(*    the tip the explicit cap of pc_p2c_stdcap (STDCAP_CAP) with uniform    *)
(*    bounds on [0,theta].                                                    *)
(*  - The view of any G = Gs on [0,1) has the same evolving necks.            *)
(* ========================================================================= *)

needs "src/pc_p2c_stdc3.ml";;
needs "src/pc_p2c_stdcap.ml";;
needs "src/pc_p2c_stdnc3.ml";;
needs "src/pc_p3e_cylrig.ml";;
needs "src/pc_p2b_neckbd.ml";;
needs "src/pc_p2b_flatfwd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Evolving necks in flow views on J = [0,1).  The persistence               *)
(* of the nonempty neck image forces every time of the neck into J, so two  *)
(* flows that agree on J have the same evolving necks; the view of Gs is   *)
(* such a view once Tm = 1.                                                  *)
(* ------------------------------------------------------------------------- *)

let STDS_EVNECK_TIMES = prove
 (`!J (G:real->real^3->real^3^3) eps x t len (e:real^3->real^3) s.
     rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3)) J G)
                       eps x t len e /\
     t - len / mfd_scalar (open_set_atlas (:real^3)) (G t) x < s /\ s <= t
     ==> s IN J`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; rfs_persists] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real`) ASSUME_TAC))) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
  UNDISCH_TAC `rfs_neck
     ((if t IN J then euclidean else discrete_topology {}),open_set_atlas (:real^3))
     ((G:real->real^3->real^3^3) t) eps x e` THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^3) IN IMAGE (e:real^3->real^3) (sphere(vec 0,&1))` THEN SET_TAC[]);;

let STDS_EVNECK_CONG = prove
 (`!(G1:real->real^3->real^3^3) G2 eps x t len (e:real^3->real^3).
     (!s y. &0 <= s /\ s < &1 ==> G1 s y = G2 s y) /\
     rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                      {s | &0 <= s /\ s < &1} G1) eps x t len e
     ==> rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                          {s | &0 <= s /\ s < &1} G2) eps x t len e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eq") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. t - len / mfd_scalar (open_set_atlas (:real^3)) ((G1:real->real^3->real^3^3) t) x < s /\
        s <= t ==> (G1:real->real^3->real^3^3) s = G2 s`
  (LABEL_TAC "times") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^3` THEN
    USE_THEN "eq" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`{s | &0 <= s /\ s < &1}`; `G1:real->real^3->real^3^3`; `eps:real`;
                   `x:real^3`; `t:real`; `len:real`; `e:real^3->real^3`; `s:real`]
                  STDS_EVNECK_TIMES) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real->real^3->real^3^3) t = G2 t` ASSUME_TAC THENL
   [USE_THEN "times" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                   {s | &0 <= s /\ s < &1} G1) eps x t len (e:real^3->real^3)` THEN
    REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; rfs_neck] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> t - a < t`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                 {s | &0 <= s /\ s < &1} G1) eps x t len (e:real^3->real^3)` THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; rfs_close_fam; rfs_persists; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(G2:real->real^3->real^3^3) (t + s / mfd_scalar (open_set_atlas (:real^3)) (G2 t) x) =
    G1 (t + s / mfd_scalar (open_set_atlas (:real^3)) (G2 t) x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    USE_THEN "times" (MATCH_MP_TAC o REWRITE_RULE[ASSUME
      `(G1:real->real^3->real^3^3) t = G2 t`]) THEN
    SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) ((G2:real->real^3->real^3^3) t) x`
    ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G2:real->real^3->real^3^3) t) x` THEN
    SUBGOAL_THEN `--len / R < s / R /\ s / R <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The power maps stds_pw lam y = |y|^(-lam-1) y (lam > 0):                   *)
(* |stds_pw lam y| = |y|^(-lam), they fix the unit sphere, stds_pw (inv lam) *)
(* inverts stds_pw lam, they are diffeomorphisms of annuli (reversing the    *)
(* radius), and they pull cylinder_flow t back to                            *)
(* lam^2 cylinder_flow(1 - (1-t)/lam^2) (P2BN_PW_CYL).                        *)
(* ------------------------------------------------------------------------- *)

let stds_pw = new_definition
 `stds_pw (lam:real) (y:real^3) = norm y rpow (--lam - &1) % y`;;

let STDS_PW_NORM = prove
 (`!lam (y:real^3). ~(y = vec 0) ==> norm(stds_pw lam y) = norm y rpow (--lam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_pw] THEN
  ASM_SIMP_TAC[SMT_POWER_MAP_NORM]);;

let STDS_PW_NZ = prove
 (`!lam (y:real^3). ~(y = vec 0) ==> ~(stds_pw lam y = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lam:real`; `y:real^3`] STDS_PW_NORM) THEN ASM_REWRITE_TAC[NORM_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> ~(&0 = a)`) THEN
  ASM_SIMP_TAC[RPOW_POS_LT; NORM_POS_LT]);;

let STDS_PW_SPHERE = prove
 (`!lam (y:real^3). norm y = &1 ==> stds_pw lam y = y`,
  SIMP_TAC[stds_pw; RPOW_ONE; VECTOR_MUL_LID]);;

let STDS_PW_INV = prove
 (`!lam (y:real^3). &0 < lam /\ ~(y = vec 0) ==> stds_pw (inv lam) (stds_pw lam y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_pw] THEN
  MP_TAC(ISPECL [`--lam`; `--inv lam`; `y:real^3`] SMT_POWER_MAP_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `--lam * --inv lam - &1 = &0` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[RPOW_0; VECTOR_MUL_LID]]);;

let STDS_PW_SMOOTH = prove
 (`!lam. smooth_map_on {x:real^3 | ~(x = vec 0)} (stds_pw lam)`,
  GEN_TAC THEN
  SUBGOAL_THEN `stds_pw lam = (\x:real^3. norm x rpow ((--lam) - &1) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_pw]; REWRITE_TAC[SMOOTH_MAP_ON_POWER_MAP]]);;

let STDS_RPOW_NEG_LT = prove
 (`!lam a b. &0 < lam /\ &0 < a /\ a < b ==> b rpow (--lam) < a rpow (--lam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_NEG] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
  ASM_SIMP_TAC[RPOW_POS_LT; RPOW_LT2; REAL_LT_IMP_LE]);;

let STDS_PW_DIFFEO = prove
 (`!lam a b. &0 < lam /\ &0 < a /\ a < b
             ==> diffeomorphism_on (annulus a b) (annulus (b rpow (--lam)) (a rpow (--lam)))
                   (stds_pw lam) (stds_pw (inv lam))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv lam /\ inv(inv lam) = lam` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b rpow (--lam) /\ b rpow (--lam) < a rpow (--lam)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_RPOW_NEG_LT] THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[STDS_PW_SMOOTH] THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[STDS_PW_SMOOTH] THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `a < norm(y:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_PW_NORM; STDS_PW_INV] THEN CONJ_TAC THEN
    MATCH_MP_TAC STDS_RPOW_NEG_LT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `b rpow --lam < norm(w:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`inv lam`; `w:real^3`] STDS_PW_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[STDS_PW_NORM] THEN
    SUBGOAL_THEN `!r. &0 < r ==> (r rpow (--lam)) rpow (--inv lam) = r` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `--lam * --inv lam = &1` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
        REWRITE_TAC[RPOW_POW; REAL_POW_1]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(a rpow (--lam)) rpow (--inv lam)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC STDS_RPOW_NEG_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RPOW_POS_LT];
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(b rpow (--lam)) rpow (--inv lam)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC STDS_RPOW_NEG_LT THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]]]);;

let STDS_PW_CYL = prove
 (`!lam t (y:real^3).
     &0 < lam /\ ~(y = vec 0)
     ==> mpullback (stds_pw lam) (cylinder_flow t) y =
         (lam pow 2) %% cylinder_flow (&1 - (&1 - t) / lam pow 2) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(--lam - &1) / &2`; `t:real`; `y:real^3`] P2BN_PW_CYL) THEN
  SUBGOAL_THEN `&2 * (--lam - &1) / &2 + &1 = --lam` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NEG_EQ_0; REAL_POW_NEG; ARITH] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; stds_pw] THEN X_GEN_TAC `z:real^3` THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN
  SIMP_TAC[RPOW_RPOW; NORM_POS_LE] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The neck maps stds_emap g0 A0 x lam = stds_nmap g0 A0 x o                 *)
(* stds_pw lam.  d0(nmap_x w) = d0(x) - sqrt 2 log|w|, so                     *)
(* d0(emap y) = d0(x) + sqrt 2 lam log|y|; emap fixes the centre             *)
(* (emap basis1 = x); far out it parametrizes the neck domain and its image  *)
(* is the shell abs(d0 - d0(x)) < lam / eps.                                  *)
(* ------------------------------------------------------------------------- *)

let stds_emap = new_definition
 `stds_emap (g0:real^3->real^3^3) (A0:real) (x:real^3) (lam:real) =
    stds_nmap g0 A0 x o stds_pw lam`;;

let STDS_ORTH_NORM = prove
 (`!(Q:real^3^3) w. orthogonal_matrix Q ==> norm(Q ** w) = norm w`,
  SIMP_TAC[vector_norm; STDS_ORTH_DOT]);;

let STDS_NMAP_DIST = prove
 (`!g0 A0 (x:real^3) w.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ ~(w = vec 0) /\
     sqrt(&2) * log(norm w) < p3_std_dist g0 x
     ==> p3_std_dist g0 (stds_nmap g0 A0 x w) = p3_std_dist g0 x - sqrt(&2) * log(norm w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_nmap] THEN
  MP_TAC(SPEC `x:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(p3_std_nc g0 A0 x) /\
                log(norm(p3_std_nc g0 A0 x)) = (A0 + &4 - p3_std_dist g0 x) / sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_NC_MU_POS; P3S_NC_NORM; LOG_EXP; REAL_EXP_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `mu = norm(p3_std_nc g0 A0 x)` THEN
  SUBGOAL_THEN `norm(mu % (stds_rot x ** (w:real^3))) = mu * norm w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; STDS_ORTH_NORM; REAL_ARITH `&0 < m ==> abs m = m`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `log(norm(mu % (stds_rot x ** (w:real^3)))) =
                (A0 + &4 - p3_std_dist g0 x) / sqrt(&2) + log(norm w)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL [REWRITE_TAC[P3S_SQRT2_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `mu % (stds_rot x ** (w:real^3))`]
               P3S_NCINV_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sqrt(&2) * ((A0 + &4 - p3_std_dist g0 x) / sqrt(&2) + log(norm(w:real^3))) =
                    (A0 + &4 - p3_std_dist g0 x) + sqrt(&2) * log(norm w)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD);;

let STDS_EMAP_DIST = prove
 (`!g0 A0 (x:real^3) lam y.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ ~(y = vec 0) /\ &0 < lam /\
     --(sqrt(&2) * lam * log(norm y)) < p3_std_dist g0 x
     ==> p3_std_dist g0 (stds_emap g0 A0 x lam y) =
         p3_std_dist g0 x + sqrt(&2) * lam * log(norm y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_emap; o_THM] THEN
  SUBGOAL_THEN `log(norm(stds_pw lam (y:real^3))) = --lam * log(norm y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_PW_NORM; LOG_RPOW; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `stds_pw lam (y:real^3)`]
               STDS_NMAP_DIST) THEN
  ASM_SIMP_TAC[STDS_PW_NZ] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let STDS_EMAP_E1 = prove
 (`!g0 A0 (x:real^3) lam.
     p3_std_initial g0 A0 /\ ~(x = vec 0) ==> stds_emap g0 A0 x lam (basis 1) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_emap; o_THM] THEN
  SIMP_TAC[STDS_PW_SPHERE; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[STDS_NMAP_E1]);;

let STDS_EXP_RPOW = prove
 (`!a lam. exp a rpow lam = exp(lam * a)`,
  REWRITE_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP]);;

let STDS_NECK_DOM_EXP = prove
 (`!eps. rfs_neck_dom eps =
         annulus (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps))):real^3->bool`,
  REWRITE_TAC[rfs_neck_dom]);;

(* The neck maps parametrize the neck domain far out.                        *)

let STDS_EMAP_PARAM = prove
 (`!g0 A0 (x:real^3) lam eps.
     p3_std_initial g0 A0 /\ &0 < lam /\ &0 < eps /\
     A0 + lam / eps <= p3_std_dist g0 x
     ==> mfd_param euclidean (open_set_atlas (:real^3)) (rfs_neck_dom eps)
                   (stds_emap g0 A0 x lam) /\
         diffeomorphism_on (rfs_neck_dom eps)
           (annulus (exp(--(lam * inv(sqrt(&2) * eps)))) (exp(lam * inv(sqrt(&2) * eps))))
           (stds_pw lam) (stds_pw (inv lam))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < c /\ sqrt(&2) * (lam * c) = lam / eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[P3S_SQRT2_POS];
      MP_TAC P3S_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (rfs_neck_dom eps)
                  (annulus (exp(--(lam * c))) (exp(lam * c)))
                  (stds_pw lam) (stds_pw (inv lam))` ASSUME_TAC THENL
   [REWRITE_TAC[STDS_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`lam:real`; `exp(--c)`; `exp c`] STDS_PW_DIFFEO) THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT; STDS_EXP_RPOW] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_NEG_NEG] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[stds_emap] THEN
  MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
  MAP_EVERY EXISTS_TAC [`annulus (exp(--(lam * c))) (exp(lam * c)):real^3->bool`;
                        `annulus (exp(--(lam * c))) (exp(lam * c)):real^3->bool`;
                        `stds_pw (inv lam)`] THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS; SUBSET_REFL] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam * c`] STDS_FAR_MU_R) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--(lam * c))`;
                `exp(lam * c)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < lam * c` MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
                                             REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[mfd_param; MFD_DIFFEO_EUCLIDEAN] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closeness through the power maps, and the necks of Gs at a               *)
(* fixed time t <= theta: with lam = sqrt(1-t), pw^* cyl(t) = (1-t) cyl(0),  *)
(* so (1/(1-t)) pw^* (nmap^* Gs(t)) is close to cyl(0) (P2B9S_LCK_SCALE_LE,  *)
(* LCK_DIST2_PULLBACK, STDS_ASYM_CLOSE); its scalar curvature at basis 1 is  *)
(* (1-t) R(z,t), near 1 (P2BN_CYL_SCALAR_STAB), and LCK_DIST_RESCALE gives   *)
(* the eps-neck R(z) e^* Gs(t) ~ cyl(0).                                      *)
(* ------------------------------------------------------------------------- *)

let STDS_DIFFEO_FACTS = prove
 (`!s t (f:real^3->real^3) g.
     diffeomorphism_on s t f g
     ==> open s /\ open t /\ (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> g y IN s) /\
         smooth_map_on s f /\ smooth_map_on t g`,
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let STDS_PW_LCK = prove
 (`!k lam c U U' (G0:real^3->real^3^3) H y.
     &0 < lam /\ &0 < c /\ metric_field U G0 /\ metric_field U H /\
     diffeomorphism_on U' U (stds_pw lam) (stds_pw (inv lam)) /\ y IN U'
     ==> lck_dist2 k (\z. c %% mpullback (stds_pw lam) G0 z)
                     (\z. c %% mpullback (stds_pw lam) H z) y <=
         (&1 + inv c) pow k * lck_dist2 k G0 H (stds_pw lam y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv c) pow k *
              lck_dist2 k (mpullback (stds_pw lam) G0) (mpullback (stds_pw lam) H) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9S_LCK_SCALE_LE THEN EXISTS_TAC `U':real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `stds_pw (inv lam)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `U':real^3->bool`; `stds_pw (inv lam)`] THEN
    ASM_REWRITE_TAC[]]);;

(* The annuli of the neck domains under the power maps.                      *)

let STDS_PW_DOM = prove
 (`!lam eps. &0 < lam /\ lam <= &1 /\ &0 < eps
     ==> annulus (exp(--(lam * inv(sqrt(&2) * eps)))) (exp(lam * inv(sqrt(&2) * eps)))
           SUBSET cball(vec 0:real^3,exp(inv(sqrt(&2) * eps))) DIFF
                  ball(vec 0,exp(--(inv(sqrt(&2) * eps)))) /\
         compact(cball(vec 0:real^3,exp(inv(sqrt(&2) * eps))) DIFF
                 ball(vec 0,exp(--(inv(sqrt(&2) * eps))))) /\
         cball(vec 0:real^3,exp(inv(sqrt(&2) * eps))) DIFF
         ball(vec 0,exp(--(inv(sqrt(&2) * eps)))) SUBSET (:real^3) DELETE vec 0 /\
         annulus (exp(--(lam * inv(sqrt(&2) * eps)))) (exp(lam * inv(sqrt(&2) * eps)))
           SUBSET (:real^3) DELETE vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * c <= c` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(lam * c)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(lam * c))` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    MATCH_MP_TAC STDS_CANNULUS_SUBSET THEN REWRITE_TAC[REAL_EXP_POS_LT];
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `exp(--(lam * c)) < norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
    MP_TAC(SPEC `--(lam * c)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC]);;

(* The neck at (z,t) from closeness of nmap_z^* G to cyl(t) on the annulus  *)
(* K0 = [exp(-c),exp(c)], c = 1/(sqrt 2 eps).                                *)

let STDS_TIME_NECK_GEOM = prove
 (`!g0 A0 (G:real^3->real^3^3) z t eps eta etas alpha.
     p3_std_initial g0 A0 /\ metric_field (:real^3) G /\
     &0 <= t /\ t < &1 /\ &0 < eps /\ eps <= &1 / &4 /\
     A0 + sqrt(&1 - t) / eps <= p3_std_dist g0 z /\
     (!w. w IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
               ball(vec 0,exp(--(inv(sqrt(&2) * eps))))
          ==> lck_dist2 (rfs_kreg eps) (cylinder_flow t)
                        (mpullback (stds_nmap g0 A0 z) G) w < eta) /\
     &0 < eta /\ &2 pow (rfs_kreg eps) * eta < etas pow 2 /\
     &2 pow (rfs_kreg eps) * eta <= (eps / &4) pow 2 /\
     &0 < alpha /\ alpha <= eps / &8 /\
     (!S (G':real^3->real^3^3) y.
        open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G' /\ y IN S /\
        lck_dist2 2 (cylinder_flow (&0)) G' y < etas pow 2
        ==> abs(lscalar G' y - &1) <= alpha)
     ==> abs((&1 - t) * mfd_scalar (open_set_atlas (:real^3)) G z - &1) <= alpha /\
         rfs_neck (euclidean,open_set_atlas (:real^3)) G eps z
                  (stds_emap g0 A0 z (sqrt(&1 - t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lam = sqrt(&1 - t)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1 /\ lam pow 2 = &1 - t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  SUBGOAL_THEN `2 <= k` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2C_KREG_FOUR) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  MP_TAC(SPECL [`lam:real`; `eps:real`] STDS_PW_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`; `lam:real`; `eps:real`]
               STDS_EMAP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = annulus (exp(--(lam * c))) (exp(lam * c)):real^3->bool` THEN
  (* the far point and the nmap diffeo on U *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`; `lam * c`] STDS_FAR_MU_R) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE; REAL_POS];
      SUBGOAL_THEN `sqrt(&2) * lam * c = lam / eps` (fun th -> ASM_REWRITE_TAC[th]) THEN
      EXPAND_TAC "c" THEN MP_TAC P3S_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN
      CONV_TAC REAL_FIELD];
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < lam * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`; `exp(--(lam * c))`;
                `exp(lam * c)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `IMAGE (stds_nmap g0 A0 z) U`; `stds_nmap g0 A0 z`;
                 `(\w. inv(norm(p3_std_nc g0 A0 z)) % (transp(stds_rot z) ** w)) o
                  p3_std_nc g0 A0`] STDS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps:real^3->bool`; `U:real^3->bool`; `stds_pw lam`;
                 `stds_pw (inv lam)`] STDS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H = mpullback (stds_nmap g0 A0 z) (G:real^3->real^3^3)` THEN
  SUBGOAL_THEN `metric_field U (H:real^3->real^3^3) /\ metric_field U (cylinder_flow t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "H" THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (stds_nmap g0 A0 z) U`;
        `(\w. inv(norm(p3_std_nc g0 A0 z)) % (transp(stds_rot z) ** w)) o p3_std_nc g0 A0`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD]];
    ALL_TAC] THEN
  (* the rescaled pullback W on the neck domain *)
  ABBREV_TAC `W = \w:real^3. inv(&1 - t) %% mpullback (stds_pw lam) H w` THEN
  SUBGOAL_THEN `&0 < &1 - t /\ &0 < inv(&1 - t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (W:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `stds_pw (inv lam)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(rfs_neck_dom eps:real^3->bool) /\
                rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET {x:real^3 | ~(x = vec 0)} ==> s SUBSET (:real^3) DELETE vec 0`) THEN
    MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN rfs_neck_dom eps ==> ~(w = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0` THEN SET_TAC[]; ALL_TAC] THEN
  (* closeness of W to cyl(0) on the neck domain *)
  SUBGOAL_THEN `!y. y IN rfs_neck_dom eps
                    ==> lck_dist2 k (cylinder_flow (&0)) W y <= &2 pow k * eta`
  (LABEL_TAC "Wclose") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `lck_dist2 k (cylinder_flow (&0)) W y =
                  lck_dist2 k (\w. inv(&1 - t) %% mpullback (stds_pw lam) (cylinder_flow t) w)
                              (\w. inv(&1 - t) %% mpullback (stds_pw lam) H w) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[STDS_PW_CYL] THEN
      REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(&1 - t) * (&1 - t) = &1 /\ &1 - (&1 - t) / (&1 - t) = &0`
      (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LID]) THEN
      UNDISCH_TAC `&0 < &1 - t` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv(inv(&1 - t))) pow k *
                lck_dist2 k (cylinder_flow t) H (stds_pw lam y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STDS_PW_LCK THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `rfs_neck_dom eps:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_INV] THEN
    SUBGOAL_THEN `(&1 + (&1 - t)) pow k <= &2 pow k` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lck_dist2 k (cylinder_flow t) H (stds_pw lam y) < eta /\
                  &0 <= lck_dist2 k (cylinder_flow t) H (stds_pw lam y)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `stds_pw lam (y:real^3) IN U` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow k * lck_dist2 k (cylinder_flow t) H (stds_pw lam y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE; REAL_POS]];
    ALL_TAC] THEN
  (* the scalar curvature of W at basis 1 *)
  SUBGOAL_THEN `(basis 1:real^3) IN rfs_neck_dom eps /\ (basis 1:real^3) IN U /\
                norm(basis 1:real^3) = &1` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      EXPAND_TAC "U" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
      MP_TAC(SPEC `lam * c` REAL_EXP_LE_X) THEN MP_TAC(SPEC `--(lam * c)` REAL_EXP_POS_LT) THEN
      REWRITE_TAC[REAL_EXP_NEG] THEN
      SUBGOAL_THEN `&1 < exp(lam * c)` MP_TAC THENL
       [MP_TAC(SPEC `lam * c` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT DISCH_TAC THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
        ASM_REWRITE_TAC[REAL_LT_01];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (W:real^3->real^3^3) (basis 1) =
                (&1 - t) * mfd_scalar (open_set_atlas (:real^3)) G z` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps:real^3->bool`; `mpullback (stds_pw lam) (H:real^3->real^3^3)`;
                   `inv(&1 - t)`; `basis 1:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `stds_pw (inv lam)`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `rfs_neck_dom eps:real^3->bool`; `stds_pw lam`;
                   `stds_pw (inv lam)`; `H:real^3->real^3^3`; `basis 1:real^3`]
                  LSCALAR_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[STDS_PW_SPHERE] THEN EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`IMAGE (stds_nmap g0 A0 z) U`; `U:real^3->bool`; `stds_nmap g0 A0 z`;
                   `(\w. inv(norm(p3_std_nc g0 A0 z)) % (transp(stds_rot z) ** w)) o
                    p3_std_nc g0 A0`; `G:real^3->real^3^3`; `basis 1:real^3`]
                  LSCALAR_PULLBACK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[STDS_NMAP_E1; RFB_OPEN_SET_MFD_SCALAR; OPEN_UNIV; IN_UNIV] THEN
    UNDISCH_TAC `&0 < &1 - t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((&1 - t) * mfd_scalar (open_set_atlas (:real^3)) G z - &1) <= alpha`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `lscalar (W:real^3->real^3^3) (basis 1) =
                  (&1 - t) * mfd_scalar (open_set_atlas (:real^3)) G z`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) W (basis 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 pow k * eta` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) G z` THEN
  ABBREV_TAC `cp = (&1 - t) * R` THEN
  SUBGOAL_THEN `&0 < cp /\ cp <= &1 + alpha /\ abs(cp - &1) <= alpha` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1 - t`; `R:real`] (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck; STDCAP_OSA_FACTS] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^3` THEN
    ASM_SIMP_TAC[STDS_EMAP_E1; IN_SPHERE_0];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  EXISTS_TAC `((&1 + alpha) * (eps / &4) + alpha * (&7 / &4)) pow 2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= &2 * (eps / &4) /\ alpha <= eps / &8 /\ &0 < eps
                               ==> x + alpha * &7 / &4 < eps`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 k (cylinder_flow (&0))
      (\y. R %% rfs_pullback (open_set_atlas (:real^3)) (stds_emap g0 A0 z lam) G y) y =
    lck_dist2 k (cylinder_flow (&0)) (\w. cp %% (W:real^3->real^3^3) w) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[STDS_RFS_PULLBACK_UNIV; stds_emap] THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0) /\ stds_pw lam (w:real^3) IN U` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`stds_pw lam`; `stds_nmap g0 A0 z`; `G:real^3->real^3^3`; `w:real^3`]
                  APX_MPULLBACK_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
        ASM_REWRITE_TAC[STDS_PW_SMOOTH; IN_ELIM_THM; OPEN_NONZERO];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "W" THEN ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "cp" THEN
    UNDISCH_TAC `&0 < &1 - t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps:real^3->bool`; `cylinder_flow (&0)`;
                 `W:real^3->real^3^3`; `cp:real`; `y:real^3`] LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN `sqrt(&3) <= &7 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) W y) <= eps / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow k * eta` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (&0)) (\w. cp %% (W:real^3->real^3^3) w) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_SIMP_TAC[RFB_METRIC_FIELD_CMUL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (&0)) (\w. cp %% (W:real^3->real^3^3) w) y) <=
                (&1 + alpha) * (eps / &4) + alpha * (&7 / &4)` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (&0)) W y /\ &0 <= sqrt(&3)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cp * sqrt(lck_dist2 k (cylinder_flow (&0)) W y) + abs(cp - &1) * sqrt(&3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> a + b <= c + d`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow (&0)) (\w. cp %% (W:real^3->real^3^3) w) y =
                sqrt(lck_dist2 k (cylinder_flow (&0)) (\w. cp %% (W:real^3->real^3^3) w) y) pow 2`
  SUBST1_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Evolving necks of Gs back to time 0 far out.  With                       *)
(* R = R(x,t), lam = R^(-1/2) and delta = 1 - R(1-t): at rescaled time s,    *)
(* tau = t + s/R, R pw^* cyl(tau) = cyl(s + delta) exactly, so               *)
(* R pw^*(nmap^* Gs(tau)) is close to cyl(s + delta); the base shift         *)
(* cyl(s+delta) -> cyl(s) costs a factor (1+delta)^(k+2) and the term         *)
(* lck(cyl s)(cyl(s+delta)) <= ((1+delta)^(k+2) 2 delta)^2 (P3E_LCK_CYL_SHIFT,*)
(* LCK_DIST_CYLINDER_BASE, LCK_DIST_TRIANGLE).                               *)
(* ------------------------------------------------------------------------- *)

let STDS_PW_DOM2 = prove
 (`!lam lmax eps. &0 < lam /\ lam <= lmax /\ &0 < eps
     ==> annulus (exp(--(lam * inv(sqrt(&2) * eps)))) (exp(lam * inv(sqrt(&2) * eps)))
           SUBSET cball(vec 0:real^3,exp(lmax * inv(sqrt(&2) * eps))) DIFF
                  ball(vec 0,exp(--(lmax * inv(sqrt(&2) * eps)))) /\
         compact(cball(vec 0:real^3,exp(lmax * inv(sqrt(&2) * eps))) DIFF
                 ball(vec 0,exp(--(lmax * inv(sqrt(&2) * eps))))) /\
         cball(vec 0:real^3,exp(lmax * inv(sqrt(&2) * eps))) DIFF
         ball(vec 0,exp(--(lmax * inv(sqrt(&2) * eps)))) SUBSET (:real^3) DELETE vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * c <= lmax * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(lam * c)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(lam * c))` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    MATCH_MP_TAC STDS_CANNULUS_SUBSET THEN REWRITE_TAC[REAL_EXP_POS_LT]]);;

(* (1 + a)^n <= 2 for 0 <= a, n a <= 1/2.                                     *)

let STDS_POW_SMALL = prove
 (`!n a. &0 <= a /\ &n * a <= &1 / &2 ==> (&1 + a) pow n <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&n * a)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_LE_X]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1 / &2)` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC]);;

(* The base shift cyl(s + delta) -> cyl(s), s <= 0.                          *)

let STDS_CYL_SHIFT_EQ = prove
 (`!s delta (z:real^3).
     ~(z = vec 0)
     ==> cylinder_flow delta z + cylinder_flow s z - cylinder_flow (&0) z =
         cylinder_flow (s + delta) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `delta:real`; `z:real^3`] P3E_CYL_SHIFT_AFFINE) THEN
  MP_TAC(SPECL [`delta:real`; `z:real^3`] P3E_CYL_AFFINE) THEN
  MP_TAC(SPECL [`s:real`; `z:real^3`] P3E_CYL_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let STDS_BASE_SHIFT = prove
 (`!k s delta U (Gf:real^3->real^3^3) y B.
     s <= &0 /\ abs delta <= &1 / &2 /\ open U /\ U SUBSET (:real^3) DELETE vec 0 /\
     metric_field U Gf /\
     (!w. w IN U ==> lck_dist2 k (cylinder_flow (s + delta)) Gf w <= B pow 2) /\
     &0 <= B /\ (&1 + abs delta) * B < &1 /\ y IN U
     ==> sqrt(lck_dist2 k (cylinder_flow s) Gf y) <=
         (&1 + abs delta) pow (k + 2) * B +
         (&1 + abs delta) pow (k + 2) * (&2 * abs delta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < &1 /\ s + delta < &1 /\ &1 <= &1 - s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m0 = max (&1) ((&1 - (s + delta)) / (&1 - s))` THEN
  SUBGOAL_THEN `&1 <= m0 /\ m0 <= &1 + abs delta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= c /\ b <= c ==> max (&1) b <= c`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `abs delta * &1 <= abs delta * (&1 - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN U ==> ~(z = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `U SUBSET (:real^3) DELETE vec 0` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN U ==> sqrt(lck_dist2 k (cylinder_flow (s + delta)) Gf w) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow s) /\ metric_field U (cylinder_flow (s + delta)) /\
                metric_field U (cylinder_flow (&0)) /\ metric_field U (cylinder_flow delta)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G1 = \z:real^3. Gf z + cylinder_flow s z - cylinder_flow (s + delta) z` THEN
  SUBGOAL_THEN `metric_field U (G1:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN MATCH_MP_TAC P3E_SHIFT_METRIC_FIELD THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 + abs delta) * B` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[SQRT_POS_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P3E_LCK_DIST2_POS THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow (s + delta)) Gf w)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^3->bool`; `cylinder_flow s`; `G1:real^3->real^3^3`;
                 `Gf:real^3->real^3^3`; `y:real^3`] LCK_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow s)
                  (\z. cylinder_flow s z + (Gf:real^3->real^3^3) z - G1 z) y =
                lck_dist2 k (cylinder_flow s)
                  (\z. cylinder_flow delta z + cylinder_flow s z - cylinder_flow (&0) z) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "G1" THEN
    ASM_SIMP_TAC[STDS_CYL_SHIFT_EQ] THEN MATRIX_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow s) G1 y) +
              sqrt(lck_dist2 k (cylinder_flow s)
                     (\z. cylinder_flow delta z + cylinder_flow s z - cylinder_flow (&0) z) y)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= (&1 + abs delta) pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> a + b <= c + d`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(m0 pow (k + 2) * lck_dist2 k (cylinder_flow (s + delta)) Gf y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN EXPAND_TAC "m0" THEN EXPAND_TAC "G1" THEN
      MATCH_MP_TAC P3E_LCK_CYL_SHIFT THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (s + delta)) Gf y` ASSUME_TAC THENL
     [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= m0 pow (k + 2) /\ m0 pow (k + 2) <= (&1 + abs delta) pow (k + 2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_MUL; REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m0 pow (k + 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow (&0)) (cylinder_flow delta) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (&1) ((&1 - &0) / (&1 - s)) pow (k + 2) *
                lck_dist2 k (cylinder_flow (&0)) (cylinder_flow delta) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3E_LCK_CYL_SHIFT THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `max (&1) ((&1 - &0) / (&1 - s)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `b <= &1 ==> max (&1) b = &1`) THEN
      SUBGOAL_THEN `&0 < &1 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `delta:real`; `U:real^3->bool`; `cylinder_flow delta`; `y:real^3`]
               LCK_DIST_CYLINDER_BASE) THEN
  ASM_REWRITE_TAC[P2BL_LCK_DIST2_REFL; SQRT_0; REAL_ADD_LID]);;

(* The family closeness of an evolving neck back to time 0.                  *)

let STDS_EVNECK_GEOM = prove
 (`!g0 A0 (Gt:real->real^3->real^3^3) x t eps eta alpha.
     p3_std_initial g0 A0 /\ (!s. &0 <= s /\ s <= t ==> metric_field (:real^3) (Gt s)) /\
     &0 < t /\ t < &1 /\ &0 < eps /\ eps <= &1 / &4 /\
     A0 + &2 / eps <= p3_std_dist g0 x /\
     abs((&1 - t) * mfd_scalar (open_set_atlas (:real^3)) (Gt t) x - &1) <= alpha /\
     (!s w. &0 <= s /\ s <= t /\
            w IN cball(vec 0,exp(&2 * inv(sqrt(&2) * eps))) DIFF
                 ball(vec 0,exp(--(&2 * inv(sqrt(&2) * eps))))
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                          (mpullback (stds_nmap g0 A0 x) (Gt s)) w < eta) /\
     &0 < eta /\ &3 pow (rfs_kreg eps) * eta <= (eps / &8) pow 2 /\
     &0 < alpha /\ alpha <= eps / &16 /\ &(rfs_kreg eps + 2) * alpha <= &1 / &2
     ==> rfs_close_fam (rfs_kreg eps) eps
           {s | --(t * mfd_scalar (open_set_atlas (:real^3)) (Gt t) x) < s /\ s <= &0}
           (rfs_neck_dom eps) cylinder_flow
           (\s y. mfd_scalar (open_set_atlas (:real^3)) (Gt t) x %%
                  rfs_pullback (open_set_atlas (:real^3))
                    (stds_emap g0 A0 x (inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) (Gt t) x))))
                    (Gt (t + s / mfd_scalar (open_set_atlas (:real^3)) (Gt t) x)) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((Gt:real->real^3->real^3^3) t) x` THEN
  SUBGOAL_THEN `&1 / &2 <= R /\ &0 < R` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= (&1 - t) * R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t) * R <= &1 * R \/ R < &0` MP_TAC THENL
     [ASM_CASES_TAC `&0 <= R` THENL
       [DISJ1_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t) * R <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - t) * --R ==> (&1 - t) * R <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &2 /\ R * lam pow 2 = &1 /\ inv R <= &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    SUBGOAL_THEN `&0 < sqrt R /\ sqrt R pow 2 = R` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_INV] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `delta = &1 - (&1 - t) * R` THEN
  SUBGOAL_THEN `abs delta <= alpha` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  MP_TAC(SPECL [`lam:real`; `&2`; `eps:real`] STDS_PW_DOM2) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam:real`; `eps:real`]
               STDS_EMAP_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A0 + &2 / eps` THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `U = annulus (exp(--(lam * c))) (exp(lam * c)):real^3->bool` THEN
  SUBGOAL_THEN `&0 < lam * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam * c`] STDS_FAR_MU_R) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `sqrt(&2) * lam * c = lam / eps` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN MP_TAC P3S_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A0 + &2 / eps` THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--(lam * c))`;
                `exp(lam * c)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `IMAGE (stds_nmap g0 A0 x) U`; `stds_nmap g0 A0 x`;
                 `(\w. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** w)) o
                  p3_std_nc g0 A0`] STDS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps:real^3->bool`; `U:real^3->bool`; `stds_pw lam`;
                 `stds_pw (inv lam)`] STDS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(rfs_neck_dom eps:real^3->bool) /\
                rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET {x:real^3 | ~(x = vec 0)} ==> s SUBSET (:real^3) DELETE vec 0`) THEN
    MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN rfs_neck_dom eps ==> ~(w = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `U SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b /\ b SUBSET c ==> a SUBSET c`) THEN
    EXISTS_TAC `cball(vec 0:real^3,exp(&2 * c)) DIFF ball(vec 0,exp(--(&2 * c)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  EXISTS_TAC `(eps / &2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN BETA_TAC THEN
  ABBREV_TAC `tau = t + s / R` THEN
  SUBGOAL_THEN `&0 <= tau /\ tau <= t /\ tau < &1 /\ &1 - (&1 - tau) * R = s + delta`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `--t < s / R /\ s / R <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MAP_EVERY EXPAND_TAC ["tau"; "delta"] THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `H = mpullback (stds_nmap g0 A0 x) ((Gt:real->real^3->real^3^3) tau)` THEN
  SUBGOAL_THEN `metric_field U (H:real^3->real^3^3) /\ metric_field U (cylinder_flow tau)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "H" THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (stds_nmap g0 A0 x) U`;
        `(\w. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** w)) o p3_std_nc g0 A0`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_SIMP_TAC[SUBSET_UNIV];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD]];
    ALL_TAC] THEN
  ABBREV_TAC `Gf = \w:real^3. R %% mpullback (stds_pw lam) H w` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (Gf:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Gf" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `stds_pw (inv lam)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the family term is Gf on the neck domain *)
  SUBGOAL_THEN
   `lck_dist2 k (cylinder_flow s)
      (\y. R %% rfs_pullback (open_set_atlas (:real^3)) (stds_emap g0 A0 x lam)
                ((Gt:real->real^3->real^3^3) tau) y) y =
    lck_dist2 k (cylinder_flow s) Gf y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[STDS_RFS_PULLBACK_UNIV; stds_emap] THEN EXPAND_TAC "Gf" THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0) /\ stds_pw lam (w:real^3) IN U` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`stds_pw lam`; `stds_nmap g0 A0 x`; `(Gt:real->real^3->real^3^3) tau`;
                   `w:real^3`] APX_MPULLBACK_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
        ASM_REWRITE_TAC[STDS_PW_SMOOTH; IN_ELIM_THM; OPEN_NONZERO];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* closeness to cyl(s + delta) *)
  SUBGOAL_THEN `!w. w IN rfs_neck_dom eps
                    ==> lck_dist2 k (cylinder_flow (s + delta)) Gf w <= (eps / &8) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `lck_dist2 k (cylinder_flow (s + delta)) Gf w =
                  lck_dist2 k (\z. R %% mpullback (stds_pw lam) (cylinder_flow tau) z)
                              (\z. R %% mpullback (stds_pw lam) H z) w`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Gf" THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[STDS_PW_CYL; MATRIX_CMUL_ASSOC] THEN
      SUBGOAL_THEN `&1 - (&1 - tau) / lam pow 2 = s + delta` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `&1 - (&1 - tau) * R = s + delta`)) THEN
        UNDISCH_TAC `R * lam pow 2 = &1` THEN UNDISCH_TAC `&0 < lam` THEN
        CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[MATRIX_CMUL_LID]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv R) pow k * lck_dist2 k (cylinder_flow tau) H (stds_pw lam w)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STDS_PW_LCK THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `rfs_neck_dom eps:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `stds_pw lam (w:real^3) IN U` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `lck_dist2 k (cylinder_flow tau) H (stds_pw lam w) < eta /\
                  &0 <= lck_dist2 k (cylinder_flow tau) H (stds_pw lam w)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "H" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + inv R) pow k <= &3 pow k` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow k * eta` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the base shift *)
  MP_TAC(SPECL [`k:num`; `s:real`; `delta:real`; `rfs_neck_dom eps:real^3->bool`;
                `Gf:real^3->real^3^3`; `y:real^3`; `eps / &8`] STDS_BASE_SHIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &17 / &16 * (&1 / &32) ==> x < &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k + 2`; `abs delta`] STDS_POW_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(k + 2) * alpha` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    DISCH_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow s) Gf y) <= eps / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs delta) pow (k + 2) * eps / &8 +
                (&1 + abs delta) pow (k + 2) * (&2 * abs delta)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * eps / &8 + &2 * (&2 * alpha)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> a + b <= c + d`) THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&0 <= &1 + abs x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s) Gf y` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow s) Gf y =
                sqrt(lck_dist2 k (cylinder_flow s) Gf y) pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* The far evolving necks.  At a far point x and a time t < 1                *)
(* with nmap_x^* Gt close to the cylinder flow on [0,t], the map             *)
(* stds_emap x R^(-1/2), R = R(x,t), is an evolving eps-neck of length t R   *)
(* (back to time 0); its image stays in the shell abs(d0 - d0(x)) < 2/eps.  *)
(* ------------------------------------------------------------------------- *)

let STDS_NECK_DOM_LOG = prove
 (`!eps (y:real^3).
     &0 < eps /\ y IN rfs_neck_dom eps
     ==> ~(y = vec 0) /\ --inv(sqrt(&2) * eps) < log(norm y) /\
         log(norm y) < inv(sqrt(&2) * eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STDS_NECK_DOM_EXP; annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `exp(--c)` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POS_LT];
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    ASM_REWRITE_TAC[]]);;

let STDS_EMAP_SHELL = prove
 (`!g0 A0 (x:real^3) lam eps y.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < lam /\ &0 < eps /\
     lam / eps < p3_std_dist g0 x /\ y IN rfs_neck_dom eps
     ==> abs(p3_std_dist g0 (stds_emap g0 A0 x lam y) - p3_std_dist g0 x) < lam / eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `y:real^3`] STDS_NECK_DOM_LOG) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[P3S_SQRT2_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(&2) * lam) * inv(sqrt(&2) * eps) = lam / eps` ASSUME_TAC THENL
   [MP_TAC P3S_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(&2) * lam) * log(norm(y:real^3)) < (sqrt(&2) * lam) * inv(sqrt(&2) * eps) /\
                (sqrt(&2) * lam) * --inv(sqrt(&2) * eps) < (sqrt(&2) * lam) * log(norm y)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam:real`; `y:real^3`]
               STDS_EMAP_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&2) * lam * log(norm(y:real^3)) = (sqrt(&2) * lam) * log(norm y)`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_ASSOC]; ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * lam * log(norm(y:real^3)) = (sqrt(&2) * lam) * log(norm y)`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_ASSOC]; ASM_REAL_ARITH_TAC]);;

(* The far evolving neck.                                                    *)

let STDS_FAR_EVNECK = prove
 (`!g0 A0 (Gt:real->real^3->real^3^3) x t eps eta etas alpha.
     p3_std_initial g0 A0 /\ (!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) (Gt s)) /\
     &0 < t /\ t < &1 /\ &0 < eps /\ eps <= &1 / &4 /\
     A0 + &5 + &2 / eps <= p3_std_dist g0 x /\
     (!s w. &0 <= s /\ s <= t /\
            w IN cball(vec 0,exp(&2 * inv(sqrt(&2) * eps))) DIFF
                 ball(vec 0,exp(--(&2 * inv(sqrt(&2) * eps))))
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                          (mpullback (stds_nmap g0 A0 x) (Gt s)) w < eta) /\
     &0 < eta /\ &3 pow (rfs_kreg eps) * eta <= (eps / &8) pow 2 /\
     &2 pow (rfs_kreg eps) * eta < etas pow 2 /\
     &0 < alpha /\ alpha <= eps / &16 /\ &(rfs_kreg eps + 2) * alpha <= &1 / &2 /\
     (!S (G':real^3->real^3^3) y.
        open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G' /\ y IN S /\
        lck_dist2 2 (cylinder_flow (&0)) G' y < etas pow 2
        ==> abs(lscalar G' y - &1) <= alpha)
     ==> ?e. rfs_evolving_neck (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                              {s | &0 <= s /\ s < &1} Gt)
               eps x t (t * mfd_scalar (open_set_atlas (:real^3)) (Gt t) x) e /\
             !z. z IN IMAGE e (rfs_neck_dom eps) ==> A0 + &5 <= p3_std_dist g0 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / eps /\ sqrt(&1 - t) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `&0`] STDS_FAR_MU_R) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
                    SIMP_TAC[]];
    ALL_TAC] THEN
  (* hypotheses of the time-t neck lemma *)
  SUBGOAL_THEN `metric_field (:real^3) ((Gt:real->real^3->real^3^3) t) /\
                (!s. &0 <= s /\ s <= t ==> metric_field (:real^3) ((Gt:real->real^3->real^3^3) s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REPEAT STRIP_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + sqrt(&1 - t) / eps <= p3_std_dist g0 x /\ A0 + &2 / eps <= p3_std_dist g0 x`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 - t) / eps <= &2 / eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. w IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
                    ball(vec 0,exp(--(inv(sqrt(&2) * eps))))
               ==> lck_dist2 (rfs_kreg eps) (cylinder_flow t)
                     (mpullback (stds_nmap g0 A0 x) ((Gt:real->real^3->real^3^3) t)) w < eta`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `exp(inv(sqrt(&2) * eps)) <= exp(&2 * inv(sqrt(&2) * eps)) /\
                  exp(--(&2 * inv(sqrt(&2) * eps))) <= exp(--(inv(sqrt(&2) * eps)))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
                               ball(vec 0,exp(--(inv(sqrt(&2) * eps))))` THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow (rfs_kreg eps) * eta <= (eps / &4) pow 2 /\ alpha <= eps / &8`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow (rfs_kreg eps) * eta` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps / &8) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(Gt:real->real^3->real^3^3) t`; `x:real^3`;
                `t:real`; `eps:real`; `eta:real`; `etas:real`; `alpha:real`]
               STDS_TIME_NECK_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  (* the family closeness *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `Gt:real->real^3->real^3^3`; `x:real^3`;
                `t:real`; `eps:real`; `eta:real`; `alpha:real`] STDS_EVNECK_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((Gt:real->real^3->real^3^3) t) x` THEN
  SUBGOAL_THEN `&1 / &2 <= R /\ &0 < R` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= (&1 - t) * R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t) * R <= &1 * R \/ R < &0` MP_TAC THENL
     [ASM_CASES_TAC `&0 <= R` THENL
       [DISJ1_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t) * R <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - t) * --R ==> (&1 - t) * R <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam / eps <= &2 / eps` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam:real`; `eps:real`]
               STDS_EMAP_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  EXISTS_TAC `stds_emap g0 A0 x lam` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam:real`; `eps:real`;
                  `y:real^3`] STDS_EMAP_SHELL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN `(t * R) / R = t /\ &0 < t * R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the neck at time t is the slice s = 0 of the family *)
  SUBGOAL_THEN `rfs_close_on (rfs_kreg eps) eps (rfs_neck_dom eps) (cylinder_flow (&0))
                  (\y. R %% rfs_pullback (open_set_atlas (:real^3)) (stds_emap g0 A0 x lam)
                                         ((Gt:real->real^3->real^3^3) t) y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_close_fam (rfs_kreg eps) eps {s | --(t * R) < s /\ s <= &0}
                   (rfs_neck_dom eps) cylinder_flow
                   (\s y. R %% rfs_pullback (open_set_atlas (:real^3)) (stds_emap g0 A0 x lam)
                                 ((Gt:real->real^3->real^3^3) (t + s / R)) y)` THEN
    REWRITE_TAC[rfs_close_fam; rfs_close_on; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `&0 / x = &0`; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((Gt:real->real^3->real^3^3) t)
                         eps x (stds_emap g0 A0 x lam)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck; STDCAP_OSA_FACTS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^3` THEN
    ASM_SIMP_TAC[STDS_EMAP_E1; IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in euclidean (IMAGE (stds_emap g0 A0 x lam) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`open_set_atlas (:real^3)`; `rfs_neck_dom eps:real^3->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; OPEN_ANNULUS];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
  REWRITE_TAC[rfs_persists] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s /\ s < &1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS]);;

(* ------------------------------------------------------------------------- *)
(* The radial structure of the neck maps.  d0 = rho(|y|), so                 *)
(* {d0 < b} = ball(0,rinv b); emap x lam w is the radial map                 *)
(* rinv(d0(x) + sqrt 2 lam log|w|)/|w| (Q w), Q = stds_rot x; its image of   *)
(* the neck domain is the shell abs(d0 - d0(x)) < lam/eps; the profile       *)
(* r -> rinv(D + sqrt 2 lam log r) has a positive derivative.                *)
(* ------------------------------------------------------------------------- *)

let STDS_DIST_RINV = prove
 (`!g0 A0 b (y:real^3).
     p3_std_initial g0 A0 /\ &0 <= b
     ==> (p3_std_dist g0 y < b <=> norm y < p3s_rad_rinv g0 b) /\
         (b < p3_std_dist g0 y <=> p3s_rad_rinv g0 b < norm y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `b:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`; `p3s_rad_rinv g0 b`]
               P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC);;

let STDS_DIST_BALL = prove
 (`!g0 A0 b.
     p3_std_initial g0 A0 /\ &0 <= b
     ==> {y:real^3 | p3_std_dist g0 y < b} = ball(vec 0,p3s_rad_rinv g0 b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN
  ASM_MESON_TAC[STDS_DIST_RINV]);;

let STDS_DIST_ANNULUS = prove
 (`!g0 A0 a b.
     p3_std_initial g0 A0 /\ &0 <= a /\ &0 <= b
     ==> {y:real^3 | a < p3_std_dist g0 y /\ p3_std_dist g0 y < b} =
         annulus (p3s_rad_rinv g0 a) (p3s_rad_rinv g0 b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; annulus] THEN
  ASM_MESON_TAC[STDS_DIST_RINV]);;

(* The radial form of the neck maps.                                         *)

let STDS_EMAP_RADIAL = prove
 (`!g0 A0 (x:real^3) lam w.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < lam /\ ~(w = vec 0)
     ==> stds_emap g0 A0 x lam w =
         (p3s_rad_rinv g0 (p3_std_dist g0 x + sqrt(&2) * lam * log(norm w)) / norm w) %
         (stds_rot x ** w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stds_emap; o_THM; stds_nmap; stds_pw; p3s_ncinv] THEN
  MP_TAC(SPEC `x:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(p3_std_nc g0 A0 x) /\
                log(norm(p3_std_nc g0 A0 x)) = (A0 + &4 - p3_std_dist g0 x) / sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_NC_MU_POS; P3S_NC_NORM; LOG_EXP; REAL_EXP_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `Q = stds_rot x` THEN
  ABBREV_TAC `mu = norm(p3_std_nc g0 A0 x)` THEN
  ABBREV_TAC `q = norm(w:real^3) rpow (--lam - &1)` THEN
  SUBGOAL_THEN `&0 < q /\ log q = (--lam - &1) * log(norm(w:real^3))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[RPOW_POS_LT; LOG_RPOW]; ALL_TAC] THEN
  SUBGOAL_THEN `mu % ((Q:real^3^3) ** (q % w)) = (mu * q) % (Q ** w)` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu * q` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((mu * q) % ((Q:real^3^3) ** w)) = (mu * q) * norm w` SUBST1_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; STDS_ORTH_NORM; REAL_ARITH `&0 < a ==> abs a = a`]; ALL_TAC] THEN
  SUBGOAL_THEN `log((mu * q) * norm(w:real^3)) =
                (A0 + &4 - p3_std_dist g0 x) / sqrt(&2) - lam * log(norm w)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &4 - sqrt(&2) * ((A0 + &4 - p3_std_dist g0 x) / sqrt(&2) -
                                      lam * log(norm(w:real^3))) =
                p3_std_dist g0 x + sqrt(&2) * lam * log(norm w)` SUBST1_TAC THENL
   [MP_TAC P3S_SQRT2_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < mu * q` THEN UNDISCH_TAC `&0 < norm(w:real^3)` THEN
  CONV_TAC REAL_FIELD);;

(* The image of the neck domain is the shell abs(d0 - d0(x)) < lam / eps.    *)

let STDS_EMAP_IMAGE = prove
 (`!g0 A0 (x:real^3) lam eps.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < lam /\ &0 < eps /\
     lam / eps < p3_std_dist g0 x
     ==> IMAGE (stds_emap g0 A0 x lam) (rfs_neck_dom eps) =
         {y | abs(p3_std_dist g0 y - p3_std_dist g0 x) < lam / eps}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDS_EMAP_SHELL THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `abs(p3_std_dist g0 (vec 0:real^3) - p3_std_dist g0 x) < lam / eps` THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `vec 0:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[NORM_0; P3S_RHO_0] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < sqrt(&2) * lam` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  ABBREV_TAC `s = (p3_std_dist g0 y - p3_std_dist g0 x) / (sqrt(&2) * lam)` THEN
  MP_TAC(SPEC `x:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = stds_rot x` THEN
  ABBREV_TAC `w' = exp s % inv(norm y) % (y:real^3)` THEN
  SUBGOAL_THEN `norm(w':real^3) = exp s` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_EXP; REAL_ABS_INV; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal_matrix(transp(Q:real^3^3)) /\
                (Q:real^3^3) ** (transp Q ** w') = w'` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  EXISTS_TAC `transp(Q:real^3^3) ** w'` THEN
  SUBGOAL_THEN `norm(transp(Q:real^3^3) ** w') = exp s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_ORTH_NORM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(transp(Q:real^3^3) ** w' = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `lam:real`;
                  `transp(Q:real^3^3) ** w'`] STDS_EMAP_RADIAL) THEN
    ASM_REWRITE_TAC[LOG_EXP] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `p3_std_dist g0 x + sqrt(&2) * lam * s = p3_std_dist g0 y` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN UNDISCH_TAC `&0 < sqrt(&2) * lam` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`] P3S_RINV_UNIQUE) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
    SUBST1_TAC(SYM(ASSUME `exp s % inv(norm y) % (y:real^3) = w'`)) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPEC `s:real` REAL_EXP_POS_LT) THEN UNDISCH_TAC `&0 < norm(y:real^3)` THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[STDS_NECK_DOM_EXP; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `abs s < inv(sqrt(&2) * eps)` MP_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[REAL_ABS_DIV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `inv(sqrt(&2) * eps) * sqrt(&2) * lam = lam / eps` SUBST1_TAC THENL
       [MP_TAC P3S_SQRT2_POS THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC]]);;

(* The profile r -> rinv(D + sqrt 2 lam log r).                              *)

let STDS_PROFILE = prove
 (`!g0 A0 D lam r.
     p3_std_initial g0 A0 /\ &0 < lam /\ &0 < r /\ &0 < D + sqrt(&2) * lam * log r
     ==> ((\r. p3s_rad_rinv g0 (D + sqrt(&2) * lam * log r)) has_real_derivative
          (sqrt(&2) * lam * inv r) *
          inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (D + sqrt(&2) * lam * log r)))))
         (atreal r) /\
         &0 < (sqrt(&2) * lam * inv r) *
              inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (D + sqrt(&2) * lam * log r))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\r. D + sqrt(&2) * lam * log r) has_real_derivative
                 sqrt(&2) * lam * inv r) (atreal r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`log`; `inv r`; `lam:real`; `r:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\r. lam * log r`; `lam * inv r`; `sqrt(&2)`; `r:real`]
                  HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\r:real. (D:real)`; `&0`; `\r. sqrt(&2) * lam * log r`; `sqrt(&2) * lam * inv r`;
                   `atreal r`] HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_LID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(INST [`\s. inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 s)))`,`g':real->real`;
                 `sqrt(&2) * lam * inv r`,`f':real`]
            (ISPECL [`\s:real. &0 < s`; `\r. D + sqrt(&2) * lam * log r`; `p3s_rad_rinv g0`]
                    HAS_REAL_DERIVATIVE_CHAIN)) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P3S_RINV_DERIV THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[P3S_SQRT2_POS] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      REWRITE_TAC[p3s_rad_a] THEN MATCH_MP_TAC P3S_STD_POS THEN EXISTS_TAC `A0:real` THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]]]);;

(* Orthogonal matrices give sphere diffeomorphisms; radial_ext of y -> Q^T y. *)

let STDS_ORTH_SPHERE_DIFFEO = prove
 (`!Q:real^3^3. orthogonal_matrix Q
                ==> sphere_diffeo (\y. transp Q ** y) (\y. Q ** y) /\
                    (!y. radial_ext (\y. transp Q ** y) y = transp Q ** y)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix(transp(Q:real^3^3))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[sphere_diffeo; smooth_near] THEN
    SUBGOAL_THEN `smooth_map_on (:real^3) (\y. transp(Q:real^3^3) ** y) /\
                  smooth_map_on (:real^3) (\y. (Q:real^3^3) ** y)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF; ETA_AX] (ISPECL [`(:real^3)`; `\x:real^3. x`]
                                                         SMOOTH_MAP_ON_LINEAR_O)) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[STDS_ORTH_NORM; MATRIX_VECTOR_MUL_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[TRANSP_TRANSP; MATRIX_VECTOR_MUL_LID];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[radial_ext; MATRIX_VECTOR_MUL_RMUL] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_MUL_RZERO] THEN
    SUBGOAL_THEN `norm(y:real^3) * inv(norm y) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[NORM_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Bounds for Gs on [0,theta] x cball(0,rho), theta < 1,                     *)
(* uniform in t: the metric is equivalent to g0 (SNGL_METRIC_EQUIV_LOCAL,    *)
(* STNC_CORE_QF), R <= 6 K (|Rm| <= K on [0,b), b < 1), and the derivative  *)
(* terms of the cap clauses are bounded by |nabla Rm|, |nabla^2 Rm|          *)
(* (P2C_SCALAR_DERIV_TRACE), jointly continuous (RFA_RMD2_CONTINUOUS_M),     *)
(* and |Ric|^2 <= R^2 (P2BFF_RIC2_LE_SCALAR2, Ric >= 0).                      *)
(* ------------------------------------------------------------------------- *)

let STDS_OSA_LOCAL = prove
 (`!(g:real^3->real^3^3) y.
     metric_local (open_set_atlas (:real^3)) (chart_at (open_set_atlas (:real^3)) y) g = g /\
     SND(chart_at (open_set_atlas (:real^3)) y) y = y`,
  REPEAT GEN_TAC THEN SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; OPEN_UNIV; IN_UNIV]);;

let STDS_RMD_12 = prove
 (`!(G:real^3->real^3^3) y.
     lrm_deriv_norm2 1 G y = ltnorm2 5 G (lnabla 4 G (lrm4 G)) y /\
     lrm_deriv_norm2 2 G y = ltnorm2 6 G (lnabla 5 G (lnabla 4 G (lrm4 G))) y`,
  REWRITE_TAC[lrm_deriv_norm2; num_CONV `2`; num_CONV `1`; lnabla_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* A jointly continuous function on [0,1) x R^3 is bounded above on          *)
(* [0,theta] x cball(0,rho).                                                 *)

let STDS_TS_BOUND = prove
 (`!(f:real#real^3->real) theta rho.
     continuous_map
       (prod_topology (subtopology euclideanreal {t | &0 <= t /\ t < &1})
                      (subtopology euclidean (topspace euclidean)),
        euclideanreal) f /\
     &0 <= theta /\ theta < &1
     ==> ?B. !t y. &0 <= t /\ t <= theta /\ y IN cball(vec 0,rho) ==> f(t,y) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prod_topology (subtopology euclideanreal {t | &0 <= t /\ t < &1})
                                (subtopology euclidean (topspace euclidean:real^3->bool))`;
                 `euclideanreal`; `f:real#real^3->real`;
                 `real_interval[&0,theta] CROSS cball(vec 0:real^3,rho)`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_compact_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]);;

(* The two-sided quadratic-form sandwich.                                    *)

let STDS_QF_SANDWICH = prove
 (`!lam Lam vv q0 q e1 e2 c1 c2.
     &0 <= vv /\ &0 < lam /\ lam * vv <= q0 /\ q0 <= Lam * vv /\
     e1 * q0 <= q /\ q <= e2 * q0 /\ &0 <= c1 /\ c1 <= e1 /\ &0 <= e2 /\ e2 <= c2
     ==> (lam * c1) * vv <= q /\ q <= (Lam * c2) * vv`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e1 * q0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lam * c1) * vv = c1 * (lam * vv)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e2 * q0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Lam * c2) * vv = c2 * (Lam * vv)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * vv` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The uniform bounds.                                                       *)

let STDS_UNIF_BOUNDS = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 theta rho.
           p3_std_initial g0 A0 /\ &0 <= theta /\ theta < &1
           ==> ?m M KR K1 K2.
                 &0 < m /\ &1 <= M /\ &0 <= K1 /\ &0 <= K2 /\
                 !t y. &0 <= t /\ t <= theta /\ norm y <= rho
                       ==> (!v. m * (v dot v) <= v dot (stds_gs g0 t y ** v) /\
                                v dot (stds_gs g0 t y ** v) <= M * (v dot v)) /\
                           mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) y <= KR /\
                           sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) (stds_gs g0 t) y)
                           <= K1 /\
                           abs(rfs_scalar_lap (open_set_atlas (:real^3)) (stds_gs g0 t) y +
                               &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) (stds_gs g0 t) y)
                           <= K2`,
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `theta:real`; `rho:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `stds_gs_hyps` ASSUME_TAC THENL [ASM_MESON_TAC[stds_tm_hyps]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_tm g0 = &1` ASSUME_TAC THENL [ASM_MESON_TAC[STDS_TM_EQ_1]; ALL_TAC] THEN
  ABBREV_TAC `b = (theta + &1) / &2` THEN
  SUBGOAL_THEN `theta < b /\ b < &1 /\ &0 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) (stds_gs g0) /\
                ?K0. !t x. &0 <= t /\ t <= b
                           ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
    ASM_REWRITE_TAC[p3_partial_std] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = max K0 (&0)` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t <= b
                 ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the slices *)
  SUBGOAL_THEN `!t. &0 <= t /\ t <= theta
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t) /\
                        metric_field (:real^3) (stds_gs g0 t) /\
                        (!x u v. ~collinear {vec 0,u,v}
                                 ==> &0 <= mfd_sectional (open_set_atlas (:real^3))
                                                         (stds_gs g0 t) x u v)`
  (LABEL_TAC "sl") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= t /\ t < stds_tm g0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[STDS_GS_RIEM]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[STDS_GS_RIEM]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[stds_tm_hyps]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* metric bounds *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `rho:real`] STNC_CORE_QF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` (X_CHOOSE_THEN `Lam0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qf"))))) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `stds_gs g0`; `&0`; `b:real`; `(:real^3)`; `K:real`]
                SNGL_METRIC_EQUIV_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[DIMINDEX_3; IN_UNIV; REAL_SUB_RZERO] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(LABEL_TAC "eq")] THEN
  (* joint continuity of nabla Rm and nabla^2 Rm *)
  MP_TAC(ISPECL [`\z:real#real^3. rfa_rmd2 1 (open_set_atlas (:real^3))
                                          (stds_gs g0 (FST z)) (SND z)`;
                 `theta:real`; `rho:real`] STDS_TS_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`1`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `&1`;
                   `stds_gs g0`] RFA_RMD2_CONTINUOUS_M) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "b1"))] THEN
  MP_TAC(ISPECL [`\z:real#real^3. rfa_rmd2 2 (open_set_atlas (:real^3))
                                          (stds_gs g0 (FST z)) (SND z)`;
                 `theta:real`; `rho:real`] STDS_TS_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `&1`;
                   `stds_gs g0`] RFA_RMD2_CONTINUOUS_M) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "b2"))] THEN
  MAP_EVERY EXISTS_TAC
   [`lam0 * exp(--(&4 * K))`; `max (&1) (Lam0 * exp(&4 * K))`; `&6 * K`;
    `sqrt(&9 * max B1 (&0))`; `sqrt(&27 * max B2 (&0)) + &2 * (&6 * K) pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + &2 * b`) THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t < b /\ t <= b /\ y IN cball(vec 0:real^3,rho)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) y) <= &6 * K`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_MFD_SCALAR_ABS_3 THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[STDCAP_OSA_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV];
      MATCH_MP_TAC(REAL_ARITH `x <= k ==> &6 * x <= &6 * k`) THEN USE_THEN "rm" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_rmd2 1 (open_set_atlas (:real^3)) (stds_gs g0 t) y <= B1 /\
                rfa_rmd2 2 (open_set_atlas (:real^3)) (stds_gs g0 t) y <= B2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "b1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "b2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. exp(--(&2 * (&2 * K) * t)) * (v dot ((g0:real^3->real^3^3) y ** v)) <=
                    v dot (stds_gs g0 t y ** v) /\
                    v dot (stds_gs g0 t y ** v) <=
                    exp(&2 * (&2 * K) * t) * (v dot (g0 y ** v))`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g = stds_gs g0 t` THEN
  REPEAT CONJ_TAC THENL
   [(* metric bounds *)
    X_GEN_TAC `v:real^3` THEN
    SUBGOAL_THEN `&2 * (&2 * K) * t <= &4 * K` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&4 * K) * t <= (&4 * K) * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `lam0 * (v dot v) <= v dot ((g0:real^3->real^3^3) y ** v) /\
                  v dot (g0 y ** v) <= Lam0 * (v dot v)` STRIP_ASSUME_TAC THENL
     [USE_THEN "qf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(lam0 * exp(--(&4 * K))) * (v dot v) <= v dot ((g:real^3->real^3^3) y ** v) /\
                  v dot (g y ** v) <= (Lam0 * exp(&4 * K)) * (v dot v)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC STDS_QF_SANDWICH THEN
      MAP_EVERY EXISTS_TAC [`v dot ((g0:real^3->real^3^3) y ** v)`;
                            `exp(--(&2 * (&2 * K) * t))`; `exp(&2 * (&2 * K) * t)`] THEN
      ASM_REWRITE_TAC[DOT_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Lam0 * exp(&4 * K)) * ((v:real^3) dot v)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN REAL_ARITH_TAC;
    (* scalar curvature *)
    ASM_REAL_ARITH_TAC;
    (* the gradient *)
    REWRITE_TAC[rfs_scalar_grad2; STDS_OSA_LOCAL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC(ISPECL [`(:real^3)`; `g:real^3->real^3^3`; `y:real^3`] P2C_SCALAR_DERIV_TRACE) THEN
    ASM_REWRITE_TAC[IN_UNIV; DIMINDEX_3; GSYM STDS_RMD_12] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `rfa_rmd2 1 (open_set_atlas (:real^3)) g y <= B1` THEN
    REWRITE_TAC[rfa_rmd2; STDS_OSA_LOCAL] THEN REAL_ARITH_TAC;
    (* the Laplacian term *)
    REWRITE_TAC[rfs_scalar_lap; rfs_ric_norm2; STDS_OSA_LOCAL] THEN
    SUBGOAL_THEN `(\z u. lricci (g:real^3->real^3^3) z (u 1) (u 2)) = lric2 g` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; lric2]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
      `abs a <= A /\ &0 <= b /\ b <= B ==> abs(a + &2 * b) <= A + &2 * B`) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3)`; `g:real^3->real^3^3`; `y:real^3`] P2C_SCALAR_DERIV_TRACE) THEN
      ASM_REWRITE_TAC[IN_UNIV; DIMINDEX_3; GSYM STDS_RMD_12] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `rfa_rmd2 2 (open_set_atlas (:real^3)) g y <= B2` THEN
      REWRITE_TAC[rfa_rmd2; STDS_OSA_LOCAL] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `(:real^3)` THEN
      ASM_SIMP_TAC[LRG_LRIC2_FIELD; IN_UNIV];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lscalar (g:real^3->real^3^3) y pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BFF_RIC2_LE_SCALAR2 THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
        MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `y:real^3`]
                     STDS_GS_SEC_CONSEQ) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
          ASM_MESON_TAC[];
          ASM_REWRITE_TAC[mfd_ricci; STDS_OSA_LOCAL] THEN MESON_TAC[]];
        MP_TAC(ISPECL [`(:real^3)`; `g:real^3->real^3^3`; `y:real^3`] RFB_OPEN_SET_MFD_SCALAR) THEN
        REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_REWRITE_TAC[REAL_ABS_POS]]]]);;

(* ------------------------------------------------------------------------- *)
(* The cap near the tip at a time t < 1 (lam = sqrt(1-t)):                   *)
(* U = ball(0,rinv(D1 + 2 lam/eps)), core ball(0,rinv D1), outer neck the    *)
(* map emap z lam with d0(z) = D1 + lam/eps (image exactly the shell between *)
(* the two balls), inner neck emap z' lam with d0(z') = D1, sphere map       *)
(* transp(stds_rot z'), profile rinv(D1 + sqrt 2 lam log r); STDCAP_CAP.     *)
(* ------------------------------------------------------------------------- *)

let STDS_RINV_MONO_LE = prove
 (`!g0 A0 a b. p3_std_initial g0 A0 /\ &0 <= a /\ a <= b
               ==> p3s_rad_rinv g0 a <= p3s_rad_rinv g0 b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `a:real`] P3S_RINV) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `b:real`] P3S_RINV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 a`; `p3s_rad_rinv g0 b`]
               P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let STDS_AXIS_POINT = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> p3_std_dist g0 (p3s_rad_rinv g0 s % basis 1:real^3) = s /\
                 ~(p3s_rad_rinv g0 s % basis 1:real^3 = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_POS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`;
                  `p3s_rad_rinv g0 s % basis 1:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`];
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH; REAL_LT_IMP_NZ]]);;

let STDS_PROFILE_ARG_POS = prove
 (`!D lam r. &0 < lam /\ lam <= &1 /\ &1 / &4 < r /\ r < &2 /\ &6 < D
             ==> &0 < D + sqrt(&2) * lam * log r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&4) < log r` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r /\ inv r < &4` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `inv r` LOG_LT_X) THEN ASM_SIMP_TAC[REAL_LT_INV; LOG_INV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= log r` THENL
   [SUBGOAL_THEN `&0 <= sqrt(&2) * lam * log r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - lam) * --log r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * (lam * log r + &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The near cap.                                                             *)

let STDS_NEAR_CAP = prove
 (`?epsc. &0 < epsc /\ epsc <= &1 / &4 /\
     !g0 A0 (g:real^3->real^3^3) t eps D1 eta etas alpha m M cR KR K1 K2 rho3.
       p3_std_initial g0 A0 /\ riemannian_metric (open_set_atlas (:real^3)) g /\
       metric_field (:real^3) g /\ &0 <= t /\ t < &1 /\ &0 < eps /\ eps <= epsc /\
       A0 + &4 / eps + &8 <= D1 /\
       (!z w. D1 <= p3_std_dist g0 z /\
              w IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
                   ball(vec 0,exp(--(inv(sqrt(&2) * eps))))
              ==> lck_dist2 (rfs_kreg eps) (cylinder_flow t)
                            (mpullback (stds_nmap g0 A0 z) g) w < eta) /\
       &0 < eta /\ &2 pow (rfs_kreg eps) * eta < etas pow 2 /\
       &2 pow (rfs_kreg eps) * eta <= (eps / &4) pow 2 /\
       &0 < alpha /\ alpha <= eps / &8 /\
       (!S (G':real^3->real^3^3) y.
          open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G' /\ y IN S /\
          lck_dist2 2 (cylinder_flow (&0)) G' y < etas pow 2
          ==> abs(lscalar G' y - &1) <= alpha) /\
       &0 < m /\ &1 <= M /\ &0 < cR /\ &0 <= K1 /\ &0 <= K2 /\
       p3s_rad_rinv g0 (D1 + &2 / eps) + inv(sqrt cR) <= rho3 /\
       (!y v. y IN ball(vec 0,rho3)
              ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
       (!y. y IN ball(vec 0,rho3)
            ==> cR <= mfd_scalar (open_set_atlas (:real^3)) g y /\
                mfd_scalar (open_set_atlas (:real^3)) g y <= KR) /\
       (!y. y IN ball(vec 0,p3s_rad_rinv g0 (D1 + &2 / eps))
            ==> sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) g y) <= K1 /\
                abs(rfs_scalar_lap (open_set_atlas (:real^3)) g y +
                    &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) g y) <= K2)
       ==> rfs_cap (euclidean,open_set_atlas (:real^3)) g
             (stdcap_const m M cR KR K1 K2 (p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps)))
             eps (ball(vec 0,p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps)))
             (ball(vec 0,p3s_rad_rinv g0 D1))`,
  MP_TAC STDCAP_CAP THEN
  DISCH_THEN(X_CHOOSE_THEN `epsc0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap"))) THEN
  EXISTS_TAC `min epsc0 (&1 / &4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= epsc0 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  ABBREV_TAC `lam = sqrt(&1 - t)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam / eps /\ lam / eps <= &1 / eps /\ &0 < &1 / eps /\
                &4 / eps = &4 * (&1 / eps) /\ &2 / eps = &2 * (&1 / eps)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the centres of the two necks *)
  ABBREV_TAC `z' = p3s_rad_rinv g0 D1 % basis 1:real^3` THEN
  ABBREV_TAC `z = p3s_rad_rinv g0 (D1 + lam / eps) % basis 1:real^3` THEN
  SUBGOAL_THEN `p3_std_dist g0 z' = D1 /\ ~(z':real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN MATCH_MP_TAC STDS_AXIS_POINT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 z = D1 + lam / eps /\ ~(z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC STDS_AXIS_POINT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the necks at time t *)
  SUBGOAL_THEN `!w:real^3. D1 <= p3_std_dist g0 w
                ==> rfs_neck (euclidean,open_set_atlas (:real^3)) g eps w
                             (stds_emap g0 A0 w lam)`
  (LABEL_TAC "neck") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `g:real^3->real^3^3`; `w:real^3`; `t:real`;
                  `eps:real`; `eta:real`; `etas:real`; `alpha:real`] STDS_TIME_NECK_GEOM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `w':real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the outer neck covers the shell between the balls *)
  SUBGOAL_THEN `IMAGE (stds_emap g0 A0 z lam) (rfs_neck_dom eps) =
                annulus (p3s_rad_rinv g0 D1) (p3s_rad_rinv g0 (D1 + &2 * lam / eps))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`; `lam:real`; `eps:real`]
                 STDS_EMAP_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `D1:real`; `D1 + &2 * lam / eps`]
                 STDS_DIST_ANNULUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (stds_emap g0 A0 z' lam) (rfs_neck_dom eps) SUBSET
                ball(vec 0,p3s_rad_rinv g0 (D1 + &2 * lam / eps))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z':real^3`; `lam:real`; `eps:real`]
                 STDS_EMAP_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `D1 + &2 * lam / eps`] STDS_DIST_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the sphere map and the radial form of the inner neck *)
  MP_TAC(SPEC `z':real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `stds_rot z'` STDS_ORTH_SPHERE_DIFFEO) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &4) (&2)
        ==> stds_emap g0 A0 z' lam (radial_ext (\y. transp (stds_rot z') ** y) y) =
            (p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log(norm y)) / norm y) % y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `orthogonal_matrix(transp(stds_rot z')) /\
                  norm(transp(stds_rot z') ** y) = norm(y:real^3) /\
                  stds_rot z' ** (transp(stds_rot z') ** y) = y` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP; STDS_ORTH_NORM] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      UNDISCH_TAC `orthogonal_matrix(stds_rot z')` THEN
      SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(transp(stds_rot z') ** (y:real^3) = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN
      SUBGOAL_THEN `norm(transp(stds_rot z') ** (y:real^3)) = norm y` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z':real^3`; `lam:real`;
                  `transp(stds_rot z') ** (y:real^3)`] STDS_EMAP_RADIAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* monotonicity of the radii *)
  SUBGOAL_THEN `p3s_rad_rinv g0 (D1 + &2 * lam / eps) <= p3s_rad_rinv g0 (D1 + &2 / eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_RINV_MONO_LE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(vec 0,p3s_rad_rinv g0 (D1 + &2 * lam / eps))
        ==> sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) g y) <= K1 /\
            abs(rfs_scalar_lap (open_set_atlas (:real^3)) g y +
                &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) g y) <= K2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the profile *)
  SUBGOAL_THEN
   `!r. &1 / &4 < r /\ r < &2
        ==> ((\r. p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log r)) has_real_derivative
             (sqrt(&2) * lam * inv r) *
             inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log r)))))
            (atreal r) /\
            &0 < (sqrt(&2) * lam * inv r) *
                 inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log r))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC STDS_PROFILE THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC STDS_PROFILE_ARG_POS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log(&1 / &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDS_PROFILE_ARG_POS THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* STDCAP_CAP *)
  USE_THEN "cap" (MP_TAC o SPECL
   [`g:real^3->real^3^3`; `eps:real`;
    `\r. p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log r)`;
    `\r. (sqrt(&2) * lam * inv r) *
         inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (D1 + sqrt(&2) * lam * log r))))`;
    `z:real^3`; `stds_emap g0 A0 z lam`; `z':real^3`; `stds_emap g0 A0 z' lam`;
    `\y:real^3. transp(stds_rot z') ** y`; `\y:real^3. stds_rot z' ** y`;
    `p3s_rad_rinv g0 (D1 + &2 * lam / eps)`; `rho3:real`; `m:real`; `M:real`; `cR:real`;
    `KR:real`; `K1:real`; `K2:real`]) THEN
  BETA_TAC THEN REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(USE_THEN "neck" MATCH_MP_TAC) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MT Thm 12.32 (the last clause of P2C_STD_PROPS_STATEMENT) for Gs.  R >=   *)
(* r^-2: Thm 12.28 (cap or (1+eps)-neck); R < r^-2: t <= theta by Prop       *)
(* 12.31, then the near cap (d0(x) < D1) or the far evolving neck back to    *)
(* time 0 (d0(x) >= D1), with the closeness of STDS_ASYM_CLOSE on [0,theta]  *)
(* and the uniform bounds of STDS_UNIF_BOUNDS; C' = max(C0,                  *)
(* stdcap_const(..., rinv(D1 + 2/eps))).                                     *)
(* ------------------------------------------------------------------------- *)

let STDS_CAP_CONST_MONO = prove
 (`!m M cR KR K1 K2 r1 r2.
     &0 < m /\ &1 <= M /\ &0 < cR /\ &0 <= KR /\ &0 <= K1 /\ &0 <= K2 /\
     &0 <= r1 /\ r1 <= r2
     ==> &1 < stdcap_const m M cR KR K1 K2 r1 /\
         stdcap_const m M cR KR K1 K2 r1 <= stdcap_const m M cR KR K1 K2 r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt M /\ &0 <= sqrt KR /\ &0 < sqrt m /\ &0 < sqrt cR /\ &0 < pi`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POS_LT; PI_POS; REAL_ARITH `&1 <= M ==> &0 <= M`];
    ALL_TAC] THEN
  ABBREV_TAC `a = sqrt M * sqrt KR` THEN
  ABBREV_TAC `b = M * sqrt M * (&4 / &3 * pi) * KR * sqrt KR` THEN
  ABBREV_TAC `E = &2 + KR / cR + (M * sqrt M) / (m * sqrt m * (&4 / &3 * pi)) +
                  K1 / (cR * sqrt cR) + K2 / cR pow 2` THEN
  SUBGOAL_THEN `!r. stdcap_const m M cR KR K1 K2 r = E + &2 * r * a + b * r pow 3`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[stdcap_const] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"; "E"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b /\ &2 <= E` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "b" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "E" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= d
                               ==> &2 <= &2 + a + b + c + d`) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REPEAT CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r1 * a /\ r1 * a <= r2 * a /\ &0 <= b * r1 pow 3 /\
                b * r1 pow 3 <= b * r2 pow 3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The small parameter eta of the closeness conditions.                      *)

let STDS_ETA_CHOICE = prove
 (`!k eps etas. &0 < eps /\ &0 < etas
     ==> ?eta. &0 < eta /\ &3 pow k * eta <= (eps / &8) pow 2 /\
               &2 pow k * eta < etas pow 2 /\ &2 pow k * eta <= (eps / &4) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &3 pow k /\ &0 < &2 pow k /\ &0 < (eps / &8) pow 2 /\ &0 < etas pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min ((eps / &8) pow 2 / &3 pow k) (etas pow 2 / (&2 * &2 pow k))` THEN
  ABBREV_TAC `eta = min ((eps / &8) pow 2 / &3 pow k) (etas pow 2 / (&2 * &2 pow k))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= (eps / &8) pow 2 / &3 pow k /\
                eta <= etas pow 2 / (&2 * &2 pow k)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 pow k * eta <= (eps / &8) pow 2 /\ &2 pow k * eta <= etas pow 2 / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 pow k * ((eps / &8) pow 2 / &3 pow k)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &3 pow k` THEN
        CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 pow k * (etas pow 2 / (&2 * &2 pow k))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &2 pow k` THEN
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow k * eta` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps / &8) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

(* MT Thm 12.32 for the standard flow Gs.                                    *)

let STDS_P6 = prove
 (`!d:real^4->bool.
     stds_tm_hyps d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3)
     ==> ?eps0. &0 < eps0 /\
           !g0 A0 eps.
             p3_std_initial g0 A0 /\ &0 < eps /\ eps <= eps0
             ==> ?C'. &1 < C' /\
                   !x t. &0 < t /\ t < &1
                     ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t)
                                        C' eps U Y /\ x IN Y) \/
                         (?e. rfs_evolving_neck
                                (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                               {s | &0 <= s /\ s < &1} (stds_gs g0))
                                eps x t
                                (t * mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x) e /\
                              !z. z IN IMAGE e (rfs_neck_dom eps)
                                  ==> A0 + &5 <= p3_std_dist g0 z) \/
                         (?e. rfs_evolving_neck
                                (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                               {s | &0 <= s /\ s < &1} (stds_gs g0))
                                eps x t (&1 + eps) e)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_gs_hyps /\ P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\
                P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
                P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[stds_tm_hyps; stds_gs_hyps]; ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_THM_12_28) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[stds_tm_hyps]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1228"))) THEN
  X_CHOOSE_THEN `epsc:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) STDS_NEAR_CAP THEN
  EXISTS_TAC `min eps1 epsc` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `eps:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= epsc /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `eps <= min eps1 epsc` (K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_A0_POS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the flow Gs *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_tm g0 = &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_partial_std g0 (&1) (stds_gs g0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < &1
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 s) /\
                        metric_field (:real^3) (stds_gs g0 s)` (LABEL_TAC "riem") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC STDS_GS_RIEM THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Thm 12.28 at eps *)
  USE_THEN "T1228" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPECL [`C0:real`; `g0:real^3->real^3^3`; `A0:real`]))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "can"))) THEN
  (* P5 *)
  MP_TAC(SPEC `d:real^4->bool` STDS_PROP_12_31) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p5"))) THEN
  ABBREV_TAC `theta = max (&1 / &2) (&1 - c * r pow 2)` THEN
  SUBGOAL_THEN `&1 / &2 <= theta /\ theta < &1 /\ &1 - c * r pow 2 <= theta`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "theta" THEN SUBGOAL_THEN `&0 < c * r pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_THEN `max (&1 / &2) (&1 - c * r pow 2) = theta` (K ALL_TAC) THEN
  (* the curvature-stability and closeness parameters *)
  ABBREV_TAC `k = rfs_kreg eps` THEN
  ABBREV_TAC `alpha = min (eps / &16) (inv(&2 * &(k + 2)))` THEN
  SUBGOAL_THEN `&0 < alpha /\ alpha <= eps / &16 /\ alpha <= eps / &8 /\
                &(k + 2) * alpha <= &1 / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &(k + 2)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "alpha" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "alpha" THEN REAL_ARITH_TAC;
      EXPAND_TAC "alpha" THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(k + 2) * inv(&2 * &(k + 2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; EXPAND_TAC "alpha" THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &(k + 2)` THEN
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  UNDISCH_THEN `min (eps / &16) (inv(&2 * &(k + 2))) = alpha` (K ALL_TAC) THEN
  MP_TAC(SPEC `alpha:real` P2BN_CYL_SCALAR_STAB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `etas:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab0"))) THEN
  SUBGOAL_THEN
   `!S (G':real^3->real^3^3) y.
      open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G' /\ y IN S /\
      lck_dist2 2 (cylinder_flow (&0)) G' y < etas pow 2
      ==> abs(lscalar G' y - &1) <= alpha` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "stab0" (MP_TAC o SPECL [`&0`; `S:real^3->bool`; `G':real^3->real^3^3`;
                                     `y:real^3`]) THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `eps:real`; `etas:real`] STDS_ETA_CHOICE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  (* the asymptotic closeness on [0,theta] *)
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&1`; `stds_gs g0`; `theta:real`;
                 `cball(vec 0:real^3,exp(&2 * inv(sqrt(&2) * eps))) DIFF
                  ball(vec 0,exp(--(&2 * inv(sqrt(&2) * eps))))`;
                 `k:num`; `eta:real`] STDS_ASYM_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      MATCH_MP_TAC STDS_CANNULUS_SUBSET THEN REWRITE_TAC[REAL_EXP_POS_LT]];
    DISCH_THEN(X_CHOOSE_THEN `A1:real` (LABEL_TAC "asym"))] THEN
  (* the cap parameters and the uniform bounds *)
  ABBREV_TAC `D1 = max (A1 + &1) (A0 + &4 / eps + &8)` THEN
  ABBREV_TAC `rho3 = p3s_rad_rinv g0 (D1 + &2 / eps) + inv(sqrt c)` THEN
  SUBGOAL_THEN `A1 < D1 /\ A0 + &4 / eps + &8 <= D1 /\ &0 < &1 / eps /\
                &4 / eps <= &4 * (&1 / eps) /\ &4 * (&1 / eps) <= &4 / eps /\
                &2 / eps <= &2 * (&1 / eps) /\ &2 * (&1 / eps) <= &2 / eps`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `max (A1 + &1) (A0 + &4 / eps + &8) = D1` (K ALL_TAC) THEN
  SUBGOAL_THEN `&0 <= p3s_rad_rinv g0 (D1 + &2 / eps) /\ &0 < inv(sqrt c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `D1 + &2 / eps`] P3S_RINV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_UNIF_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `theta:real`; `rho3:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `KR:real`
    (X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `K2:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ub")))))))))) THEN
  SUBGOAL_THEN `&0 <= KR` ASSUME_TAC THENL
   [USE_THEN "ub" (MP_TAC o SPECL [`&0`; `vec 0:real^3`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "p5" (MP_TAC o SPECL [`vec 0:real^3`; `&0`]) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; REAL_SUB_RZERO; REAL_DIV_1] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `max C0 (stdcap_const m M c KR K1 K2 (p3s_rad_rinv g0 (D1 + &2 / eps)))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `inv(r pow 2) <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x` THENL
   [(* the canonical neighbourhoods of Thm 12.28 *)
    USE_THEN "can" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `C0:real`; `eps:real`; `&1 + eps`; `x:real^3`;
                  `t:real`] STDS_CANON_L_GV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[stds_gv] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `Y:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN
      MAP_EVERY EXISTS_TAC [`C0:real`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* low curvature: t <= theta *)
  SUBGOAL_THEN `t <= theta` ASSUME_TAC THENL
   [SUBGOAL_THEN `c / (&1 - t) < inv(r pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x` THEN
      CONJ_TAC THENL [USE_THEN "p5" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - t /\ &0 < r pow 2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `inv(r pow 2) * (&1 - t) = (&1 - t) / r pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "riem" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `p3_std_dist g0 x < D1` THENL
   [(* the cap near the tip *)
    DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`ball(vec 0:real^3,p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps))`;
      `ball(vec 0:real^3,p3s_rad_rinv g0 D1)`] THEN
    SUBGOAL_THEN `(x:real^3) IN ball(vec 0,p3s_rad_rinv g0 D1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `D1:real`; `x:real^3`]
                   STDS_DIST_RINV) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps) <=
                  p3s_rad_rinv g0 (D1 + &2 / eps) /\
                  &0 <= p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= sqrt(&1 - t) / eps /\ sqrt(&1 - t) / eps <= &1 / eps`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE] THEN
          MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC STDS_RINV_MONO_LE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `D1 + &2 * sqrt(&1 - t) / eps`]
                     P3S_RINV) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN
    MAP_EVERY EXISTS_TAC
     [`stdcap_const m M c KR K1 K2 (p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps))`;
      `x:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m:real`; `M:real`; `c:real`; `KR:real`; `K1:real`; `K2:real`;
                  `p3s_rad_rinv g0 (D1 + &2 * sqrt(&1 - t) / eps)`;
                  `p3s_rad_rinv g0 (D1 + &2 / eps)`] STDS_CAP_CONST_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z w. D1 <= p3_std_dist g0 z /\
            w IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
                 ball(vec 0,exp(--(inv(sqrt(&2) * eps))))
            ==> lck_dist2 k (cylinder_flow t)
                  (mpullback (stds_nmap g0 A0 z) (stds_gs g0 t)) w < eta`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
      USE_THEN "asym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN cball(vec 0,exp(inv(sqrt(&2) * eps))) DIFF
                                 ball(vec 0,exp(--(inv(sqrt(&2) * eps))))` THEN
      SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[P3S_SQRT2_POS];
        ALL_TAC] THEN
      SPEC_TAC(`inv(sqrt(&2) * eps)`,`cc:real`) THEN GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `exp cc <= exp(&2 * cc) /\ exp(--(&2 * cc)) <= exp(--cc)` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p3s_rad_rinv g0 (D1 + &2 / eps) + inv(sqrt c) <= rho3` ASSUME_TAC THENL
     [EXPAND_TAC "rho3" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!y v. y IN ball(vec 0,rho3)
            ==> m * (v dot v) <= v dot (stds_gs g0 t y ** v) /\
                v dot (stds_gs g0 t y ** v) <= M * (v dot v)` ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN REWRITE_TAC[IN_BALL_0] THEN
      DISCH_TAC THEN USE_THEN "ub" (MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN ball(vec 0,rho3)
          ==> c <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) y /\
              mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) y <= KR` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      USE_THEN "ub" (MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / (&1 - t)` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        SUBGOAL_THEN `&0 <= c * t` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
        USE_THEN "p5" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN ball(vec 0,p3s_rad_rinv g0 (D1 + &2 / eps))
          ==> sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) (stds_gs g0 t) y) <= K1 /\
              abs(rfs_scalar_lap (open_set_atlas (:real^3)) (stds_gs g0 t) y +
                  &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) (stds_gs g0 t) y) <= K2`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      USE_THEN "ub" (MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "near" (MP_TAC o SPECL
     [`g0:real^3->real^3^3`; `A0:real`; `stds_gs g0 t`; `t:real`; `eps:real`; `D1:real`;
      `eta:real`; `etas:real`; `alpha:real`; `m:real`; `M:real`; `c:real`; `KR:real`;
      `K1:real`; `K2:real`; `rho3:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the evolving neck far out *)
  SUBGOAL_THEN `!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) (stds_gs g0 s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "riem" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &5 + &2 / eps <= p3_std_dist g0 x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s w. &0 <= s /\ s <= t /\
          w IN cball(vec 0,exp(&2 * inv(sqrt(&2) * eps))) DIFF
               ball(vec 0,exp(--(&2 * inv(sqrt(&2) * eps))))
          ==> lck_dist2 k (cylinder_flow s)
                (mpullback (stds_nmap g0 A0 x) (stds_gs g0 s)) w < eta` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "asym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MATCH_MP_TAC STDS_FAR_EVNECK THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `etas:real`; `alpha:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The route form of P2C_STD_PROPS.  Witness Gs = stds_gs g0 (Tm = 1); every *)
(* G that agrees with Gs on [0,1) inherits the clauses P1-P6 of              *)
(* P2C_STD_PROPS_STATEMENT: complete slices with sec > 0 (STDS_GS_BASICS,    *)
(* STDS_GS_SEC_POS), SO(3) invariance (stds_rotm), the far necks and         *)
(* cylinder asymptotics (STDS_ASYM_P3, STDS_ASYM_P4), P5 (STDS_PROP_12_31)   *)
(* and P6 (STDS_P6 with STDS_EVNECK_CONG).  The noncollapsing input          *)
(* P2C_STD_NONCOLL_STATEMENT is STNC_STD_NONCOLL.                            *)
(* ------------------------------------------------------------------------- *)

let STDS_CLOSE_FAM_CONG = prove
 (`!k eps J s (G0:real->real^3->real^3^3) G1 G2.
     (!t. t IN J ==> G1 t = G2 t) /\ rfs_close_fam k eps J s G0 G1
     ==> rfs_close_fam k eps J s G0 G2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_close_fam] THEN STRIP_TAC THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G2:real->real^3->real^3^3) t = G1 t` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let STDS_PROPS = prove
 (`!d:real^4->bool.
     stds_tm_hyps d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3) ==> P2C_STD_PROPS_STATEMENT`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_gs_hyps /\ P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\
                P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
                P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
                P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_STD_UNIQUE_STATEMENT`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[stds_tm_hyps; stds_gs_hyps]; ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_P6) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p6"))) THEN
  REWRITE_TAC[P2C_STD_PROPS_STATEMENT] THEN EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  EXISTS_TAC `stds_gs g0` THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_tm g0 = &1` ASSUME_TAC THENL [ASM_MESON_TAC[STDS_TM_EQ_1]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_partial_std g0 (&1) (stds_gs g0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < &1
                    ==> stds_rotm (stds_gs g0 t) /\
                        mfd_complete (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t)`
  (LABEL_TAC "rot") THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* agreement on [0,1) gives equal slices *)
  SUBGOAL_THEN `!G:real->real^3->real^3^3.
                  (!t x. &0 <= t /\ t < &1 ==> G t x = stds_gs g0 t x)
                  ==> !t. &0 <= t /\ t < &1 ==> G t = stds_gs g0 t` (LABEL_TAC "agree") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^3` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the maximal flow on [0,1) *)
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_FLOW) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    (* P1, P2, P3 *)
    X_GEN_TAC `G:real->real^3->real^3^3` THEN DISCH_TAC THEN
    USE_THEN "agree" (MP_TAC o SPEC `G:real->real^3->real^3^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "eqG")] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "eqG" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "rot" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        REPEAT STRIP_TAC THEN
        MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_POS) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[stds_tm_hyps]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `Q:real^3^3`; `x:real^3`] THEN STRIP_TAC THEN
      USE_THEN "eqG" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "rot" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[stds_rotm] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t0:real`; `eps:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&1`; `stds_gs g0`; `t0:real`;
                     `eps:real`] STDS_ASYM_P3) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `X:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `X:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC STDS_CLOSE_FAM_CONG THEN
      EXISTS_TAC `\s y. rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3)
                                     (stds_gs g0 s) y` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "eqG" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    (* P4 *)
    MAP_EVERY X_GEN_TAC [`Tp:real`; `eps:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&1`; `stds_gs g0`; `Tp:real`;
                   `eps:real`] STDS_ASYM_P4) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p4"))) THEN
    EXISTS_TAC `A1:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`] THEN STRIP_TAC THEN
    USE_THEN "agree" (MP_TAC o SPEC `G:real->real^3->real^3^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "p4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* P5 *)
    MP_TAC(SPEC `d:real^4->bool` STDS_PROP_12_31) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p5"))) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`] THEN STRIP_TAC THEN
    USE_THEN "agree" (MP_TAC o SPEC `G:real->real^3->real^3^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "p5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* P6 *)
    X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
    USE_THEN "p6" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C':real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c6"))) THEN
    EXISTS_TAC `C':real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `x:real^3`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!s y. &0 <= s /\ s < &1 ==> stds_gs g0 s y = (G:real->real^3->real^3^3) s y`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real->real^3->real^3^3) t = stds_gs g0 t` SUBST1_TAC THENL
     [USE_THEN "agree" (MP_TAC o SPEC `G:real->real^3->real^3^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "c6" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `Y:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC STDS_EVNECK_CONG THEN EXISTS_TAC `stds_gs g0` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e:real^3->real^3` THEN
      MATCH_MP_TAC STDS_EVNECK_CONG THEN EXISTS_TAC `stds_gs g0` THEN ASM_REWRITE_TAC[]]]);;

(* The main theorem: the route form P2C_STD_PROPS_ROUTE_STATEMENT.           *)

let STDS_PROPS_ROUTE = prove
 (`!d:real^4->bool. P2C_STD_PROPS_ROUTE_STATEMENT d`,
  GEN_TAC THEN REWRITE_TAC[P2C_STD_PROPS_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC STDS_PROPS THEN EXISTS_TAC `d:real^4->bool` THEN
  ASM_REWRITE_TAC[stds_tm_hyps; stds_gs_hyps; STNC_STD_NONCOLL]);;

