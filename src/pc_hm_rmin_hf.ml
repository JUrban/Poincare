(* ========================================================================= *)
(* Hole filling for G-energy minimizers from planar domains into S (part of  *)
(* pc_hm_reg_min): the competitor Pg o (Poisson extension on a good circle,  *)
(* glued with the variable-radius mollification hmrm_vr on the annulus, u    *)
(* outside), the energy comparison E(ball(b,R/16)) <= Ch E(annulus(R/16,R))  *)
(* on balls of small energy, and the resulting power decay of the energy.    *)
(* ========================================================================= *)

needs "src/pc_hm_rmin_fv.ml";;
needs "src/pc_hm_rmin_vr.ml";;
needs "src/pc_wan_lap2e.ml";;

prioritize_real();;
type_invention_error := true;;

(* The energy of the minimizer u (weak partials on its domain s) on A.      *)

let hmrm_en = new_definition
 `hmrm_en (s:real^2->bool) (u:real^2->real^K) (A:real^2->bool) =
    drop(integral A (\x. lift(norm(wan_wd s 1 u x) pow 2 + norm(wan_wd s 2 u x) pow 2)))`;;

(* ========================================================================= *)
(* Elementary facts on hmrm_en, the Dirichlet integral of maps equal on a    *)
(* set, and the global W^{1,2} membership of the variable-radius             *)
(* mollification when the h-balls stay in a compact subset of the domain.    *)
(* ========================================================================= *)

let HMRM_EN_DENS = prove
 (`!(s:real^2->bool) (u:real^2->real^K) A.
     wan_w12 s u /\ lebesgue_measurable A /\ A SUBSET s
     ==> (\x. lift(norm(wan_wd s 1 u x) pow 2 + norm(wan_wd s 2 u x) pow 2))
         absolutely_integrable_on A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 ==> wan_wd s i (u:real^2->real^K) IN lspace A (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[GSYM drop; LIFT_DROP] THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2]];
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[ARITH; ETA_AX]]);;

let HMRM_EN_POS = prove
 (`!(s:real^2->bool) (u:real^2->real^K) A.
     wan_w12 s u /\ lebesgue_measurable A /\ A SUBSET s ==> &0 <= hmrm_en s u A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_en] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[HMRM_EN_DENS; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SIMP_TAC[LIFT_DROP; REAL_LE_ADD; REAL_LE_POW_2]);;

let HMRM_EN_MONO = prove
 (`!(s:real^2->bool) (u:real^2->real^K) A A'.
     wan_w12 s u /\ lebesgue_measurable A /\ lebesgue_measurable A' /\
     A SUBSET A' /\ A' SUBSET s
     ==> hmrm_en s u A <= hmrm_en s u A'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_en] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN MATCH_MP_TAC HMRM_EN_DENS THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN MATCH_MP_TAC HMRM_EN_DENS THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[LIFT_DROP; REAL_LE_ADD; REAL_LE_POW_2]]);;

let HMRM_EN_UNION = prove
 (`!(s:real^2->bool) (u:real^2->real^K) A A'.
     wan_w12 s u /\ lebesgue_measurable A /\ lebesgue_measurable A' /\
     A SUBSET s /\ A' SUBSET s /\ negligible(A INTER A')
     ==> hmrm_en s u (A UNION A') = hmrm_en s u A + hmrm_en s u A'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_en; GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN MATCH_MP_TAC HMRM_EN_DENS THEN
  ASM_REWRITE_TAC[]);;

let HMRM_EN_DIR = prove
 (`!(s:real^2->bool) (u:real^2->real^K) t.
     open t /\ t SUBSET s /\ wan_w12 s u ==> hmrm_en s u t = wan_dir t u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_en] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC HMRM_DIR_RESTRICT THEN ASM_REWRITE_TAC[]);;

let HMRM_DIR_EQ_ON = prove
 (`!(t:real^N->bool) (u:real^N->real^K) u'.
     (!x. x IN t ==> u x = u' x) ==> wan_dir t u = wan_dir t u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`; `u':real^N->real^K`]
                CMT_WAN_WD_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* The mollification M = hmrm_vr h u0 is W^{1,2} on the whole domain s when *)
(* every closed h-ball with h > 0 lies in a compact subset k of s: near k   *)
(* by HMRM_VR_W12_LOC, and M - u is compactly supported in a neighbourhood  *)
(* of k (zero extension of a W_0 map).                                       *)

let HMRM_VR_W12_GLOBAL = prove
 (`!(s:real^2->bool) (u:real^2->real^K) (h:real^2->real) k.
     open s /\ wan_w12 s u /\ compact k /\ k SUBSET s /\
     smooth_map_on (:real^2) (\x. lift(h x)) /\ (!x. &0 <= h x) /\
     (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2) /\
     (!x. &0 < h x ==> cball(x,h x) SUBSET k)
     ==> wan_w12 s (hmrm_vr h (\x. if x IN s then u x else vec 0))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `Cv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC")) HMRM_VR_W12_LOC THEN
  ABBREV_TAC `u0 = \x:real^2. if x IN s then (u:real^2->real^K) x else vec 0` THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `k:real^2->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
  ABBREV_TAC `K2 = {x + y:real^2 | x IN k /\ y IN cball(vec 0,dd)}` THEN
  ABBREV_TAC `U = {x + y:real^2 | x IN k /\ y IN ball(vec 0,dd)}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~(x IN k) ==> (h:real^2->real) x = &0` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= h /\ ~(&0 < h) ==> h = &0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:real^2) IN k)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^2) IN c ==> c SUBSET k ==> x IN k`) THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 U (hmrm_vr h (u0:real^2->real^K))` ASSUME_TAC THENL
   [USE_THEN "LOC" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real`;
                                    `K2:real^2->bool`; `U:real^2->bool`; `K2:real^2->bool`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_REFL] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,h x)` THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `k:real^2->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN EXPAND_TAC "u0" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 U (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = \x. hmrm_vr h (u0:real^2->real^K) x - (u:real^2->real^K) x` THEN
  SUBGOAL_THEN `wan_w120 U (D:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[HMRM_VR_ZERO] THEN EXPAND_TAC "u0" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN s` (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `D:real^2->real^K`] WAN_W120_ZERO_EXT) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  ABBREV_TAC `Dz = \x. if x IN U then (D:real^2->real^K) x else vec 0` THEN
  SUBGOAL_THEN `wan_w12 (:real^2) (Dz:real^2->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12; DIMINDEX_2] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `\x. if x IN U then wan_wd U i (D:real^2->real^K) x else vec 0` THEN
    ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`] THEN
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `i:num`; `D:real^2->real^K`] WAN_WD_WORKS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_2] THEN ASM_MESON_TAC[wan_w120]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\x. (u:real^2->real^K) x + Dz x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\x. (u:real^2->real^K) x + Dz x`;
                 `hmrm_vr h (u0:real^2->real^K)`] CMT_WAN_W12_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["Dz"; "D"] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^2) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_VR_ZERO] THEN EXPAND_TAC "u0" THEN ASM_REWRITE_TAC[VECTOR_ADD_RID]);;

(* ========================================================================= *)
(* A good circle.  For a continuous nonnegative density g and the annulus    *)
(* r1 < |x - b| < 2 r1 there is a radius rho in (r1,2 r1) with               *)
(*   rho^2 int_0^2pi g(circ(b,rho,t)) dt <= 2 int_annulus g                 *)
(* (polar coordinates WAN_POLAR_ANNULUS and a strict mean value argument).  *)
(* ========================================================================= *)

let HMRM_ANNULUS_EQ = prove
 (`!(b:real^2) r1 r2.
     {x | r1 < norm(x - b) /\ norm(x - b) < r2} = ball(b,r2) DIFF cball(b,r1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC);;

let HMRM_GOOD_RADIUS = prove
 (`!(g:real^2->real) b r1.
     (\x. lift(g x)) continuous_on (:real^2) /\ (!x. &0 <= g x) /\ &0 < r1
     ==> ?rho. r1 < rho /\ rho < &2 * r1 /\
               rho pow 2 *
               drop(integral (interval[vec 0,lift(&2 * pi)])
                      (\t. lift(g(wan_circ b rho (drop t))))) <=
               &2 * drop(integral {x | r1 < norm(x - b) /\ norm(x - b) < &2 * r1}
                           (\x. lift(g x)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {x:real^2 | r1 < norm(x - b) /\ norm(x - b) < &2 * r1}` THEN
  SUBGOAL_THEN `(\x. lift((g:real^2->real) x)) absolutely_integrable_on A` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `cball(b:real^2,&2 * r1)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^2)`; `\x. lift((g:real^2->real) x)`] WAN_CONTINUOUS_LLOC) THEN
      ASM_REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[COMPACT_CBALL; SUBSET_UNIV];
      ALL_TAC] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[HMRM_ANNULUS_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^2->bool) SUBSET t ==> s DIFF u SUBSET t`) THEN
      REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
      SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((g:real^2->real) x)`; `b:real^2`; `&0`; `r1:real`; `&2 * r1`]
                WAN_POLAR_ANNULUS) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D = drop(integral A (\x. lift((g:real^2->real) x)))` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "NEG" o REWRITE_RULE
    [NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; REAL_NOT_LE]) THEN
  ABBREV_TAC
   `phi = \r:real^1. drop r % integral (interval[vec 0,lift(&2 * pi)])
                                (\t. lift((g:real^2->real)(wan_circ b (drop r) (drop t))))` THEN
  MP_TAC(ISPECL [`phi:real^1->real^1`; `(\r. lift(D / r1)):real^1->real^1`;
                 `lift r1`; `lift(&2 * r1)`; `{lift r1,lift(&2 * r1)}`]
                WAN_INTEGRAL_STRICT_AE) THEN
  REWRITE_TAC[NOT_IMP; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    REWRITE_TAC[INTEGRABLE_CONST];
    REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY];
    X_GEN_TAC `r:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_INTERVAL_1; LIFT_DROP; DE_MORGAN_THM] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `r1 < drop r /\ drop r < &2 * r1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[DROP_CMUL] THEN
    USE_THEN "NEG" (MP_TAC o SPEC `drop r`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ABBREV_TAC
     `I0 = drop(integral (interval[vec 0,lift(&2 * pi)])
                  (\t. lift((g:real^2->real)(wan_circ b (drop r) (drop t)))))` THEN
    SUBGOAL_THEN `&0 < drop r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `drop r * r1` THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    SUBGOAL_THEN `(drop r * r1) * D / r1 = drop r * D` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(drop r * r1) * drop r * I0 = r1 * (drop r pow 2 * I0)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `r1 * &2 * D` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (interval[lift r1,lift(&2 * r1)]) (phi:real^1->real^1) = lift D`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_CONST; LIFT_DROP; DROP_CMUL] THEN
  SUBGOAL_THEN `content(interval[lift r1,lift(&2 * r1)]) = r1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_ARITH `&0 < r1 ==> r1 <= &2 * r1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 * D / r1 = D` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < r1` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[REAL_LT_REFL]]);;

(* ========================================================================= *)
(* The harmonic piece of the competitor.  For a smooth map m0 and a circle   *)
(* of radius rho around b, the Poisson extension H of the boundary values    *)
(* m0(circ(b,rho,t)) is continuous on the closed disc, equals m0 on the      *)
(* circle, is W^{1,2} with Dirichlet integral at most rho^2 Ic, and stays in *)
(* the ball of radius sqrt(pi/2 rho^2 Ic) around m0(circ(b,rho,0)), where Ic *)
(* is the integral of |D m0|^2 over the circle (WAN_POISSON_ENERGY,          *)
(* WAN_LOOP_OSC_BOUND and the maximum principle                              *)
(* WAN_MAX_PRINCIPLE_DISC_BALL).                                             *)
(* ========================================================================= *)

let HMRM_TRIG_CS = prove
 (`!t (v:real^K) w. norm(--(sin t) % v + cos t % w) pow 2 <= norm v pow 2 + norm w pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs(sin t) * norm(v:real^K) + abs(cos t) * norm(w:real^K)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^K) <= x /\ norm(b:real^K) <= y ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sin t) pow 2 + abs(cos t) pow 2 = &1` MP_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS; SIN_CIRCLE]; ALL_TAC] THEN
  ABBREV_TAC `a = abs(sin t)` THEN ABBREV_TAC `c = abs(cos t)` THEN
  ABBREV_TAC `p = norm(v:real^K)` THEN ABBREV_TAC `q = norm(w:real^K)` THEN
  DISCH_TAC THEN MP_TAC(SPEC `a * q - c * p` REAL_LE_POW_2) THEN
  SUBGOAL_THEN
   `(a * p + c * q) pow 2 + (a * q - c * p) pow 2 = (a pow 2 + c pow 2) * (p pow 2 + q pow 2)`
  MP_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC);;

let HMRM_CIRC_COMP_CONT = prove
 (`!(Fc:real^2->real^K) b r.
     Fc continuous_on (:real^2) ==> (\s. Fc(wan_circ b r (drop s))) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^2`; `r:real`; `&0`] WAN_CIRC_CONT) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\s. (Fc:real^2->real^K)(wan_circ b r (drop s))) =
                Fc o (\s. wan_circ b r (drop s))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let HMRM_CIRC_PERIODIC = prove
 (`!(b:real^2) r t. wan_circ b r (t + &2 * pi) = wan_circ b r t`,
  REWRITE_TAC[wan_circ; SIN_PERIODIC; COS_PERIODIC]);;

let HMRM_POISSON_PIECE = prove
 (`!(m0:real^2->real^K) b rho.
     smooth_map_on (:real^2) m0 /\ &0 < rho
     ==> ?H. H continuous_on cball(b,rho) /\
             (!x. x IN sphere(b,rho) ==> H x = m0 x) /\
             wan_w12 (ball(b,rho)) H /\
             wan_dir (ball(b,rho)) H <=
             rho pow 2 *
             drop(integral (interval[vec 0,lift(&2 * pi)])
                    (\t. lift(norm(partial_derivative 1 m0 (wan_circ b rho (drop t))) pow 2 +
                              norm(partial_derivative 2 m0 (wan_circ b rho (drop t))) pow 2))) /\
             (!x. x IN cball(b,rho)
                  ==> norm(H x - m0(wan_circ b rho (&0))) pow 2 <=
                      pi / &2 * rho pow 2 *
                      drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(norm(partial_derivative 1 m0 (wan_circ b rho (drop t))) pow 2 +
                                   norm(partial_derivative 2 m0 (wan_circ b rho (drop t))) pow 2))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Ic = drop(integral (interval[vec 0,lift(&2 * pi)])
          (\t. lift(norm(partial_derivative 1 (m0:real^2->real^K) (wan_circ b rho (drop t))) pow 2 +
                    norm(partial_derivative 2 m0 (wan_circ b rho (drop t))) pow 2)))` THEN
  SUBGOAL_THEN `!i. (partial_derivative i (m0:real^2->real^K)) continuous_on (:real^2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `f = \t. (m0:real^2->real^K)(wan_circ b rho t)` THEN
  ABBREV_TAC
   `f' = \t. rho % (--(sin t) % partial_derivative 1 (m0:real^2->real^K) (wan_circ b rho t) +
                    cos t % partial_derivative 2 m0 (wan_circ b rho t))` THEN
  SUBGOAL_THEN
   `!t. &0 <= t
        ==> ((\s. (f':real->real^K)(drop s)) has_integral (f t - f(&0)))
            (interval[vec 0,lift t])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["f"; "f'"] THEN
    MP_TAC(ISPECL [`m0:real^2->real^K`; `b:real^2`; `rho:real`; `&0`; `&0`; `t:real`]
                  WAN_CIRC_FTC_SMOOTH) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. (f':real->real^K)(drop s)) continuous_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "f'" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MP_TAC(SPEC `&0` WAN_CONT_SIN_COS) THEN REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF] THEN ASM_SIMP_TAC[HMRM_CIRC_COMP_CONT; LIFT_NEG; CONTINUOUS_ON_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. lift(norm((f':real->real^K)(drop s)) pow 2)) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC HMRM_CONT_POW2 THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. lift(norm(partial_derivative 1 (m0:real^2->real^K) (wan_circ b rho (drop t))) pow 2 +
              norm(partial_derivative 2 m0 (wan_circ b rho (drop t))) pow 2))
    integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV; LIFT_ADD] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HMRM_CONT_POW2 THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    ASM_SIMP_TAC[HMRM_CIRC_COMP_CONT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)])
           (\s. lift(norm((f':real->real^K)(drop s)) pow 2))) <= rho pow 2 * Ic`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)])
        (\t. rho pow 2 %
             lift(norm(partial_derivative 1 (m0:real^2->real^K) (wan_circ b rho (drop t))) pow 2 +
                  norm(partial_derivative 2 m0 (wan_circ b rho (drop t))) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN EXPAND_TAC "f'" THEN
      REWRITE_TAC[DROP_CMUL; LIFT_DROP; NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; HMRM_TRIG_CS];
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^2`; `rho:real`; `f:real->real^K`; `f':real->real^K`]
    (REWRITE_RULE[WAN_POISSON_ENERGY_STATEMENT] (ISPEC `(:K)` WAN_POISSON_ENERGY))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[HMRM_CIRC_PERIODIC];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `H:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. y IN sphere(b:real^2,rho)
                    ==> ?t. &0 <= t /\ t <= &2 * pi /\ y = wan_circ b rho t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP WAN_SPHERE_CIRC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (SUBST1_TAC o SYM)) THEN
    MP_TAC(ISPECL [`b:real^2`; `rho:real`; `t:real`] WAN_CIRC_PERIODIC_REP) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[];
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ABBREV_TAC
   `Q = pi / &2 * drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\s. lift(norm((f':real->real^K)(drop s)) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= Q /\ Q <= pi / &2 * rho pow 2 * Ic` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (f':real->real^K)(drop s)`; `f:real->real^K`;
                 `\s. norm((f':real->real^K)(drop s)) pow 2`] WAN_LOOP_OSC_BOUND) THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[WAN_CIRC_2PI]; DISCH_THEN(LABEL_TAC "OSC")] THEN
  MP_TAC(ISPECL [`b:real^2`; `rho:real`; `H:real^2->real^K`;
                 `(f:real->real^K)(&0)`; `sqrt Q`]
    (REWRITE_RULE[WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT]
       (ISPEC `(:K)` WAN_MAX_PRINCIPLE_DISC_BALL))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sphere(b:real^2,rho)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_CBALL; dist] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    USE_THEN "OSC" (MP_TAC o SPECL [`t:real`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
                    ALL_TAC] THEN
    EXPAND_TAC "Q" THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_CBALL; dist] THEN
  SUBGOAL_THEN `(f:real->real^K)(&0) = m0(wan_circ b rho (&0))` SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt Q pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* The three generic steps of the energy comparison: gluing the harmonic     *)
(* piece H into M across a circle, the admissibility of the projected        *)
(* competitor, and the comparison of the G-energies on the region where the  *)
(* competitor differs from u.                                                *)
(* ========================================================================= *)

let HMRM_GLUE_V = prove
 (`!(s:real^2->bool) (M:real^2->real^K) H b rho t.
     open s /\ wan_w12 s M /\ &0 < rho /\ cball(b,rho) SUBSET t /\ open t /\ t SUBSET s /\
     H continuous_on cball(b,rho) /\ M continuous_on cball(b,rho) /\
     wan_w12 (ball(b,rho)) H /\ (!x. x IN sphere(b,rho) ==> H x = M x)
     ==> wan_w12 t (\x. if x IN ball(b,rho) then H x else M x) /\
         wan_dir t (\x. if x IN ball(b,rho) then H x else M x) =
         wan_dir (ball(b,rho)) H + wan_dir (t DIFF cball(b,rho)) M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 t (M:real^2->real^K) /\ wan_w12 (ball(b,rho)) (M:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`b:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `b:real^2`; `rho:real`; `M:real^2->real^K`;
                 `H:real^2->real^K`]
    (REWRITE_RULE[WAN_GLUE_W12_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_GLUE_W12))) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`b:real^2`; `rho:real`; `\x. (H:real^2->real^K) x - M x`]
    (REWRITE_RULE[WAN_W120_CONT_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT))) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[VECTOR_SUB_EQ] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]]);;

(* Admissibility: W = Pg o V on cball(b,R2) and u outside is in W^{1,2}(s), *)
(* takes values in S a.e. and W - u is in W_0^{1,2}(s).                      *)

let HMRM_ADMISSIBLE = prove
 (`!(S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) (V:real^2->real^K)
    (Pg:real^K->real^K) b R2 Z B.
     open s /\ bounded s /\ cball(b,R2) SUBSET s /\ wan_w12 s u /\ wan_w12 s V /\
     negligible Z /\ (!x. x IN s DIFF Z ==> u x IN S) /\
     (!y z. norm(Pg y - Pg z) <= B * norm(y - z)) /\
     (!x. x IN s /\ ~(x IN cball(b,R2)) ==> V x = u x) /\
     (!z. z IN S ==> Pg z = z) /\
     (!x. x IN cball(b,R2) DIFF Z ==> Pg(V x) IN S)
     ==> cm_wmap S s (\x. if x IN cball(b,R2) then Pg(V x) else u x) /\
         wan_w120 s (\x. (if x IN cball(b,R2) then Pg(V x) else u x) - u x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = \x. if x IN cball(b,R2) then (Pg:real^K->real^K)(V x)
                      else (u:real^2->real^K) x` THEN
  SUBGOAL_THEN `wan_w12 s (\x. (Pg:real^K->real^K)((V:real^2->real^K) x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `V:real^2->real^K`; `Pg:real^K->real^K`; `B:real`]
      (REWRITE_RULE[WAN_CHAIN_LIP_W12_STATEMENT]
         (ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_LIP_W12))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (W:real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `\x. (Pg:real^K->real^K)((V:real^2->real^K) x)`;
                   `W:real^2->real^K`] HMD_W12_AE_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `Z:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^2) IN Z` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((Pg:real^K->real^K)((V:real^2->real^K) x) = W x)` THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(V:real^2->real^K) x = u x /\ (u:real^2->real^K) x IN S`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cm_wmap] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `Z:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^2. x IN s DIFF Z ==> P x`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN EXISTS_TAC `cball(b:real^2,R2)` THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN EXPAND_TAC "W" THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL]);;

(* Comparison: a minimizer has at most the G-energy of an admissible W on    *)
(* an open t where W may differ from u (W = u off the closed set c, with    *)
(* c DIFF t negligible).                                                      *)

let HMRM_MIN_COMPARE = prove
 (`!S (G:real^K->real^K^K) d (s:real^2->bool) (u:real^2->real^K) W t c.
     cm_target S G d /\ open s /\ open t /\ t SUBSET s /\ closed c /\ t SUBSET c /\
     negligible(c DIFF t) /\
     cm_minimizer S G s u /\ cm_wmap S s W /\ wan_w120 s (\x. W x - u x) /\
     (!x. x IN s DIFF c ==> W x = u x)
     ==> wan_gdir t G u <= wan_gdir t G W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K) /\ wan_w12 s (W:real^2->real^K)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_gen G s (u:real^2->real^K) <= cm_gen G s W` MP_TAC THENL
   [ASM_MESON_TAC[cm_minimizer]; ALL_TAC] THEN
  REWRITE_TAC[cm_gen; REAL_ARITH `a / &2 <= b / &2 <=> a <= b`] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `t:real^2->bool`; `u:real^2->real^K`] HMRM_GDIR_SPLIT) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `t:real^2->bool`; `W:real^2->real^K`] HMRM_GDIR_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. drop(integral (s DIFF t)
          (\x. lift(wan_wd s i (u:real^2->real^K) x dot (G(u x) ** wan_wd s i u x))))) =
    sum(1..2) (\i. drop(integral (s DIFF t)
          (\x. lift(wan_wd s i (W:real^2->real^K) x dot (G(W x) ** wan_wd s i W x)))))`
  SUBST1_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `s DIFF c:real^2->bool`; `u:real^2->real^K`;
                 `W:real^2->real^K`; `i:num`] HMRM_WD_LOCAL) THEN
  ASM_SIMP_TAC[OPEN_DIFF; DIMINDEX_2; SUBSET_DIFF] THEN DISCH_TAC THEN
  EXISTS_TAC `(c DIFF t) UNION
              {x | x IN s DIFF c /\ ~(wan_wd s i (u:real^2->real^K) x = wan_wd s i W x)}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((x:real^2) IN c)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^2->real^K) x = u x /\ wan_wd s i (u:real^2->real^K) x = wan_wd s i W x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The two estimates of the mollification used by the hole filling: its      *)
(* Dirichlet integral on an annulus around b is bounded by the energy of u   *)
(* on ball(b,R) DIFF ball(b,R/16), and its squared distance to S at a point  *)
(* x with h x > 0 by the energy of u on any measurable set containing        *)
(* ball(x,h x).                                                              *)
(* ========================================================================= *)

let HMRM_VR_ANNULUS = prove
 (`?Cv. &0 < Cv /\
     !(s:real^2->bool) (u:real^2->real^K) (h:real^2->real) b R r1 r2 h0.
       open s /\ wan_w12 s u /\ &0 < R /\ cball(b,R) SUBSET s /\
       smooth_map_on (:real^2) (\x. lift(h x)) /\ (!x. &0 <= h x /\ h x <= h0) /\
       (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2) /\
       R / &16 + h0 <= r1 /\ r2 + h0 < R
       ==> wan_w12 (ball(b,r2) DIFF cball(b,r1))
                   (hmrm_vr h (\x. if x IN s then u x else vec 0)) /\
           wan_dir (ball(b,r2) DIFF cball(b,r1))
                   (hmrm_vr h (\x. if x IN s then u x else vec 0)) <=
           Cv * hmrm_en s u (ball(b,R) DIFF ball(b,R / &16))`,
  X_CHOOSE_THEN `Cv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC"))
    (INST_TYPE [`:K`,`:K`] HMRM_VR_W12_LOC) THEN
  EXISTS_TAC `Cv:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "LOC" (MP_TAC o SPECL
    [`s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real`; `cball(b:real^2,R)`;
     `ball(b:real^2,r2) DIFF cball(b,r1)`; `cball(b:real^2,r2 + h0) DIFF ball(b,r1 - h0)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CBALL; OPEN_DIFF; OPEN_BALL; CLOSED_CBALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; IN_BALL] THEN GEN_TAC THEN
      UNDISCH_TAC `r2 + h0 < R` THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_CBALL; IN_BALL; REAL_NOT_LE;
                                              REAL_NOT_LT] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= (h:real^2->real) x /\ h x <= h0` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; IN_BALL; REAL_NOT_LT] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC [`dist(x:real^2,y) < h x`; `r1 < dist(b:real^2,x)`;
                             `dist(b:real^2,x) < r2`; `(h:real^2->real) x <= h0`] THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM hmrm_en] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cv * hmrm_en s (u:real^2->real^K) (cball(b,r2 + h0) DIFF ball(b,r1 - h0))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMRM_EN_MONO THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; IN_BALL; REAL_NOT_LT] THEN GEN_TAC THEN
    MAP_EVERY UNDISCH_TAC [`r2 + h0 < R`; `R / &16 + h0 <= r1`] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]]);;

let HMRM_VR_TUBE = prove
 (`?Cn. &0 < Cn /\
     !(S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) (h:real^2->real) x A.
       closed S /\ open s /\ wan_w12 s u /\
       (?Z. negligible Z /\ !y. y IN s DIFF Z ==> u y IN S) /\
       &0 < h x /\ ball(x,h x) SUBSET A /\ lebesgue_measurable A /\ A SUBSET s
       ==> dist(hmrm_vr h (\y. if y IN s then u y else vec 0) x,
                closest_point S (hmrm_vr h (\y. if y IN s then u y else vec 0) x)) pow 2
           <= Cn * hmrm_en s u A`,
  X_CHOOSE_THEN `Cn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEAR"))
    (INST_TYPE [`:K`,`:K`] HMRM_VR_NEAR) THEN
  EXISTS_TAC `Cn:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `Z:real^2->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `ball(x:real^2,h x) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cn * wan_dir (ball(x:real^2,h x)) (u:real^2->real^K)` THEN CONJ_TAC THENL
   [USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `Z:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(x:real^2,h x)) (u:real^2->real^K) = hmrm_en s u (ball(x,h x))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMRM_EN_DIR THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRM_EN_MONO THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]);;

(* ========================================================================= *)
(* The core of the hole filling.  For the data of the target (ellipticity    *)
(* lam <= Lam, the extension Pg of the nearest point map on the d1-tube with *)
(* Lipschitz constant B), the constants Cv, Cn of HMRM_VR_ANNULUS and        *)
(* HMRM_VR_TUBE and a radius function h equal to h0 <= R/16 on cball(b,R/4)  *)
(* and 0 off ball(b,R/2): if the energy of the minimizer u on ball(b,R) is   *)
(* small, then                                                               *)
(*   lam E(ball(b,R/16)) <= Lam B^2 3 Cv E(ball(b,R) DIFF ball(b,R/16)).     *)
(* ========================================================================= *)

let HMRM_SMOOTH_DIR = prove
 (`!(m:real^2->real^K) t.
     smooth_map_on (:real^2) m /\ open t /\ bounded t
     ==> wan_w12 t m /\
         wan_dir t m =
         drop(integral t (\x. lift(norm(partial_derivative 1 m x) pow 2 +
                                   norm(partial_derivative 2 m x) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. (\x. partial_derivative i (m:real^2->real^K) x) continuous_on (:real^2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^2->real^K. f continuous_on (:real^2) ==> f IN lspace t (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRM_CONT_LSPACE2 THEN
    EXISTS_TAC `closure t:real^2->bool` THEN
    ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_SUBSET; LEBESGUE_MEASURABLE_OPEN] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `m:real^2->real^K`]
    (REWRITE_RULE[WAN_W12_C1_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_W12_C1))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HMRM_SMOOTH_CONT] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_MESON_TAC[smooth_map_on; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_ADD; GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[]);;

let HMRM_HF_CORE = prove
 (`!S (G:real^K->real^K^K) d lam Lam d1 B (Pg:real^K->real^K) Cv Cn
    (h:real^2->real) h0 (s:real^2->bool) (u:real^2->real^K) b R.
     (!(s:real^2->bool) (u:real^2->real^K) (h:real^2->real) b R r1 r2 h0.
        open s /\ wan_w12 s u /\ &0 < R /\ cball(b,R) SUBSET s /\
        smooth_map_on (:real^2) (\x. lift(h x)) /\ (!x. &0 <= h x /\ h x <= h0) /\
        (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2) /\
        R / &16 + h0 <= r1 /\ r2 + h0 < R
        ==> wan_w12 (ball(b,r2) DIFF cball(b,r1))
                    (hmrm_vr h (\x. if x IN s then u x else vec 0)) /\
            wan_dir (ball(b,r2) DIFF cball(b,r1))
                    (hmrm_vr h (\x. if x IN s then u x else vec 0)) <=
            Cv * hmrm_en s u (ball(b,R) DIFF ball(b,R / &16)))
     ==> (!(S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) (h:real^2->real) x A.
            closed S /\ open s /\ wan_w12 s u /\
            (?Z. negligible Z /\ !y. y IN s DIFF Z ==> u y IN S) /\
            &0 < h x /\ ball(x,h x) SUBSET A /\ lebesgue_measurable A /\ A SUBSET s
            ==> dist(hmrm_vr h (\y. if y IN s then u y else vec 0) x,
                     closest_point S (hmrm_vr h (\y. if y IN s then u y else vec 0) x)) pow 2
                <= Cn * hmrm_en s u A)
     ==> cm_target S G d /\
         &0 < lam /\ lam <= Lam /\ vectorize o G continuous_on (:real^K) /\
         (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi) /\
                 xi dot (G z ** xi) <= Lam * norm xi pow 2) /\
         &0 < d1 /\ &0 <= B /\ (!y z. norm(Pg y - Pg z) <= B * norm(y - z)) /\
         (!z. z IN cm_tube S d1 ==> Pg z = closest_point S z /\ closest_point S z IN S) /\
         (!z. z IN S ==> Pg z = z) /\
         &0 < Cv /\ &0 < Cn /\
         smooth_map_on (:real^2) (\x. lift(h x)) /\ (!x. &0 <= h x /\ h x <= h0) /\
         (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2) /\
         &0 < h0 /\ h0 <= R / &16 /\
         (!x. norm(x - b) <= R / &4 ==> h x = h0) /\
         (!x. R / &2 <= norm(x - b) ==> h x = &0) /\
         open s /\ bounded s /\ cm_minimizer S G s u /\ &0 < R /\ cball(b,R) SUBSET s /\
         Cn * hmrm_en s u (ball(b,R)) < (d1 / &2) pow 2 /\
         pi * Cv * hmrm_en s u (ball(b,R)) < (d1 / &2) pow 2
         ==> lam * hmrm_en s u (ball(b,R / &16)) <=
             Lam * B pow 2 * (&3 * Cv * hmrm_en s u (ball(b,R) DIFF ball(b,R / &16)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ANN") THEN DISCH_THEN(LABEL_TAC "TUBE") THEN
  STRIP_TAC THEN
  (* the minimizer and the target *)
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN `?Z. negligible Z /\ !x. x IN s DIFF Z ==> (u:real^2->real^K) x IN S`
  (X_CHOOSE_THEN `Z:real^2->bool` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (S:real^K->bool) /\ ~(S = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `cm_target S (G:real^K->real^K^K) d`) THEN REWRITE_TAC[cm_target] THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `u0 = \x:real^2. if x IN s then (u:real^2->real^K) x else vec 0` THEN
  SUBGOAL_THEN `(u0:real^2->real^K) IN lspace (:real^2) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "u0" THEN
    ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`; WAN_W12_IMP_LSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (u0:real^2->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (wan_moll h0 (u0:real^2->real^K))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* M = hmrm_vr h u0: equal to m0 = wan_moll h0 u0 near b, to u far from b *)
  SUBGOAL_THEN
   `!x. norm(x - b) <= R / &4 ==> hmrm_vr h (u0:real^2->real^K) x = wan_moll h0 u0 x`
  (LABEL_TAC "MM0") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^2->real) x = h0` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^2->real`; `u0:real^2->real^K`; `x:real^2`] HMRM_VR_MOLL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s /\ R / &2 <= norm(x - b) ==> hmrm_vr h (u0:real^2->real^K) x = u x`
  (LABEL_TAC "MU") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^2->real) x = &0` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HMRM_VR_ZERO] THEN EXPAND_TAC "u0" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (hmrm_vr h (u0:real^2->real^K))` ASSUME_TAC THENL
   [EXPAND_TAC "u0" THEN MATCH_MP_TAC HMRM_VR_W12_GLOBAL THEN
    EXISTS_TAC `cball(b:real^2,R)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(x - b:real^2) < R / &2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^2->real) x = &0` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^2->real) x <= R / &16` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN DISCH_TAC THEN X_GEN_TAC `y:real^2` THEN
    MAP_EVERY UNDISCH_TAC [`(h:real^2->real) x <= R / &16`; `norm(x - b:real^2) < R / &2`;
                           `&0 < R`] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  (* the energy density of m0 and a good circle in the annulus R/8 < |x - b| < R/4 *)
  ABBREV_TAC
   `e0 = \x. norm(partial_derivative 1 (wan_moll h0 (u0:real^2->real^K)) x) pow 2 +
             norm(partial_derivative 2 (wan_moll h0 u0) x) pow 2` THEN
  SUBGOAL_THEN `(\x. lift((e0:real^2->real) x)) continuous_on (:real^2) /\ (!x. &0 <= e0 x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2] THEN REWRITE_TAC[LIFT_ADD] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC HMRM_CONT_POW2 THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC HMRM_SMOOTH_CONT THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real^2->real`; `b:real^2`; `R / &8`] HMRM_GOOD_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 * R / &8 = R / &4`; HMRM_ANNULUS_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `En = hmrm_en s (u:real^2->real^K) (ball(b,R) DIFF ball(b,R / &16))` THEN
  ABBREV_TAC `Eb = hmrm_en s (u:real^2->real^K) (ball(b,R))` THEN
  SUBGOAL_THEN `&0 <= En /\ En <= Eb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["En"; "Eb"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_EN_POS; MATCH_MP_TAC HMRM_EN_MONO] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL; SUBSET_DIFF] THEN
    MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the energy of m0 on the inner annulus *)
  SUBGOAL_THEN
   `drop(integral (ball(b,R / &4) DIFF cball(b:real^2,R / &8)) (\x. lift((e0:real^2->real) x)))
    <= Cv * En`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `drop(integral (ball(b,R / &4) DIFF cball(b:real^2,R / &8))
                    (\x. lift((e0:real^2->real) x))) =
      wan_dir (ball(b,R / &4) DIFF cball(b,R / &8)) (wan_moll h0 (u0:real^2->real^K))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`wan_moll h0 (u0:real^2->real^K)`;
                     `ball(b:real^2,R / &4) DIFF cball(b,R / &8)`] HMRM_SMOOTH_DIR) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL; BOUNDED_DIFF; BOUNDED_BALL];
        DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN EXPAND_TAC "e0" THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_dir (ball(b,R / &4) DIFF cball(b:real^2,R / &8)) (wan_moll h0 (u0:real^2->real^K)) =
      wan_dir (ball(b,R / &4) DIFF cball(b,R / &8)) (hmrm_vr h u0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC HMRM_DIR_EQ_ON THEN X_GEN_TAC `x:real^2` THEN
      REWRITE_TAC[IN_DIFF; IN_BALL] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "MM0" MATCH_MP_TAC THEN UNDISCH_TAC `dist(b:real^2,x) < R / &4` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    USE_THEN "ANN" (MP_TAC o SPECL
      [`s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real`; `b:real^2`; `R:real`;
       `R / &8`; `R / &4`; `h0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the harmonic piece on the good circle *)
  MP_TAC(ISPECL [`wan_moll h0 (u0:real^2->real^K)`; `b:real^2`; `rho:real`]
                HMRM_POISSON_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(norm(partial_derivative 1 (wan_moll h0 (u0:real^2->real^K))
                       (wan_circ b rho (drop t))) pow 2 +
                norm(partial_derivative 2 (wan_moll h0 u0) (wan_circ b rho (drop t))) pow 2))) =
    drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift((e0:real^2->real)(wan_circ b rho (drop t)))))`
  SUBST1_TAC THENL [EXPAND_TAC "e0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Ic = drop(integral (interval[vec 0,lift(&2 * pi)])
                       (\t. lift((e0:real^2->real)(wan_circ b rho (drop t)))))` THEN
  ABBREV_TAC `p0 = wan_circ b rho (&0)` THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rho pow 2 * Ic <= &2 * Cv * En` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pi * Cv * En < (d1 / &2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `pi * Cv * Eb` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pi / &2 * rho pow 2 * Ic <= pi * Cv * En` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &2 * (&2 * Cv * En)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the outer annulus R/8 < rho < |x - b| < R/2 *)
  REMOVE_THEN "ANN" (MP_TAC o SPECL
    [`s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real`; `b:real^2`; `R:real`;
     `rho:real`; `R / &2`; `h0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* closeness to S *)
  SUBGOAL_THEN `?Z. negligible Z /\ !y. y IN s DIFF Z ==> (u:real^2->real^K) y IN S`
  ASSUME_TAC THENL [EXISTS_TAC `Z:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "TUBE" (MP_TAC o SPECL
    [`S:real^K->bool`; `s:real^2->bool`; `u:real^2->real^K`; `h:real^2->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "TB") THEN
  SUBGOAL_THEN `&0 < d1 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(d1 / &2) pow 2 < d1 pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < d1 pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(p0 - b:real^2) = rho` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `hmrm_vr h (u0:real^2->real^K) p0 = wan_moll h0 u0 p0` ASSUME_TAC THENL
   [USE_THEN "MM0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `dist(wan_moll h0 (u0:real^2->real^K) p0, closest_point S (wan_moll h0 u0 p0)) < d1 / &2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `hmrm_vr h (u0:real^2->real^K) p0 = wan_moll h0 u0 p0`)) THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Cn * Eb` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Eb" THEN USE_THEN "TB" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(h:real^2->real) p0 = h0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^2` THEN
      MAP_EVERY UNDISCH_TAC [`norm(p0 - b:real^2) = rho`; `rho < R / &4`;
                             `h0 <= R / &16`; `&0 < R`] THEN
      CONV_TAC NORM_ARITH;
      MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the values of H and M near b are in the d1-tube *)
  SUBGOAL_THEN `!x. x IN ball(b,rho) ==> (H:real^2->real^K) x IN cm_tube S d1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
    EXISTS_TAC `closest_point S (wan_moll h0 (u0:real^2->real^K) p0)` THEN
    ASM_SIMP_TAC[CLOSEST_POINT_IN_SET] THEN
    SUBGOAL_THEN `norm((H:real^2->real^K) x - wan_moll h0 (u0:real^2->real^K) p0) < d1 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `pi * Cv * En` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &2 * rho pow 2 * Ic` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`b:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `dist(wan_moll h0 (u0:real^2->real^K) p0, closest_point S (wan_moll h0 u0 p0)) < d1 / &2` THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN cball(b,R / &2) DIFF Z ==> hmrm_vr h (u0:real^2->real^K) x IN cm_tube S d1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN cball(b,R / &2)` THEN
      MATCH_MP_TAC(SET_RULE `t SUBSET (s:real^2->bool) ==> x IN t ==> x IN s`) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(b:real^2,R)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
    ASM_CASES_TAC `&0 < (h:real^2->real) x` THENL
     [EXISTS_TAC `closest_point S (hmrm_vr h (u0:real^2->real^K) x)` THEN
      ASM_SIMP_TAC[CLOSEST_POINT_IN_SET] THEN
      MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Cn * Eb` THEN CONJ_TAC THENL
       [EXPAND_TAC "Eb" THEN USE_THEN "TB" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(h:real^2->real) x <= R / &16` MP_TAC THENL
           [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
          UNDISCH_TAC `(x:real^2) IN cball(b,R / &2)` THEN
          REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
          REPEAT DISCH_TAC THEN X_GEN_TAC `y:real^2` THEN
          MAP_EVERY UNDISCH_TAC [`(h:real^2->real) x <= R / &16`; `dist(b:real^2,x) <= R / &2`;
                                 `&0 < R`] THEN
          CONV_TAC NORM_ARITH;
          MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(h:real^2->real) x = &0` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= h /\ ~(&0 < h) ==> h = &0`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(u:real^2->real^K) x` THEN ASM_SIMP_TAC[HMRM_VR_ZERO; IN_DIFF] THEN
      EXPAND_TAC "u0" THEN ASM_REWRITE_TAC[DIST_REFL]];
    ALL_TAC] THEN
  (* the glued map V and the projected competitor W *)
  ABBREV_TAC `V = \x. if x IN ball(b,rho) then (H:real^2->real^K) x
                      else hmrm_vr h (u0:real^2->real^K) x` THEN
  SUBGOAL_THEN
   `hmrm_vr h (u0:real^2->real^K) continuous_on cball(b,rho) /\
    (!x. x IN sphere(b,rho) ==> (H:real^2->real^K) x = hmrm_vr h u0 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_moll h0 (u0:real^2->real^K)` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
        CONV_TAC SYM_CONV THEN USE_THEN "MM0" MATCH_MP_TAC THEN
        MAP_EVERY UNDISCH_TAC [`dist(b:real^2,x) <= rho`; `rho < R / &4`] THEN
        CONV_TAC NORM_ARITH;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[HMRM_SMOOTH_CONT; SUBSET_UNIV]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(H:real^2->real^K) x = wan_moll h0 u0 x` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "MM0" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^2) IN sphere(b,rho)` THEN REWRITE_TAC[IN_SPHERE] THEN
      UNDISCH_TAC `rho < R / &4` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(b:real^2,R / &2) SUBSET s /\ ball(b:real^2,R / &2) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(b:real^2->bool) SUBSET c /\ c SUBSET s ==> c SUBSET s /\ b SUBSET s`) THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(b:real^2,R)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `hmrm_vr h (u0:real^2->real^K)`; `H:real^2->real^K`;
                 `b:real^2`; `rho:real`; `s:real^2->bool`] HMRM_GLUE_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(b:real^2,R)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `hmrm_vr h (u0:real^2->real^K)`; `H:real^2->real^K`;
                 `b:real^2`; `rho:real`; `ball(b:real^2,R / &2)`] HMRM_GLUE_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN
    MAP_EVERY UNDISCH_TAC [`rho < R / &4`; `&0 < R`] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN cball(b,R / &2) DIFF Z ==> (Pg:real^K->real^K)((V:real^2->real^K) x) IN S`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(V:real^2->real^K) x IN cm_tube S d1` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN s /\ ~(x IN cball(b,R / &2)) ==> (V:real^2->real^K) x = u x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL; REAL_NOT_LE] THEN STRIP_TAC THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `~(dist(b:real^2,x) < rho)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "MU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `R / &2 < dist(b:real^2,x)` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `s:real^2->bool`; `u:real^2->real^K`; `V:real^2->real^K`;
                 `Pg:real^K->real^K`; `b:real^2`; `R / &2`; `Z:real^2->bool`; `B:real`]
                HMRM_ADMISSIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = \x. if x IN cball(b,R / &2) then (Pg:real^K->real^K)((V:real^2->real^K) x)
                      else (u:real^2->real^K) x` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wan_w120 s (\x. (W:real^2->real^K) x - u x)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the comparison of the G-energies on ball(b,R/2) *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `W:real^2->real^K`; `ball(b:real^2,R / &2)`;
                 `cball(b:real^2,R / &2)`] HMRM_MIN_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CLOSED_CBALL; BALL_SUBSET_CBALL; CBALL_DIFF_BALL;
                    NEGLIGIBLE_SPHERE] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN EXPAND_TAC "W" THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(b,R / &2)) (u:real^2->real^K) /\
                wan_w12 (ball(b,R / &2)) (W:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[cm_wmap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(b:real^2,R / &2)`; `G:real^K->real^K^K`; `u:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  MP_TAC(ISPECL [`ball(b:real^2,R / &2)`; `G:real^K->real^K^K`; `W:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(b,R / &2)) (W:real^2->real^K) =
    wan_dir (ball(b,R / &2)) (\x. (Pg:real^K->real^K)((V:real^2->real^K) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRM_DIR_EQ_ON THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN cball(b,R / &2)` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`b:real^2`; `R / &2`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(b:real^2,R / &2)`; `V:real^2->real^K`; `Pg:real^K->real^K`; `B:real`]
    (REWRITE_RULE[WAN_CHAIN_LIP_W12_STATEMENT]
       (ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_LIP_W12))) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lam * hmrm_en s (u:real^2->real^K) (ball(b,R / &16)) <=
    lam * wan_dir (ball(b,R / &2)) u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `wan_dir (ball(b,R / &2)) (u:real^2->real^K) = hmrm_en s u (ball(b,R / &2))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMRM_EN_DIR THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MATCH_MP_TAC HMRM_EN_MONO THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(b,R / &2)) (V:real^2->real^K) <= &3 * Cv * En` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= &2 * c /\ b <= c ==> a + b <= &3 * c`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam /\ &0 <= B pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Lam * wan_dir (ball(b,R / &2)) (W:real^2->real^K)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B pow 2 * wan_dir (ball(b,R / &2)) (V:real^2->real^K)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `wan_dir (ball(b,R / &2)) (V:real^2->real^K) <= &3 * Cv * En` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Hole filling (Widman) for G-energy minimizers on balls of small energy:   *)
(*   E(ball(b,R/16)) <= Ch E(ball(b,R) DIFF ball(b,R/16))                    *)
(* with eps0, Ch depending only on the target data (S,G,d).                  *)
(* ========================================================================= *)

let HMRM_HOLE_FILL = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eps0 Ch. &0 < eps0 /\ &0 < Ch /\
           !s u b R.
             open s /\ bounded s /\ cm_minimizer S G s u /\ &0 < R /\
             cball(b,R) SUBSET s /\ hmrm_en s u (ball(b,R)) < eps0
             ==> hmrm_en s u (ball(b,R / &16)) <=
                 Ch * hmrm_en s u (ball(b,R) DIFF ball(b,R / &16))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) o
              MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` STRIP_ASSUME_TAC)) o MATCH_MP HMRM_PG) THEN
  X_CHOOSE_THEN `Cv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ANN"))
    (INST_TYPE [`:K`,`:K`] HMRM_VR_ANNULUS) THEN
  X_CHOOSE_THEN `Cn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TUBE"))
    (INST_TYPE [`:K`,`:K`] HMRM_VR_TUBE) THEN
  X_CHOOSE_THEN `c0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CUT")))
    (INST_TYPE [`:2`,`:N`] HMRM_H_CUTOFF) THEN
  SUBGOAL_THEN `&0 < Cn + pi * Cv + &1 /\ &0 < (d1 / &2) pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < a + b + &1`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; PI_POS];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(d1 / &2) pow 2 / (Cn + pi * Cv + &1)` THEN
  EXISTS_TAC `Lam * (B pow 2 + &1) * &3 * Cv / lam` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Eb = hmrm_en s (u:real^2->real^K) (ball(b,R))` THEN
  ABBREV_TAC `En = hmrm_en s (u:real^2->real^K) (ball(b,R) DIFF ball(b,R / &16))` THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Eb /\ &0 <= En` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Eb"; "En"] THEN CONJ_TAC THEN MATCH_MP_TAC HMRM_EN_POS THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL] THEN
    MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cn * Eb < (d1 / &2) pow 2 /\ pi * Cv * Eb < (d1 / &2) pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(Cn + pi * Cv + &1) * Eb < (d1 / &2) pow 2` MP_TAC THENL
     [UNDISCH_TAC `Eb < (d1 / &2) pow 2 / (Cn + pi * Cv + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pi * Cv * Eb /\ &0 <= Cn * Eb` MP_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; PI_POS];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 <= Eb` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radius function *)
  USE_THEN "CUT" (MP_TAC o SPECL [`b:real^2`; `R / &4`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 * R / &4 = R / &2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!z. z IN cm_tube S d1 ==> (Pg:real^K->real^K) z = closest_point S z /\
                               closest_point S z IN S) /\
    (!z. z IN S ==> (Pg:real^K->real^K) z = z) /\
    &0 < c0 * R / &4 /\ c0 * R / &4 <= R / &16`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &4 * R / &4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `lam:real`; `Lam:real`;
                 `d1:real`; `B:real`; `Pg:real^K->real^K`; `Cv:real`; `Cn:real`;
                 `\x. c0 * R / &4 * smooth_bump (R / &4) (R / &2) (x - b:real^2)`;
                 `c0 * R / &4`; `s:real^2->bool`; `u:real^2->real^K`; `b:real^2`; `R:real`]
                HMRM_HF_CORE) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [USE_THEN "ANN" ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [USE_THEN "TUBE" ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Lam * B pow 2 * (&3 * Cv * En)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lam * (Lam * (B pow 2 + &1) * &3 * Cv / lam) * En =
                Lam * (B pow 2 + &1) * (&3 * Cv * En)`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* From hole filling to power decay.                                         *)
(*   E(ball(b,R/16)) <= theta E(ball(b,R)), theta = Ch/(1+Ch) < 1, iterated  *)
(* m times with theta^m <= 1/16, gives                                       *)
(*   E(ball(b,rho)) <= 16 (rho/R)^(1/m) E(ball(b,R))   (0 < rho <= R).       *)
(* ========================================================================= *)

let HMRM_EN_SPLIT_BALL = prove
 (`!(s:real^2->bool) (u:real^2->real^K) b r R.
     wan_w12 s u /\ ball(b,R) SUBSET s /\ r <= R
     ==> hmrm_en s u (ball(b,R)) =
         hmrm_en s u (ball(b,r)) + hmrm_en s u (ball(b,R) DIFF ball(b,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(b:real^2,R) = ball(b,r) UNION (ball(b,R) DIFF ball(b,r))`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [MP_TAC(ISPECL [`b:real^2`; `r:real`; `R:real`] SUBSET_BALL) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRM_EN_UNION THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_DIFF] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`b:real^2`; `r:real`; `R:real`] SUBSET_BALL) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    REWRITE_TAC[SET_RULE `(s:real^2->bool) INTER (t DIFF s) = {}`; NEGLIGIBLE_EMPTY]]);;

let HMRM_RPOW_POW_INV = prove
 (`!m k. 1 <= m ==> (inv(&16 pow m) pow k) rpow (inv(&m)) = inv(&16) pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(&16 pow m) pow k = (inv(&16) pow k) rpow (&m)` SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_POW; REAL_POW_INV; REAL_POW_POW] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SIMP_TAC[RPOW_RPOW; REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
  SUBGOAL_THEN `&m * inv(&m) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    REWRITE_TAC[RPOW_POW; REAL_POW_1]]);;

let HMRM_ITER_DECAY = prove
 (`!(phi:real->real) R0 m.
     &0 < R0 /\ 1 <= m /\ (!t. &0 < t /\ t <= R0 ==> &0 <= phi t) /\
     (!s t. &0 < s /\ s <= t /\ t <= R0 ==> phi s <= phi t) /\
     (!r. &0 < r /\ r <= R0 ==> phi(r / &16 pow m) <= phi r / &16)
     ==> !rho r. &0 < rho /\ rho <= r /\ r <= R0
                 ==> phi rho <= &16 * (rho / r) rpow (inv(&m)) * phi r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = inv(&16 pow m)` THEN
  SUBGOAL_THEN `&0 < q /\ q <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &16`] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n r. &0 < r /\ r <= R0
                      ==> &0 < r * q pow n /\ r * q pow n <= R0 /\ r * q pow n <= r`
  (LABEL_TAC "RN") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < q pow n /\ q pow n <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r * q pow n <= r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n r. &0 < r /\ r <= R0 ==> phi(r * q pow n) <= phi r * inv(&16) pow n`
  (LABEL_TAC "IT") THENL
   [INDUCT_TAC THENL [REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "RN" (MP_TAC o SPECL [`n:num`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r * q pow n` o check (fun th ->
      can (find_term ((=) `&16 pow m`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r * q pow n) / &16 pow m = r * q pow SUC n` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[real_pow; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(phi:real->real)(r * q pow n) <= phi r * inv(&16) pow n` THEN
    REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rho:real`; `r:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?n. r * q pow n < rho` MP_TAC THENL
   [ASM_CASES_TAC `q < &1` THENL
     [MP_TAC(SPECL [`q:real`; `rho / r`] REAL_ARCH_POW_INV) THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      EXISTS_TAC `n:num` THEN UNDISCH_TAC `q pow n < rho / r` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~(q < &1)` THEN EXPAND_TAC "q" THEN REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_INV_LT_1 THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
   [REWRITE_TAC[real_pow; REAL_MUL_RID; LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n':num`) THEN REWRITE_TAC[LT; REAL_NOT_LT] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  USE_THEN "RN" (MP_TAC o SPECL [`n':num`; `r:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real->real)(r * q pow n')` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `s:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real->real) r * inv(&16) pow n'` THEN
  CONJ_TAC THENL [USE_THEN "IT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&16) pow SUC n' <= (rho / r) rpow (inv(&m))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:num`; `SUC n'`] HMRM_RPOW_POW_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (phi:real->real) r` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&16) pow SUC n' * (phi:real->real) r <=
                (rho / r) rpow (inv(&m)) * phi r` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Power decay of the energy of a G-energy minimizer on balls of small       *)
(* energy (data S,G,d fixed):                                                *)
(*   E(ball(b,rho)) <= 16 (rho/R)^(1/m) E(ball(b,R)),  0 < rho <= R.         *)
(* ========================================================================= *)

let HMRM_DECAY = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eps0 m. &0 < eps0 /\ 1 <= m /\
           !s u b R rho.
             open s /\ bounded s /\ cm_minimizer S G s u /\ &0 < R /\
             cball(b,R) SUBSET s /\ hmrm_en s u (ball(b,R)) < eps0 /\
             &0 < rho /\ rho <= R
             ==> hmrm_en s u (ball(b,rho)) <=
                 &16 * (rho / R) rpow (inv(&m)) * hmrm_en s u (ball(b,R))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `eps0:real` (X_CHOOSE_THEN `Ch:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HF")))) o
    MATCH_MP HMRM_HOLE_FILL) THEN
  ABBREV_TAC `theta = Ch / (&1 + Ch)` THEN
  SUBGOAL_THEN `&0 < theta /\ theta < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "theta" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`theta:real`; `inv(&16)`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `theta pow m < inv(&16)` THEN ASM_REWRITE_TAC[real_pow] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  EXISTS_TAC `eps0:real` THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t <= R
        ==> cball(b,t) SUBSET s /\ ball(b:real^2,t) SUBSET s /\
            hmrm_en s (u:real^2->real^K) (ball(b,t)) <= hmrm_en s u (ball(b,R)) /\
            &0 <= hmrm_en s u (ball(b,t))`
  (LABEL_TAC "PER") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `cball(b:real^2,t) SUBSET s /\ ball(b:real^2,t) SUBSET s /\
                  ball(b:real^2,R) SUBSET s`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`b:real^2`; `t:real`; `R:real`] SUBSET_CBALL) THEN
      MP_TAC(ISPECL [`b:real^2`; `t:real`] BALL_SUBSET_CBALL) THEN
      MP_TAC(ISPECL [`b:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_EN_MONO THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HMRM_EN_POS THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
    ALL_TAC] THEN
  (* one hole filling step *)
  SUBGOAL_THEN
   `!t. &0 < t /\ t <= R
        ==> hmrm_en s (u:real^2->real^K) (ball(b,t / &16)) <=
            theta * hmrm_en s u (ball(b,t))`
  (LABEL_TAC "ST") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "PER" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "HF" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `b:real^2`;
                                   `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `b:real^2`; `t / &16`; `t:real`]
                  HMRM_EN_SPLIT_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "theta" THEN
    ABBREV_TAC `a = hmrm_en s (u:real^2->real^K) (ball(b,t / &16))` THEN
    ABBREV_TAC `D = hmrm_en s (u:real^2->real^K) (ball(b,t) DIFF ball(b,t / &16))` THEN
    SUBGOAL_THEN `Ch / (&1 + Ch) * (a + D) = (Ch * (a + D)) / (&1 + Ch)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* iterated *)
  SUBGOAL_THEN
   `!k t. &0 < t /\ t <= R
          ==> hmrm_en s (u:real^2->real^K) (ball(b,t / &16 pow k)) <=
              theta pow k * hmrm_en s u (ball(b,t))`
  (LABEL_TAC "STK") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; real_div; REAL_INV_1; REAL_MUL_RID; REAL_MUL_LID; REAL_LE_REFL];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < t / &16 pow k /\ t / &16 pow k <= t` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 <= &16 pow k` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&1 <= x ==> &0 < x`; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ST" (MP_TAC o SPEC `t / &16 pow k`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(t / &16 pow k) / &16 = t / &16 pow SUC k` SUBST1_TAC THENL
     [REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `&0 <= theta` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `e1 = hmrm_en s (u:real^2->real^K) (ball(b,t / &16 pow k))` THEN
    ABBREV_TAC `e2 = hmrm_en s (u:real^2->real^K) (ball(b,t / &16 pow SUC k))` THEN
    ABBREV_TAC `e0 = hmrm_en s (u:real^2->real^K) (ball(b,t))` THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `theta * e1` THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. hmrm_en s (u:real^2->real^K) (ball(b,t))`; `R:real`; `m:num`]
                HMRM_ITER_DECAY) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRM_EN_MONO THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
        USE_THEN "PER" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "STK" (MP_TAC o SPECL [`m:num`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "PER" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ABBREV_TAC `e0 = hmrm_en s (u:real^2->real^K) (ball(b,t))` THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `theta pow m * e0` THEN
      ASM_REWRITE_TAC[REAL_ARITH `e0 / &16 = inv(&16) * e0`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(MP_TAC o SPECL [`rho:real`; `R:real`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

