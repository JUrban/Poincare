(* ========================================================================= *)
(* Unit pc_hm_reg_min: regularity of G-energy minimizers from planar balls   *)
(* into S (Schoen-Uhlenbeck 1982, sec. 3, in the hole filling form): every   *)
(* W^{1,2} minimizer is a.e. equal to a continuous S-valued minimizer        *)
(* (Campanato from the energy decay of pc_hm_rmin_hf, local representatives  *)
(* glued by Lindeloef), which is cm_wharmonic (pc_hm_rmin_fv);               *)
(* CM_REG01_STATEMENT then makes it cm_harmonic.                             *)
(*   HMRM_MINIMIZER_SMOOTH |- !kk. CM_REG01_STATEMENT kk                     *)
(*                                 ==> CM_MINIMIZER_SMOOTH_STATEMENT kk      *)
(* ========================================================================= *)

needs "src/pc_hm_rmin_hf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Hoelder continuity on balls of small energy.  Poincare on ball(x,rho) and *)
(* the decay of HMRM_DECAY give the Campanato condition with exponent        *)
(* al = 1/(2m) on ball(x0,R0/4); hence a continuous representative on        *)
(* ball(x0,R0/8) (WAN_CAMPANATO).                                            *)
(* ========================================================================= *)

(* A Hoelder map is continuous.  (The same argument as HMRC_HOLDER_CONT of  *)
(* pc_hm_reg_c1a, which is not in this load closure.)                       *)

let HMRM_HOLDER_CONT = prove
 (`!(s:real^N->bool) (w:real^N->real^K) L al.
     &0 < al /\ &0 <= L /\
     (!x y. x IN s /\ y IN s ==> norm(w x - w y) <= L * norm(x - y) rpow al)
     ==> w continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(e / (L + &1)) rpow (inv al)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN REWRITE_TAC[dist] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * norm(y - x:real^N) rpow al` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * e / (L + &1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `e / (L + &1) = ((e / (L + &1)) rpow (inv al)) rpow al` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 <= e / (L + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_LINV; REAL_LT_IMP_NZ; RPOW_POW] THEN
      REWRITE_TAC[REAL_POW_1];
      ALL_TAC] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `dist(y:real^N,x) < (e / (L + &1)) rpow inv al` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < L + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let HMRM_LOCAL_CONT = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?eps0. &0 < eps0 /\
           !s u x0 R0.
             open s /\ bounded s /\ cm_minimizer S G s u /\ &0 < R0 /\
             cball(x0,R0) SUBSET s /\ hmrm_en s u (ball(x0,R0)) < eps0
             ==> ?w. w continuous_on ball(x0,R0 / &8) /\
                     negligible {x | x IN ball(x0,R0 / &8) /\ ~(u x = w x)}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `eps0:real` (X_CHOOSE_THEN `m:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DEC")))) o
    MATCH_MP HMRM_DECAY) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `al = inv(&2 * &m)` THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < al /\ al <= &1 /\ &2 * al = inv(&m)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      SUBGOAL_THEN `&1 <= &m` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
      UNDISCH_TAC `&0 < &m` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(SPEC `al:real`
    (REWRITE_RULE[WAN_CAMPANATO_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_CAMPANATO))) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAMP"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  ABBREV_TAC `E0 = hmrm_en s (u:real^2->real^K) (ball(x0,R0))` THEN
  SUBGOAL_THEN `&0 <= E0` ASSUME_TAC THENL
   [EXPAND_TAC "E0" THEN MATCH_MP_TAC HMRM_EN_POS THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    MP_TAC(ISPECL [`x0:real^2`; `R0:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = (R0 / &2) rpow (inv(&m))` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Kc = sqrt(&256 * E0 / q)` THEN
  SUBGOAL_THEN `&0 <= &256 * E0 / q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kc /\ Kc pow 2 = &256 * E0 / q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  USE_THEN "CAMP" (MP_TAC o SPECL [`x0:real^2`; `R0 / &4`; `u:real^2->real^K`; `Kc:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,R0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(x0:real^2,R0 / &4)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
      MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `rho:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(x:real^2,x0) + rho <= R0 / &4` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(x:real^2,rho) SUBSET ball(x0,R0 / &4)` THEN
      REWRITE_TAC[SUBSET_BALLS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= dist(x:real^2,x0)` ASSUME_TAC THENL
     [REWRITE_TAC[DIST_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `cball(x:real^2,R0 / &2) SUBSET s /\ ball(x:real^2,R0 / &2) SUBSET ball(x0,R0) /\
                  ball(x:real^2,rho) SUBSET s`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,R0)` THEN
        ASM_REWRITE_TAC[SUBSET_BALLS];
        REWRITE_TAC[SUBSET_BALLS];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,R0)` THEN
        ASM_REWRITE_TAC[SUBSET_BALLS]] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^2`; `rho:real`; `u:real^2->real^K`] WAN_POINCARE_BALL_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_RAT_REDUCE_CONV `&2 pow 4`] THEN
    SUBGOAL_THEN `wan_dir (ball(x:real^2,rho)) (u:real^2->real^K) = hmrm_en s u (ball(x,rho))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMRM_EN_DIR THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "DEC" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `x:real^2`;
                                    `R0 / &2`; `rho:real`]) THEN
    SUBGOAL_THEN `hmrm_en s (u:real^2->real^K) (ball(x,R0 / &2)) <= E0` ASSUME_TAC THENL
     [EXPAND_TAC "E0" THEN MATCH_MP_TAC HMRM_EN_MONO THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      MP_TAC(ISPECL [`x0:real^2`; `R0:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RPOW_DIV; ASSUME `(R0 / &2) rpow inv(&m) = q`] THEN
    SUBGOAL_THEN `rho rpow (&2 + inv(&m)) = rho pow 2 * rho rpow (inv(&m))` SUBST1_TAC THENL
     [SIMP_TAC[RPOW_ADD; RPOW_POW; ASSUME `&0 < rho`]; ALL_TAC] THEN
    ABBREV_TAC `p = rho rpow (inv(&m))` THEN
    SUBGOAL_THEN `&0 <= p` ASSUME_TAC THENL
     [EXPAND_TAC "p" THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `Ex = hmrm_en s (u:real^2->real^K) (ball(x,rho))` THEN
    ABBREV_TAC `Ex1 = hmrm_en s (u:real^2->real^K) (ball(x,R0 / &2))` THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `I1 = drop(integral (ball(x:real^2,rho))
                       (\y. lift(norm((u:real^2->real^K) y -
                                      inv(measure(ball(x,rho))) % integral (ball(x,rho)) u)
                                 pow 2)))` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 * rho pow 2 * Ex` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&16 * rho pow 2 * (&16 * (p / q) * E0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 * (p / q) * Ex1` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(R0 / &4) / &2 = R0 / &8`] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMRM_HOLDER_CONT THEN MAP_EVERY EXISTS_TAC [`C * Kc`; `al:real`] THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A continuous representative on the whole domain.  Small balls have small  *)
(* energy (absolute continuity of the integral); local continuous            *)
(* representatives agree on overlaps (HMD_CONT_AE_EQ);                       *)
(* w(x) = (representative at x)(x) is continuous and, by Lindeloef and       *)
(* countable unions, equal to u almost everywhere.                           *)
(* ========================================================================= *)

let HMRM_SMALL_BALL = prove
 (`!(s:real^2->bool) (u:real^2->real^K) eps0.
     open s /\ wan_w12 s u /\ &0 < eps0
     ==> !x. x IN s
             ==> ?R0. &0 < R0 /\ cball(x,R0) SUBSET s /\ hmrm_en s u (ball(x,R0)) < eps0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm(wan_wd s 1 (u:real^2->real^K) x) pow 2 +
                           norm(wan_wd s 2 u x) pow 2)`;
                 `s:real^2->bool`; `eps0:real`] ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HMRM_EN_DENS; LEBESGUE_MEASURABLE_OPEN; SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M1 = measure(ball(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `&0 < M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < del / (M1 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < min r0 (sqrt(del / (M1 + &1))) /\ min r0 (sqrt(del / (M1 + &1))) <= r0 /\
    min r0 (sqrt(del / (M1 + &1))) pow 2 <= del / (M1 + &1)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(del / (M1 + &1)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL; REAL_LE_MIN] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = min r0 (sqrt(del / (M1 + &1)))` THEN STRIP_TAC THEN
  EXISTS_TAC `R0:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,R0) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^2,R0)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ball(x:real^2,R0)` o check (fun th ->
    can (find_term ((=) `del:real`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
    ASM_SIMP_TAC[HMRM_MEASURE_BALL2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `del / (M1 + &1) * M1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < M ==> d / (M + &1) * M = d * M / (M + &1)`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < M ==> &0 < M + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[hmrm_en] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  ASM_REWRITE_TAC[drop; GSYM NORM_1]);;

let HMRM_GLUE_LOCAL = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     open s /\
     (!x. x IN s ==> ?r w. &0 < r /\ ball(x,r) SUBSET s /\ w continuous_on ball(x,r) /\
                           negligible {y | y IN ball(x,r) /\ ~(u y = w y)})
     ==> ?w. w continuous_on s /\ negligible {x | x IN s /\ ~(u x = w x)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real^N->real` (X_CHOOSE_THEN `ww:real^N->real^N->real^K`
       (LABEL_TAC "LOC"))) THEN
  SUBGOAL_THEN
   `!x y z. x IN s /\ y IN s /\ z IN ball(x,rr x) /\ z IN ball(y,rr y)
            ==> (ww:real^N->real^N->real^K) x z = ww y z`
  (LABEL_TAC "AGR") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(y:real^N) IN s`)) THEN
    MP_TAC(ISPECL [`ball(x:real^N,rr x) INTER ball(y,rr y)`;
                   `(ww:real^N->real^N->real^K) x`; `(ww:real^N->real^N->real^K) y`]
                  HMD_CONT_AE_EQ) THEN
    ANTS_TAC THENL
     [SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(x:real^N,rr x)` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(y:real^N,rr y)` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{z | z IN ball(x:real^N,rr x) /\ ~((u:real^N->real^K) z = ww x z)} UNION
                    {z | z IN ball(y:real^N,rr y) /\ ~((u:real^N->real^K) z = ww y z)}` THEN
        ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_INTER] THEN MESON_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. x IN s /\ z IN ball(x,rr x)
          ==> (ww:real^N->real^N->real^K) z z = ww x z`
  (LABEL_TAC "EQW") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^N) IN s`)) THEN
    USE_THEN "AGR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  EXISTS_TAC `\z. (ww:real^N->real^N->real^K) z z` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`(ww:real^N->real^N->real^K) x`; `(rr:real^N->real) x`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "EQW" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `!y. y IN ball(x:real^N,rr x)
                        ==> (ww:real^N->real^N->real^K) x continuous at y`
      MP_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. ball(x,rr x)) s` LINDELOF) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\b. {z | z IN b /\
                                     ~((u:real^N->real^K) z = ww z z)}) f)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `b:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x. x IN s /\ b = ball(x:real^N,rr x)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET IMAGE (\x. ball(x,rr x)) s` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{z | z IN ball(x:real^N,rr x) /\ ~((u:real^N->real^K) z = ww x z)}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((u:real^N->real^K) z = ww z z)` THEN
    USE_THEN "EQW" (MP_TAC o SPECL [`x:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN BETA_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS f` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
    EXISTS_TAC `ball(z:real^N,rr z)` THEN CONJ_TAC THENL
     [EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
      USE_THEN "LOC" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^N) IN s`)) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  EXISTS_TAC `{z | z IN b /\ ~((u:real^N->real^K) z = ww z z)}` THEN
  CONJ_TAC THENL [EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* ========================================================================= *)
(* The continuous representative of a minimizer, its values in S, and the    *)
(* assembly with CM_REG01_STATEMENT.                                         *)
(* ========================================================================= *)

let HMRM_CONT_REP = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ bounded s /\ cm_minimizer S G s u
     ==> ?w. w continuous_on s /\ negligible {x | x IN s /\ ~(u x = w x)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LC")) o
              MATCH_MP HMRM_LOCAL_CONT) THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  MATCH_MP_TAC HMRM_GLUE_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `eps0:real`] HMRM_SMALL_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "LC" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `x:real^2`; `R0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`R0 / &8`; `w:real^2->real^K`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,R0)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,R0 / &8)` THEN
  REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC);;

(* A continuous map equal a.e. on an open set s to a map with values in the *)
(* closed set S takes values in S everywhere on s.                           *)

let HMRM_CONT_AE_IN = prove
 (`!(S:real^K->bool) (s:real^N->bool) (u:real^N->real^K) w Z.
     closed S /\ open s /\ w continuous_on s /\ negligible Z /\
     (!x. x IN s DIFF Z ==> u x IN S) /\ negligible {x | x IN s /\ ~(u x = w x)}
     ==> !x. x IN s ==> w x IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x | x IN s /\ ~((w:real^N->real^K) x IN S)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w:real^N->real^K`; `s:real^N->bool`; `(:real^K) DIFF S`]
                  CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible {x | x IN s /\ ~((w:real^N->real^K) x IN S)}` ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `Z UNION {x | x IN s /\ ~((u:real^N->real^K) x = w x)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN Z` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((w:real^N->real^K) x IN S)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN s /\ ~((w:real^N->real^K) x IN S)} = {}` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{x | x IN s /\ ~((w:real^N->real^K) x IN S)}` OPEN_NOT_NEGLIGIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SET_TAC[]);;

let HMRM_MINIMIZER_SMOOTH = prove
 (`!kk:K->bool. CM_REG01_STATEMENT kk ==> CM_MINIMIZER_SMOOTH_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_REG01_STATEMENT; CM_MINIMIZER_SMOOTH_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "REG") THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                 `u:real^2->real^K`] HMRM_CONT_REP) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cm_minimizer S G (ball(a:real^2,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_MINIMIZER_AE THEN EXISTS_TAC `u:real^2->real^K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) ==> (w:real^2->real^K) x IN S` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?Z. negligible Z /\ !x. x IN ball(a:real^2,r) DIFF Z ==> (u:real^2->real^K) x IN S`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
    MATCH_MP_TAC HMRM_CONT_AE_IN THEN
    MAP_EVERY EXISTS_TAC [`u:real^2->real^K`; `Z:real^2->bool`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ASSUME `cm_target S (G:real^K->real^K^K) d`) THEN REWRITE_TAC[cm_target] THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                 `w:real^2->real^K`] HMRM_CONT_MIN_WHARMONIC) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN DISCH_TAC THEN
  USE_THEN "REG" (MP_TAC o C MATCH_MP (ASSUME `cm_target S (G:real^K->real^K^K) d`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL]);;

