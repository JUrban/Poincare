(* ========================================================================= *)
(* Unit pc_hm_reg_hold (a unit of the harmonic map regularity chain of       *)
(* pc_hm_regularity): local Hoelder classes on open sets of real^N.          *)
(* hmrh_hol s al f: every point of s has a ball in s on which f is           *)
(* al-Hoelder.  hmrh_hk k s al f: f is C^k with all partial derivatives of   *)
(* order k in hmrh_hol (defined recursively through the first partials).     *)
(* Closure under sums, products, components, pastecart and smooth            *)
(* compositions, and the relation with wan_ckal.                             *)
(* ========================================================================= *)

needs "src/pc_wan_p4defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The definitions and the order-zero class.                                 *)
(* ------------------------------------------------------------------------- *)

let hmrh_hol = new_definition
 `hmrh_hol (s:real^N->bool) al (f:real^N->real^M) <=>
    !a. a IN s ==> ?r L. &0 < r /\ ball(a,r) SUBSET s /\
                         !x y. x IN ball(a,r) /\ y IN ball(a,r)
                               ==> norm(f x - f y) <= L * norm(x - y) rpow al`;;

let hmrh_hk = define
 `(hmrh_hk 0 s al (f:real^N->real^M) <=> f continuous_on s /\ hmrh_hol s al f) /\
  (!k. hmrh_hk (SUC k) s al (f:real^N->real^M) <=>
       continuously_differentiable 1 s f /\
       !i. 1 <= i /\ i <= dimindex(:N) ==> hmrh_hk k s al (partial_derivative i f))`;;

let HMRH_HOL_SUBSET = prove
 (`!(s:real^N->bool) t al (f:real^N->real^M).
     hmrh_hol s al f /\ open t /\ t SUBSET s ==> hmrh_hol t al f`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^N) IN s` (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min r e`; `L:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,e)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_MIN_MIN]]);;

let HMRH_HOL_EQ = prove
 (`!(s:real^N->bool) al (f:real^N->real^M) g.
     (!x. x IN s ==> f x = g x) /\ hmrh_hol s al f ==> hmrh_hol s al g`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `L:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->real^M) x = f x /\ g y = f y` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]]);;

let HMRH_HOL_CONST = prove
 (`!(s:real^N->bool) al (c:real^M).
     open s ==> hmrh_hol s al (\x. c)`,
  REWRITE_TAC[hmrh_hol; VECTOR_SUB_REFL; NORM_0] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `&0`] THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]);;

let HMRH_HOL_ADD = prove
 (`!(s:real^N->bool) al (f:real^N->real^M) g.
     hmrh_hol s al f /\ hmrh_hol s al g ==> hmrh_hol s al (\x. f x + g x)`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `L1:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `L2:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`min r1 r2`; `L1 + L2`] THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,r1)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,r1) /\ x IN ball(a,r2) /\
                (y:real^N) IN ball(a,r1) /\ y IN ball(a,r2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_MIN_MIN]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((f:real^N->real^M) x - f y) + norm((g:real^N->real^M) x - g y)` THEN
  CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[]);;

let HMRH_HOL_CMUL = prove
 (`!(s:real^N->bool) al (f:real^N->real^M) c.
     hmrh_hol s al f ==> hmrh_hol s al (\x. c % f x)`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `abs c * L`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_ABS_POS]);;

let HMRH_HOL_COMPONENT = prove
 (`!(s:real^N->bool) al (f:real^N->real^M) k.
     hmrh_hol s al f ==> hmrh_hol s al (\x. lift(f x$k))`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `L:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((f:real^N->real^M) x - f y)` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM]);;

let HMRH_HOL_PASTECART = prove
 (`!(s:real^N->bool) al (f:real^N->real^M) (g:real^N->real^P).
     hmrh_hol s al f /\ hmrh_hol s al g ==> hmrh_hol s al (\x. pastecart (f x) (g x))`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `L1:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `L2:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`min r1 r2`; `L1 + L2`] THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,r1)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,r1) /\ x IN ball(a,r2) /\
                (y:real^N) IN ball(a,r1) /\ y IN ball(a,r2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SUBSET_BALL; REAL_MIN_MIN]; ALL_TAC] THEN
  REWRITE_TAC[PASTECART_SUB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((f:real^N->real^M) x - f y) + norm((g:real^N->real^P) x - g y)` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* C^1 maps are locally Lipschitz and locally Hoelder; compositions and      *)
(* products in the order-zero class.                                         *)
(* ========================================================================= *)

let HMRH_LINEAR_BASIS_BOUND = prove
 (`!(f:real^M->real^N) x.
     linear f ==> norm(f x) <= sum(1..dimindex(:M)) (\j. norm(f(basis j))) * norm x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[COMPONENT_LE_NORM; NORM_POS_LE]);;

let HMRH_C1_LOCLIP = prove
 (`!(W:real^M->bool) (Phi:real^M->real^P) b.
     open W /\ continuously_differentiable 1 W Phi /\ b IN W
     ==> ?d B. &0 < d /\ ball(b,d) SUBSET W /\
               !y z. y IN ball(b,d) /\ z IN ball(b,d)
                     ==> norm(Phi y - Phi z) <= B * norm(y - z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `b:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN W ==> (Phi:real^M->real^P) differentiable (at x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `W:real^M->bool`; `Phi:real^M->real^P`]
      CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. (\x. frechet_derivative (Phi:real^M->real^P) (at x) (basis j))
                    continuous_on W` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `W:real^M->bool`; `Phi:real^M->real^P`]
      CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; CONTINUOUSLY_DIFFERENTIABLE_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bounded (IMAGE (\z. lift(sum(1..dimindex(:M))
                     (\j. norm(frechet_derivative (Phi:real^M->real^P) (at z) (basis j)))))
                   (cball(b,d)))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(b:real^M,d)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\x. frechet_derivative (Phi:real^M->real^P) (at x)` THEN
  REWRITE_TAC[CONVEX_BALL] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN cball(b,d) /\ x IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Phi:real^M->real^P) (at x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (Phi:real^M->real^P) (at x)` ONORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^M` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M))
                (\j. norm(frechet_derivative (Phi:real^M->real^P) (at x) (basis j))) *
              norm(v:real^M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMRH_LINEAR_BASIS_BOUND THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let HMRH_HOL_C1 = prove
 (`!(s:real^N->bool) al (f:real^N->real^M).
     open s /\ continuously_differentiable 1 s f /\ &0 < al /\ al <= &1
     ==> hmrh_hol s al f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrh_hol] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^M`; `a:real^N`] HMRH_C1_LOCLIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`min d (&1 / &2)`; `abs B`] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,d)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,d) /\ (y:real^N) IN ball(a,d) /\ norm(x - y) <= &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,min d (&1 / &2))` THEN
    UNDISCH_TAC `(y:real^N) IN ball(a,min d (&1 / &2))` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs B * norm(x - y:real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(x - y:real^N)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_CASES_TAC `x:real^N = y` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x - y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `t = t pow 1`] THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN MATCH_MP_TAC RPOW_MONO_INV THEN ASM_REWRITE_TAC[]);;

let HMRH_HOL_COMPOSE = prove
 (`!(s:real^N->bool) (W:real^M->bool) al (g:real^N->real^M) (Phi:real^M->real^P).
     open s /\ open W /\ g continuous_on s /\ (!x. x IN s ==> g x IN W) /\
     hmrh_hol s al g /\ continuously_differentiable 1 W Phi
     ==> hmrh_hol s al (\x. Phi(g x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "hg") ASSUME_TAC))))) THEN
  REWRITE_TAC[hmrh_hol] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  USE_THEN "hg" (MP_TAC o SPEC `a:real^N` o REWRITE_RULE[hmrh_hol]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`W:real^M->bool`; `Phi:real^M->real^P`; `(g:real^N->real^M) a`]
    HMRH_C1_LOCLIP) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^N->real^M) continuous (at a)` MP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min r rho`; `abs B * L`] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,r) /\ (y:real^N) IN ball(a,r) /\
                (g:real^N->real^M) x IN ball(g a,d) /\ g y IN ball(g a,d)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,min r rho)` THEN
    UNDISCH_TAC `(y:real^N) IN ball(a,min r rho)` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs B * norm((g:real^N->real^M) x - g y)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm((g:real^N->real^M) x - g y)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS]]);;

let HMRH_HOL_MUL = prove
 (`!(s:real^N->bool) al (c:real^N->real^1) (f:real^N->real^M).
     open s /\ c continuous_on s /\ f continuous_on s /\ hmrh_hol s al c /\ hmrh_hol s al f
     ==> hmrh_hol s al (\x. drop(c x) % f x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hc") (LABEL_TAC "hf"))))) THEN
  REWRITE_TAC[hmrh_hol] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  USE_THEN "hc" (MP_TAC o SPEC `a:real^N` o REWRITE_RULE[hmrh_hol]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `L1:real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "hf" (MP_TAC o SPEC `a:real^N` o REWRITE_RULE[hmrh_hol]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `L2:real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?Bc. !x. x IN cball(a,e) ==> norm((c:real^N->real^1) x) <= Bc`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^N->real^1`; `cball(a:real^N,e)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Bf. !x. x IN cball(a,e) ==> norm((f:real^N->real^M) x) <= Bf`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^M`; `cball(a:real^N,e)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min e (min r1 r2)`; `abs Bc * L2 + abs Bf * L1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,e)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^N,e)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN ASM_SIMP_TAC[SUBSET_BALL; REAL_MIN_MIN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,r1) /\ (y:real^N) IN ball(a,r1) /\
                x IN ball(a,r2) /\ y IN ball(a,r2) /\ x IN cball(a,e) /\ y IN cball(a,e)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,min e (min r1 r2))` THEN
    UNDISCH_TAC `(y:real^N) IN ball(a,min e (min r1 r2))` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop((c:real^N->real^1) x) % (f:real^N->real^M) x - drop(c y) % f y =
                drop(c x) % (f x - f y) + (drop(c x) - drop(c y)) % f y` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(drop((c:real^N->real^1) x) % ((f:real^N->real^M) x - f y)) +
              norm((drop(c x) - drop(c y)) % f y)` THEN
  REWRITE_TAC[NORM_TRIANGLE] THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `abs(drop((c:real^N->real^1) x)) <= abs Bc /\
                abs(drop((c:real^N->real^1) x) - drop(c y)) <= L1 * norm(x - y) rpow al /\
                norm((f:real^N->real^M) x - f y) <= L2 * norm(x - y) rpow al /\
                norm((f:real^N->real^M) y) <= abs Bf`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_1; GSYM DROP_SUB] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[NORM_1; DROP_SUB] THEN REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1] THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs Bc * (L2 * norm(x - y:real^N) rpow al) +
              (L1 * norm(x - y:real^N) rpow al) * abs Bf` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Basic properties of hmrh_hk (open sets): continuity, subsets, congruence, *)
(* constants, sums, multiples, the inclusion hk (k + 1) in hk k, and C^k     *)
(* regularity.                                                               *)
(* ========================================================================= *)

let HMRH_C1_DIFF = prove
 (`!(s:real^N->bool) (f:real^N->real^M) x.
     open s /\ continuously_differentiable 1 s f /\ x IN s ==> f differentiable (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `s:real^N->bool`; `f:real^N->real^M`]
    CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT]);;

let HMRH_HK_CONT = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M). hmrh_hk k s al f ==> f continuous_on s`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON]);;

let HMRH_HK_SUBSET = prove
 (`!k (s:real^N->bool) t al (f:real^N->real^M).
     hmrh_hk k s al f /\ open t /\ t SUBSET s ==> hmrh_hk k t al f`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_MESON_TAC[HMRH_HOL_SUBSET];
    ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]]);;

let HMRH_HK_EQ = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) g.
     open s /\ (!x. x IN s ==> f x = g x) /\ hmrh_hk k s al f ==> hmrh_hk k s al g`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ];
    ASM_MESON_TAC[HMRH_HOL_EQ];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN EXISTS_TAC `f:real^N->real^M` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `partial_derivative i (f:real^N->real^M)` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let HMRH_HK_CONST = prove
 (`!k (s:real^N->bool) al (c:real^M). open s ==> hmrh_hk k s al (\x. c)`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CONST];
    ASM_SIMP_TAC[HMRH_HOL_CONST];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST];
    SUBGOAL_THEN `partial_derivative i ((\x. c):real^N->real^M) = (\x. vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; PARTIAL_DERIVATIVE_CONST]; ASM_SIMP_TAC[]]]);;

let HMRH_HK_ADD = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) g.
     open s /\ hmrh_hk k s al f /\ hmrh_hk k s al g ==> hmrh_hk k s al (\x. f x + g x)`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_ADD];
    ASM_SIMP_TAC[HMRH_HOL_ADD];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN];
    MATCH_MP_TAC HMRH_HK_EQ THEN
    EXISTS_TAC `\x. partial_derivative i (f:real^N->real^M) x + partial_derivative i g x` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN ASM_MESON_TAC[HMRH_C1_DIFF];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]]);;

let HMRH_HK_CMUL = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) c.
     open s /\ hmrh_hk k s al f ==> hmrh_hk k s al (\x. c % f x)`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_CMUL];
    ASM_SIMP_TAC[HMRH_HOL_CMUL];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN];
    MATCH_MP_TAC HMRH_HK_EQ THEN
    EXISTS_TAC `\x. c % partial_derivative i (f:real^N->real^M) x` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_CMUL THEN ASM_MESON_TAC[HMRH_C1_DIFF];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]]);;

let HMRH_HK_SUB = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) g.
     open s /\ hmrh_hk k s al f /\ hmrh_hk k s al g ==> hmrh_hk k s al (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^M) x - g x) = (\x. f x + --(&1) % g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_ADD THEN ASM_SIMP_TAC[HMRH_HK_CMUL]);;

let HMRH_CD_SUC = prove
 (`!n (s:real^N->bool) (f:real^N->real^M).
     open s /\ continuously_differentiable 1 s f /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> continuously_differentiable n s (partial_derivative i f))
     ==> continuously_differentiable (SUC n) s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  EXISTS_TAC `\x. frechet_derivative (f:real^N->real^M) (at x)` THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_MESON_TAC[HMRH_C1_DIFF];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^N` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N))
                    (\i. (h:real^N)$i % partial_derivative i (f:real^N->real^M) x)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `linear(frechet_derivative (f:real^N->real^M) (at x))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[HMRH_C1_DIFF]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN ASM_SIMP_TAC[ETA_AX]]);;

let HMRH_HK_MONO = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M).
     open s /\ &0 < al /\ al <= &1 /\ hmrh_hk (SUC k) s al f ==> hmrh_hk k s al f`,
  INDUCT_TAC THENL
   [REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON];
      MATCH_MP_TAC HMRH_HOL_C1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let HMRH_HK_CD = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M).
     open s /\ hmrh_hk k s al f ==> continuously_differentiable k s f`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk; CONTINUOUSLY_DIFFERENTIABLE_0] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMRH_CD_SUC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `al:real` THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Components, pastecart, products, finite sums, smooth compositions and     *)
(* componentwise assembly in hmrh_hk.                                        *)
(* ========================================================================= *)

let HMRH_PD_PASTECART = prove
 (`!i (f:real^N->real^M) (g:real^N->real^P) x.
     f differentiable (at x) /\ g differentiable (at x)
     ==> partial_derivative i (\x. pastecart (f x) (g x)) x =
         pastecart (partial_derivative i f x) (partial_derivative i g x)`,
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  MP_TAC(ISPECL [`at (x:real^N)`; `f:real^N->real^M`; `g:real^N->real^P`;
                 `frechet_derivative (f:real^N->real^M) (at x)`;
                 `frechet_derivative (g:real^N->real^P) (at x)`] HAS_DERIVATIVE_PASTECART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

let HMRH_HK_COMPONENT = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) j.
     open s /\ hmrh_hk k s al f ==> hmrh_hk k s al (\x. lift(f x$j))`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE];
    ASM_SIMP_TAC[HMRH_HOL_COMPONENT];
    SUBGOAL_THEN `(\x. lift((f:real^N->real^M) x$j)) = (\y:real^M. lift(y$j)) o f`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    MATCH_MP_TAC HMRH_HK_EQ THEN
    EXISTS_TAC `\x. lift(partial_derivative i (f:real^N->real^M) x$j)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_COMPONENT THEN ASM_MESON_TAC[HMRH_C1_DIFF];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]]);;

let HMRH_HK_PASTECART = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) (g:real^N->real^P).
     open s /\ hmrh_hk k s al f /\ hmrh_hk k s al g
     ==> hmrh_hk k s al (\x. pastecart (f x) (g x))`,
  INDUCT_TAC THEN REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART];
    ASM_SIMP_TAC[HMRH_HOL_PASTECART];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN];
    MATCH_MP_TAC HMRH_HK_EQ THEN
    EXISTS_TAC `\x. pastecart (partial_derivative i (f:real^N->real^M) x)
                              (partial_derivative i (g:real^N->real^P) x)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC HMRH_PD_PASTECART THEN ASM_MESON_TAC[HMRH_C1_DIFF];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]]);;

let HMRH_HK_MUL = prove
 (`!k (s:real^N->bool) al (c:real^N->real^1) (f:real^N->real^M).
     open s /\ &0 < al /\ al <= &1 /\ hmrh_hk k s al c /\ hmrh_hk k s al f
     ==> hmrh_hk k s al (\x. drop(c x) % f x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
      MATCH_MP_TAC HMRH_HOL_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hmrh_hk k s al (c:real^N->real^1) /\ hmrh_hk k s al (f:real^N->real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMRH_HK_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `hmrh_hk (SUC k) s al (c:real^N->real^1)` THEN
  UNDISCH_TAC `hmrh_hk (SUC k) s al (f:real^N->real^M)` THEN
  REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HMRH_HK_EQ THEN
    EXISTS_TAC `\x. drop((c:real^N->real^1) x) % partial_derivative i (f:real^N->real^M) x +
                    drop(partial_derivative i c x) % f x` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_MUL THEN ASM_MESON_TAC[HMRH_C1_DIFF];
      MATCH_MP_TAC HMRH_HK_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]]]);;

let HMRH_HK_VSUM = prove
 (`!k (s:real^N->bool) al (f:num->real^N->real^M) n.
     open s /\ (!m. 1 <= m /\ m <= n ==> hmrh_hk k s al (f m))
     ==> hmrh_hk k s al (\x. vsum(1..n) (\m. f m x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN SIMP_TAC[HMRH_HK_CONST];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC HMRH_HK_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m <= SUC n`];
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let HMRH_HK_COMPOSE = prove
 (`!k (s:real^N->bool) al (W:real^M->bool) (g:real^N->real^M) (Phi:real^M->real^P).
     open s /\ &0 < al /\ al <= &1 /\ open W /\ (!x. x IN s ==> g x IN W) /\
     smooth_map_on W Phi /\ hmrh_hk k s al g
     ==> hmrh_hk k s al (\x. Phi(g x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[hmrh_hk] THEN REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `(\x. (Phi:real^M->real^P)((g:real^N->real^M) x)) = Phi o g`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^M->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[];
      MATCH_MP_TAC HMRH_HOL_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `smooth_map_on W (Phi:real^M->real^P)` THEN SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hmrh_hk k s al (g:real^N->real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRH_HK_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `hmrh_hk (SUC k) s al (g:real^N->real^M)` THEN REWRITE_TAC[hmrh_hk] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (Phi:real^M->real^P)((g:real^N->real^M) x)) = Phi o g`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `W:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `smooth_map_on W (Phi:real^M->real^P)` THEN SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC HMRH_HK_EQ THEN
  EXISTS_TAC
   `\x. vsum(1..dimindex(:M))
          (\m. drop(lift(partial_derivative i (g:real^N->real^M) x$m)) %
               partial_derivative m (Phi:real^M->real^P) (g x))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `(\x. (Phi:real^M->real^P)((g:real^N->real^M) x)) = Phi o g`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN `(Phi:real^M->real^P) differentiable (at ((g:real^N->real^M) x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^M->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`i:num`; `g:real^N->real^M`; `Phi:real^M->real^P`; `x:real^N`]
      PARTIAL_DERIVATIVE_CHAIN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HMRH_C1_DIFF]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (Phi:real^M->real^P) (at ((g:real^N->real^M) x)))`
    ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative];
    MATCH_MP_TAC HMRH_HK_VSUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HMRH_HK_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRH_HK_COMPONENT THEN ASM_SIMP_TAC[ETA_AX];
      USE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `W:real^M->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]]);;

let HMRH_HK_COMPONENTWISE = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M).
     open s /\ &0 < al /\ al <= &1 /\
     (!j. 1 <= j /\ j <= dimindex(:M) ==> hmrh_hk k s al (\x. lift(f x$j)))
     ==> hmrh_hk k s al f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = (\x:real^N. vsum(1..dimindex(:M))
                       (\j. drop(lift((f:real^N->real^M) x$j)) % basis j))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; BASIS_EXPANSION]; ALL_TAC] THEN
  MATCH_MP_TAC HMRH_HK_VSUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC HMRH_HK_MUL THEN ASM_SIMP_TAC[HMRH_HK_CONST]);;

(* ========================================================================= *)
(* Iterated partials of hmrh_hk maps, the passage to wan_ckal bounds on      *)
(* small balls, and back.                                                    *)
(* ========================================================================= *)

let HMRH_HK_ITERATED = prove
 (`!l k (s:real^N->bool) al (f:real^N->real^M).
     hmrh_hk k s al f /\ LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> hmrh_hk (k - LENGTH l) s al (iterated_partial l f)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ALL; iterated_partial; SUB_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `s:real^N->bool`; `al:real`; `f:real^N->real^M`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k - LENGTH(t:num list) = SUC(k - SUC(LENGTH t))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[hmrh_hk] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let HMRH_FINITE_MIN_INV = prove
 (`!(t:A->bool) (R:A->real).
     FINITE t /\ (!x. x IN t ==> &0 < R x)
     ==> &0 < inv(&1 + sum t (\x. inv(R x))) /\
         !x. x IN t ==> inv(&1 + sum t (\x. inv(R x))) <= R x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum t (\x. inv((R:A->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
  MP_TAC(ISPECL [`\x. inv((R:A->real) x)`; `sum t (\x. inv((R:A->real) x))`; `t:A->bool`]
    SUM_POS_BOUND) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let HMRH_HK_CKAL = prove
 (`!k (s:real^N->bool) al (f:real^N->real^M) a.
     open s /\ hmrh_hk k s al f /\ a IN s /\ &0 < al
     ==> ?r A. &0 < r /\ r <= &1 /\ cball(a,r) SUBSET s /\
               wan_ckal (ball(a,r)) k al r f A`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `T0 = pde_index_lists k (:N)` THEN
  ABBREV_TAC `T1 = {l:num list | l IN T0 /\ LENGTH l = k}` THEN
  SUBGOAL_THEN `FINITE(T0:num list->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `(T1:num list->bool) SUBSET T0` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(T1:num list->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!l:num list. l IN T0
                ==> LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM]; ALL_TAC] THEN
  (* bounds of the derivatives up to order k on the closed ball *)
  SUBGOAL_THEN
   `!l:num list. ?B. l IN T0 ==> !x. x IN cball(a,r0)
                                      ==> norm(iterated_partial l (f:real^N->real^M) x) <= B`
  MP_TAC THENL
   [X_GEN_TAC `l:num list` THEN ASM_CASES_TAC `(l:num list) IN T0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`iterated_partial l (f:real^N->real^M)`; `cball(a:real^N,r0)`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HMRH_HK_CONT THEN
      MAP_EVERY EXISTS_TAC [`k - LENGTH(l:num list)`; `al:real`] THEN
      MATCH_MP_TAC HMRH_HK_ITERATED THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `B:num list->real`) THEN
  (* Hoelder radii and constants for the top derivatives *)
  SUBGOAL_THEN
   `!l:num list. ?rl Ll. l IN T1
                 ==> &0 < rl /\ ball(a,rl) SUBSET s /\
                     !x y. x IN ball(a,rl) /\ y IN ball(a,rl)
                           ==> norm(iterated_partial l (f:real^N->real^M) x -
                                    iterated_partial l f y) <= Ll * norm(x - y) rpow al`
  MP_TAC THENL
   [X_GEN_TAC `l:num list` THEN ASM_CASES_TAC `(l:num list) IN T1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(l:num list) IN T0 /\ LENGTH l = k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(l:num list) IN T1` THEN EXPAND_TAC "T1" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:num list`; `k:num`; `s:real^N->bool`; `al:real`; `f:real^N->real^M`]
      HMRH_HK_ITERATED) THEN
    ASM_SIMP_TAC[SUB_REFL; LE_REFL] THEN REWRITE_TAC[hmrh_hk; hmrh_hol] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `RR:num list->real` (X_CHOOSE_TAC `LL:num list->real`)) THEN
  MP_TAC(ISPECL [`T1:num list->bool`; `RR:num list->real`] HMRH_FINITE_MIN_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r1 = inv(&1 + sum T1 (\l. inv((RR:num list->real) l)))` THEN STRIP_TAC THEN
  EXISTS_TAC `min (min r0 (&1)) r1` THEN
  EXISTS_TAC `sum T0 (\l. abs((B:num list->real) l)) + sum T1 (\l. abs((LL:num list->real) l))` THEN
  SUBGOAL_THEN `&0 < min (min r0 (&1)) r1 /\ min (min r0 (&1)) r1 <= &1 /\
                min (min r0 (&1)) r1 <= r0 /\ min (min r0 (&1)) r1 <= r1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = min (min r0 (&1)) r1` THEN
  SUBGOAL_THEN `&0 <= sum T0 (\l. abs((B:num list->real) l)) /\
                &0 <= sum T1 (\l. abs((LL:num list->real) l))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,r0)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[wan_ckal] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(l:num list) IN T0` ASSUME_TAC THENL
     [EXPAND_TAC "T0" THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * abs((B:num list->real) l)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `l:num list` o check (fun th ->
          can (find_term (fun t -> t = `B:num list->real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `(x:real^N) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\l. abs((B:num list->real) l)`; `sum T0 (\l. abs((B:num list->real) l))`;
                     `T0:num list->bool`] SUM_POS_BOUND) THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:num list) IN T1` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN EXPAND_TAC "T0" THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num list` o check (fun th ->
    can (find_term (fun t -> t = `RR:num list->real`)) (concl th) &&
    can (find_term (fun t -> t = `LL:num list->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r <= (RR:num list->real) l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r1:real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN ball(a,RR(l:num list)) /\ (y:real^N) IN ball(a,RR l)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,r)` THEN UNDISCH_TAC `(y:real^N) IN ball(a,r)` THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&k + al) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((LL:num list->real) l) <= sum T1 (\l. abs((LL:num list->real) l))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\l. abs((LL:num list->real) l)`; `sum T1 (\l. abs((LL:num list->real) l))`;
                   `T1:num list->bool`] SUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * ((LL:num list->real) l * norm(x - y:real^N) rpow al)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; NORM_POS_LE];
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC]);;

(* Back from wan_ckal: the top derivatives are Hoelder on the whole set. *)

let HMRH_CKAL_HOL = prove
 (`!(t:real^N->bool) m al r (w:real^N->real^M) A l.
     open t /\ &0 < r /\ wan_ckal t m al r w A /\
     LENGTH l = m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> hmrh_hol t al (iterated_partial l w)`,
  REWRITE_TAC[wan_ckal; hmrh_hol] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < r rpow (&m + al)` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `A / r rpow (&m + al)`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A / r rpow (&m + al)) * norm(x - y:real^N) rpow al =
                (A * norm(x - y) rpow al) / r rpow (&m + al)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `b * a <= c ==> a * b <= c`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let HMRH_HK_FROM_HOL = prove
 (`!m (t:real^N->bool) al (w:real^N->real^M).
     open t /\ continuously_differentiable m t w /\
     (!l. LENGTH l = m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
          ==> hmrh_hol t al (iterated_partial l w))
     ==> hmrh_hk m t al w`,
  INDUCT_TAC THENL
   [REWRITE_TAC[hmrh_hk; CONTINUOUSLY_DIFFERENTIABLE_0] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
    REWRITE_TAC[LENGTH; ALL; iterated_partial];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrh_hk] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC m` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
    MP_TAC(ISPECL [`m:num`; `t:real^N->bool`; `w:real^N->real^M`]
      CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
    SUBGOAL_THEN `iterated_partial l (partial_derivative i (w:real^N->real^M)) =
                  iterated_partial (APPEND l [i]) w` SUBST1_TAC THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ARITH_TAC]);;

let HMRH_HOL_UNIFORM = prove
 (`!(t:real^N->bool) al (f:real^N->real^M) L.
     open t /\ (!x y. x IN t /\ y IN t ==> norm(f x - f y) <= L * norm(x - y) rpow al)
     ==> hmrh_hol t al f`,
  REWRITE_TAC[hmrh_hol] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `L:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

