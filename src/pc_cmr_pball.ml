(* ========================================================================= *)
(* Unit pc_cmr_pball (a unit of the replacement chain of pc_cm_replacement): *)
(* the per-ball comparison of CM Lemma 3.11, step (3.24), with the harmonic  *)
(* (Poisson) extension in place of CM Lemma 3.14.  For maps v, v1 of small   *)
(* energy on a disc B_R that agree at some point of every circle of radius   *)
(* in (R/2,R) and whose difference has small Dirichlet energy, there is a    *)
(* radius rho in (R/2,R) with                                                *)
(*   E(v1,B_rho) - E(H(v,B_rho)) <= E(v1,B_R) - E(H(v1,B_R)) + Cp sqrt(X Y)  *)
(* where X = dir(v) + dir(v1) and Y = dir(v1 - v) on B_R.  The competitor   *)
(* for H(v1,B_R) is v1 off B_rho and Pg(H(v,B_rho) + h) on B_rho, where h is *)
(* the harmonic extension of v1 - v from a good circle (WAN_POISSON_ENERGY, *)
(* the maximum principle, the oscillation bound on almost every circle) and *)
(* Pg is the extension of the closest-point map with the energy estimate    *)
(* HMD_COMPETITOR_ENERGY of pc_hm_dirichlet.                                 *)
(*                                                                           *)
(* A good circle.  For f in W^{1,2}(B_R), almost every circle                *)
(* of radius r carries the angular derivative of f (WAN_CIRCLE_ACL) and the *)
(* oscillation bound (WAN_CIRCLE_OSC_AE); by the polar formula               *)
(* (WAN_POLAR_DIR) and averaging, some r in (R/2,R) has angular energy at   *)
(* most 4 dir(f) and squared oscillation at most 2 pi dir(f).               *)
(* ========================================================================= *)

needs "src/pc_cmr_l311.ml";;
needs "src/pc_wan_lap2e.ml";;
needs "src/pc_hm_dirichlet.ml";;

prioritize_real();;
type_invention_error := true;;

(* The angular derivative of f along the circle of radius rho.             *)

let cmr_cder = new_definition
 `cmr_cder (c:real^2) R rho (f:real^2->real^K) (s:real) =
    rho % (--(sin s) % wan_wd (ball(c,R)) 1 f (wan_circ c rho s) +
           cos s % wan_wd (ball(c,R)) 2 f (wan_circ c rho s))`;;

(* A nonnegative integrable function on (a,b) is at most twice its average  *)
(* somewhere off a given negligible set.                                    *)

let CMR_AVG_POINT = prove
 (`!(f:real->real) a b M S.
     a < b /\ negligible S /\
     (!x. a <= x /\ x <= b /\ ~(lift x IN S) ==> &0 <= f x) /\
     (\x. lift(f(drop x))) integrable_on interval[lift a,lift b] /\
     drop(integral (interval[lift a,lift b]) (\x. lift(f(drop x)))) <= M
     ==> ?x. a < x /\ x < b /\ ~(lift x IN S) /\ (b - a) * f x <= &2 * M`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?x:real. P x) <=> ~(!x. ~P x)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. a < x /\ x < b /\ ~(lift x IN S) ==> &2 * M < (b - a) * f x`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_NOT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Z = S UNION {lift a,lift b}` THEN
  SUBGOAL_THEN `negligible(Z:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_INSERT;
                                        NEGLIGIBLE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN interval[lift a,lift b] DIFF Z
        ==> a < drop x /\ drop x < b /\ ~(lift(drop x) IN S)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN EXPAND_TAC "Z" THEN
    REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_UNION; IN_INSERT; NOT_IN_EMPTY; LIFT_DROP;
                DE_MORGAN_THM] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN interval[lift a,lift b] DIFF Z ==> &0 <= f(drop x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= drop(integral (interval[lift a,lift b]) (\x. lift(f(drop x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS_AE THEN
    EXISTS_TAC `Z:real^1->bool` THEN ASM_SIMP_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * M <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (interval[lift a,lift b]) (\x. lift(f(drop x))))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * M = drop(integral (interval[lift a,lift b])
                                  (\x:real^1. lift((&2 * M) / (b - a))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTEGRAL_CONST] THEN
      SIMP_TAC[CONTENT_1; LIFT_DROP; DROP_CMUL; ASSUME `a < b`; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `Z:real^1->bool` THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1` o check (is_conj o rand o snd o strip_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop x`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integral (interval[lift a,lift b]) (\x. lift(f(drop x))) = vec 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `g = \x:real^1. if x IN Z then vec 0 else lift(f(drop x))` THEN
  SUBGOAL_THEN `((g:real^1->real^1) has_integral vec 0) (interval[lift a,lift b])` MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
    EXISTS_TAC `\x:real^1. lift(f(drop x))` THEN EXISTS_TAC `Z:real^1->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "g" THEN SIMP_TAC[IN_DIFF];
      SUBST1_TAC(SYM(ASSUME
        `integral (interval[lift a,lift b]) (\x. lift(f(drop x))) = vec 0`)) THEN
      MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x i. x IN interval[lift a,lift b] /\ 1 <= i /\ i <= dimindex(:1)
          ==> &0 <= (g:real^1->real^1) x$i`
  ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "g" THEN COND_CASES_TAC THEN REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL] THEN
    REWRITE_TAC[LIFT_COMPONENT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_NEGLIGIBLE_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `negligible(interval(lift a,lift b))` MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `Z UNION {x | x IN interval[lift a,lift b] /\ ~((g:real^1->real^1) x = vec 0)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^1) IN Z` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x IN interval[lift a,lift b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
    SUBGOAL_THEN `a < drop x /\ drop x < b /\ ~(lift(drop x) IN S)` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_conj o rand o snd o strip_forall o concl)) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      ALL_TAC] THEN
    UNDISCH_TAC `!x. a < x /\ x < b /\ ~(lift x IN S) ==> &2 * &0 < (b - a) * f x` THEN
    DISCH_THEN(MP_TAC o SPEC `drop x`) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* |a X + b Y|^2 <= (a^2 + b^2)(|X|^2 + |Y|^2).                            *)

let CMR_COMB_NORM_LE = prove
 (`!a b (X:real^N) Y.
     norm(a % X + b % Y) pow 2 <= (a pow 2 + b pow 2) * (norm X pow 2 + norm Y pow 2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `norm(a % X + b % Y) pow 2 + norm(b % X - a % (Y:real^N)) pow 2 =
    (a pow 2 + b pow 2) * (norm X pow 2 + norm Y pow 2)`
  MP_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `norm(b % X - a % (Y:real^N))` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let CMR_CDER_BOUND = prove
 (`!(c:real^2) R rho (f:real^2->real^K) s.
     norm(cmr_cder c R rho f s) pow 2 <=
     rho pow 2 * (norm(wan_wd (ball(c,R)) 1 f (wan_circ c rho s)) pow 2 +
                  norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho s)) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_cder; NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MP_TAC(ISPECL [`--(sin s)`; `cos s`;
                 `wan_wd (ball(c:real^2,R)) 1 (f:real^2->real^K) (wan_circ c rho s)`;
                 `wan_wd (ball(c:real^2,R)) 2 (f:real^2->real^K) (wan_circ c rho s)`]
                CMR_COMB_NORM_LE) THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH; SIN_CIRCLE; REAL_MUL_LID]);;

(* The Dirichlet integral as one integral of |d1 f|^2 + |d2 f|^2.            *)

let CMR_DIR_AS_SUM = prove
 (`!(s:real^2->bool) (f:real^2->real^K).
     wan_w12 s f
     ==> (\x. lift(norm(wan_wd s 1 f x) pow 2 + norm(wan_wd s 2 f x) pow 2))
         absolutely_integrable_on s /\
         wan_dir s f =
         drop(integral s (\x. lift(norm(wan_wd s 1 f x) pow 2 + norm(wan_wd s 2 f x) pow 2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(norm(wan_wd s i (f:real^2->real^K) x) pow 2)) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `f:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_wd s 1 (f:real^2->real^K) x) pow 2)) integrable_on s /\
    (\x. lift(norm(wan_wd s 2 (f:real^2->real^K) x) pow 2)) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LIFT_COMPONENT] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2; LIFT_ADD] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD]]);;

(* A good circle.                                                            *)

let CMR_GOOD_CIRCLE = prove
 (`!(c:real^2) R (f:real^2->real^K).
     &0 < R /\ f continuous_on ball(c,R) /\ wan_w12 (ball(c,R)) f
     ==> ?rho. R / &2 < rho /\ rho < R /\
           (!t. &0 <= t /\ t <= &2 * pi
                ==> ((\s. cmr_cder c R rho f (drop s))
                     has_integral (f(wan_circ c rho t) - f(wan_circ c rho (&0))))
                    (interval[vec 0,lift t])) /\
           (\s. lift(norm(cmr_cder c R rho f (drop s)) pow 2))
           integrable_on interval[vec 0,lift(&2 * pi)] /\
           drop(integral (interval[vec 0,lift(&2 * pi)])
                  (\s. lift(norm(cmr_cder c R rho f (drop s)) pow 2)))
           <= &4 * wan_dir (ball(c,R)) f /\
           (!t1 t2. norm(f(wan_circ c rho t1) - f(wan_circ c rho t2)) pow 2
                    <= &2 * pi * wan_dir (ball(c,R)) f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2`; `R:real`; `f:real^2->real^K`]
         (REWRITE_RULE[WAN_CIRCLE_ACL_STATEMENT] (ISPEC `(:K)` WAN_CIRCLE_ACL))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S1:real^1->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^2`; `R:real`; `f:real^2->real^K`] WAN_CIRCLE_OSC_AE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S2:real^1->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^2`; `R:real`; `R / &2`; `R:real`; `f:real^2->real^K`]
         (REWRITE_RULE[WAN_POLAR_DIR_STATEMENT] (ISPEC `(:K)` WAN_POLAR_DIR))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
                  ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift(R / &2),lift R])
           (\r. lift(drop r *
                     drop(integral (interval[vec 0,lift(&2 * pi)])
                            (\t. lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K)
                                             (wan_circ c (drop r) (drop t))) pow 2 +
                                      norm(wan_wd (ball(c,R)) 2 f
                                             (wan_circ c (drop r) (drop t))) pow 2))))))
    <= wan_dir (ball(c,R)) f`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(c:real^2,R)`; `f:real^2->real^K`] CMR_DIR_AS_SUM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    SUBGOAL_THEN `{x | R / &2 < norm(x - c) /\ norm(x - c) < R} SUBSET ball(c:real^2,R)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL] THEN MESON_TAC[DIST_SYM; dist]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `ball(c:real^2,R)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
      ONCE_REWRITE_TAC[SET_RULE `{x:real^2 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:real^2`; `R / &2`] CLOSED_CBALL);
        MP_TAC(ISPECL [`c:real^2`; `R:real`] OPEN_BALL)] THEN
      REWRITE_TAC[closed; cball; ball; dist] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
      MESON_TAC[NORM_SUB; REAL_NOT_LE];
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ABBREV_TAC
   `Ic = \r. drop(integral (interval[vec 0,lift(&2 * pi)])
                    (\t. lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K)
                                    (wan_circ c r (drop t))) pow 2 +
                              norm(wan_wd (ball(c,R)) 2 f (wan_circ c r (drop t))) pow 2)))` THEN
  MP_TAC(ISPECL [`\r. r * (Ic:real->real) r`; `R / &2`; `R:real`;
                 `wan_dir (ball(c:real^2,R)) (f:real^2->real^K)`;
                 `S1 UNION S2 UNION {lift R}`] CMR_AVG_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_SING] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM; IN_SING; LIFT_EQ] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `R / &2 <= r` THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "Ic" THEN REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (is_conj o rand o snd o strip_forall o concl)) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [UNDISCH_TAC `R / &2 <= r` THEN UNDISCH_TAC `r <= R` THEN
          UNDISCH_TAC `~(r:real = R)` THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
          SIMP_TAC[]];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]];
      EXPAND_TAC "Ic" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Ic" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNION; DE_MORGAN_THM; IN_SING; LIFT_EQ] o
                check (is_neg o concl)) THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `R / &2 < rho` THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `rho:real` o
    check (fun th -> is_forall(concl th) && free_in `S1:real^1->bool` (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `rho:real` o
    check (fun th -> is_forall(concl th) && free_in `S2:real^1->bool` (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `(R - R / &2) * rho * (Ic:real->real) rho <=
               &2 * wan_dir (ball(c:real^2,R)) (f:real^2->real^K)` THEN
  EXPAND_TAC "Ic" THEN REWRITE_TAC[] THEN
  ABBREV_TAC
   `J = drop(integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K)
                               (wan_circ c rho (drop t))) pow 2 +
                         norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho (drop t))) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 2 * J <= &4 * wan_dir (ball(c:real^2,R)) (f:real^2->real^K)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= rho * J` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `rho * (rho * J) <= R * (rho * J)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rho < R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(R - R / &2) * rho * J <= &2 * wan_dir (ball(c:real^2,R)) (f:real^2->real^K)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. lift(norm(cmr_cder c R rho (f:real^2->real^K) (drop s)) pow 2))
    integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     `\s. rho pow 2 %
          lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K) (wan_circ c rho (drop s))) pow 2 +
               norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho (drop s))) pow 2)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[ARITH] THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `f(wan_circ c rho (&2 * pi)) - (f:real^2->real^K)(wan_circ c rho (&0))` THEN
      REWRITE_TAC[cmr_cder] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; DROP_CMUL; REAL_ABS_POW; REAL_ABS_NORM] THEN
      REWRITE_TAC[CMR_CDER_BOUND]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmr_cder] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho pow 2 * J` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)])
        (\s. rho pow 2 %
             lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K) (wan_circ c rho (drop s))) pow 2 +
                  norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho (drop s))) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; DROP_CMUL; CMR_CDER_BOUND] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `integral (interval[vec 0,lift(&2 * pi)])
          (\s. rho pow 2 %
               lift(norm(wan_wd (ball(c,R)) 1 (f:real^2->real^K) (wan_circ c rho (drop s))) pow 2 +
                    norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho (drop s))) pow 2)) =
        rho pow 2 %
        integral (interval[vec 0,lift(&2 * pi)])
          (\s. lift(norm(wan_wd (ball(c,R)) 1 f (wan_circ c rho (drop s))) pow 2 +
                    norm(wan_wd (ball(c,R)) 2 f (wan_circ c rho (drop s))) pow 2))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "J" THEN REWRITE_TAC[DROP_CMUL; REAL_LE_REFL]]];
    REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pi / &2 * rho pow 2 * J` THEN CONJ_TAC THENL
     [EXPAND_TAC "J" THEN ASM_REWRITE_TAC[];
      MP_TAC PI_POS THEN UNDISCH_TAC `rho pow 2 * J <= &4 * wan_dir (ball(c:real^2,R)) (f:real^2->real^K)` THEN
      ABBREV_TAC `D = wan_dir (ball(c:real^2,R)) (f:real^2->real^K)` THEN
      ABBREV_TAC `P = rho pow 2 * J` THEN
      SUBGOAL_THEN `pi / &2 * rho pow 2 * J = pi / &2 * P` SUBST1_TAC THENL
       [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `pi / &2 * P <= pi / &2 * (&4 * D)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < pi` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]);;


(* ========================================================================= *)
(* The harmonic extension of f from a good circle.  If f                     *)
(* vanishes somewhere on every circle of radius in (R/2,R), there is such a *)
(* radius rho and a harmonic h on the disc B_rho, continuous up to the      *)
(* boundary, equal to f on the circle, with                                 *)
(*   dir(h) <= 4 dir(f)  and  |h| <= sqrt(2 pi dir(f))                       *)
(* (WAN_POISSON_ENERGY; oscillation bound plus a zero; maximum principle).  *)
(* ========================================================================= *)

let CMR_CIRC_PERIODIC = prove
 (`!(c:real^2) r t. wan_circ c r (t + &2 * pi) = wan_circ c r t`,
  REWRITE_TAC[wan_circ; SIN_PERIODIC; COS_PERIODIC]);;

let CMR_CIRCLE_HARM = prove
 (`!(c:real^2) R (f:real^2->real^K).
     &0 < R /\ f continuous_on ball(c,R) /\ wan_w12 (ball(c,R)) f /\
     (!rho. R / &2 < rho /\ rho < R ==> ?x. x IN sphere(c,rho) /\ f x = vec 0)
     ==> ?rho h. R / &2 < rho /\ rho < R /\
                 h continuous_on cball(c,rho) /\
                 (!x. x IN sphere(c,rho) ==> h x = f x) /\
                 smooth_map_on (ball(c,rho)) h /\
                 wan_w12 (ball(c,rho)) h /\
                 wan_dir (ball(c,rho)) h <= &4 * wan_dir (ball(c,R)) f /\
                 (!x. x IN cball(c,rho)
                      ==> norm(h x) <= sqrt(&2 * pi * wan_dir (ball(c,R)) f))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2`; `R:real`; `f:real^2->real^K`] CMR_GOOD_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [UNDISCH_TAC `R / &2 < rho` THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2`; `rho:real`; `\t. (f:real^2->real^K)(wan_circ c rho t)`;
                 `\t. cmr_cder c R rho (f:real^2->real^K) t`]
         (REWRITE_RULE[WAN_POISSON_ENERGY_STATEMENT] (ISPEC `(:K)` WAN_POISSON_ENERGY))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMR_CIRC_PERIODIC; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^K` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `h:real^2->real^K`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN sphere(c:real^2,rho) ==> (h:real^2->real^K) x = f x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_THEN(MP_TAC o MATCH_MP WAN_SPHERE_CIRC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)])
                       (\s. lift(norm(cmr_cder c R rho (f:real^2->real^K) (drop s)) pow 2)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho:real` o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `vec 0:real^K`)) (concl th) &&
                     not(free_in `h:real^2->real^K` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^2`; `rho:real`; `x0:real^2`] WAN_SPHERE_CIRC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t0:real`) THEN
  MP_TAC(ISPECL [`c:real^2`; `rho:real`; `h:real^2->real^K`; `vec 0:real^K`;
                 `sqrt(&2 * pi * wan_dir (ball(c:real^2,R)) (f:real^2->real^K))`]
         (REWRITE_RULE[WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT]
            (ISPEC `(:K)` WAN_MAX_PRINCIPLE_DISC_BALL))) THEN
  ASM_REWRITE_TAC[IN_CBALL_0] THEN ANTS_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN sphere(c:real^2,rho)`)]) THEN
    MP_TAC(ISPECL [`c:real^2`; `rho:real`; `y:real^2`] WAN_SPHERE_CIRC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `t0:real`] o
      check (fun th -> let vs,bod = strip_forall(concl th) in
                       length vs = 2 && is_binary "real_le" bod)) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO];
    SIMP_TAC[]]);;


(* ========================================================================= *)
(* The competitor and the per-ball inequality.                               *)
(* ========================================================================= *)

(* Real arithmetic for the error term.                                       *)

let CMR_PB_ARITH = prove
 (`!KK delta dw dh X Y c1 c2.
     &0 <= KK /\ &0 <= dw /\ &0 <= dh /\ &0 <= X /\ &0 <= Y /\ &0 <= c1 /\ &0 <= c2 /\
     delta = sqrt(&2 * pi * Y) /\ dw <= c1 * X /\ X <= c2 /\ dh <= &4 * Y /\ Y <= &2 * X
     ==> KK * (delta * dw + sqrt dw * sqrt dh + dh)
         <= KK * (sqrt(&2 * pi) * c1 * sqrt c2 + &2 * sqrt c1 + &4 * sqrt(&2)) *
            sqrt X * sqrt Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `delta = sqrt(&2 * pi) * sqrt Y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM SQRT_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt Y /\ &0 <= sqrt dw /\ &0 <= sqrt dh /\
                &0 <= sqrt(&2 * pi) /\ &0 <= sqrt c1 /\ &0 <= sqrt c2 /\ &0 <= sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt X * sqrt X = X /\ sqrt Y * sqrt Y = Y` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= sqrt X` THEN UNDISCH_TAC `&0 <= sqrt Y` THEN
  ABBREV_TAC `sx = sqrt X` THEN ABBREV_TAC `sy = sqrt Y` THEN
  REPEAT DISCH_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `sx <= sqrt c2` ASSUME_TAC THENL
   [EXPAND_TAC "sx" THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sy <= sqrt(&2) * sx` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sx"; "sy"] THEN REWRITE_TAC[GSYM SQRT_MUL] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dw <= sqrt c1 * sx` ASSUME_TAC THENL
   [EXPAND_TAC "sx" THEN REWRITE_TAC[GSYM SQRT_MUL] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dh <= &2 * sy` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * sy = sqrt(&4 * Y)` SUBST1_TAC THENL
     [EXPAND_TAC "sy" THEN REWRITE_TAC[SQRT_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_ARITH `&4 = &2 pow 2`] THEN
      SIMP_TAC[POW_2_SQRT; REAL_POS];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dw <= c1 * sx * sqrt c2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 * X` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `sx * sx = X`)) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&2 * pi) * sy * dw <= sqrt(&2 * pi) * c1 * sqrt c2 * sx * sy`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(sqrt(&2 * pi) * sy) * dw <= (sqrt(&2 * pi) * sy) * (c1 * sx * sqrt c2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt dw * sqrt dh <= &2 * sqrt c1 * sx * sy` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt dw * sqrt dh <= (sqrt c1 * sx) * (&2 * sy)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dh <= &4 * sqrt(&2) * sx * sy` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * sy * sy` THEN CONJ_TAC THENL
     [UNDISCH_TAC `dh <= &4 * Y` THEN UNDISCH_TAC `sy * sy = Y` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `sy * sy <= (sqrt(&2) * sx) * sy` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `sqrt(&2 * pi) * sy * dw <= sqrt(&2 * pi) * c1 * sqrt c2 * sx * sy` THEN
  UNDISCH_TAC `sqrt dw * sqrt dh <= &2 * sqrt c1 * sx * sy` THEN
  UNDISCH_TAC `dh <= &4 * sqrt(&2) * sx * sy` THEN
  REAL_ARITH_TAC);;

(* Restriction of a C^0 /\ W^{1,2} map to a smaller concentric disc.         *)

let CMR_CMAP_SUB_BALL = prove
 (`!S (c:real^2) R rho (v:real^2->real^K).
     cm_cmap S (ball(c,R)) v /\ &0 < rho /\ rho <= R ==> cm_cmap S (ball(c,rho)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v:real^2->real^K)` THEN
  ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(c:real^2,rho) SUBSET cball(c,R)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(c:real^2,R)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,R)` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* G-energies split at a circle inside an open set.                          *)

let CMR_GDIR_SPLIT_BALL = prove
 (`!(s:real^2->bool) (a:real^2) r (G:real^K->real^K^K) (u:real^2->real^K) Lam.
     open s /\ cball(a,r) SUBSET s /\ wan_w12 s u /\ CMR_GCOND G Lam
     ==> wan_gdir s G u = wan_gdir (ball(a,r)) G u + wan_gdir (s DIFF cball(a,r)) G u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s /\ s DIFF cball(a,r) SUBSET s /\
                open(s DIFF cball(a:real^2,r))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
      SET_TAC[];
      ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `ball(a:real^2,r)`; `G:real^K->real^K^K`;
                 `u:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `s DIFF cball(a:real^2,r)`; `G:real^K->real^K^K`;
                 `u:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_gdir; GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  ABBREV_TAC `q = \x. lift(wan_wd s i (u:real^2->real^K) x dot
                           ((G:real^K->real^K^K)(u x) ** wan_wd s i u x))` THEN
  SUBGOAL_THEN `(q:real^2->real^1) absolutely_integrable_on s` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `i' = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LIFT_COMPONENT];
      MATCH_MP_TAC HMD_GDIR_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_ARITH `&0 <= x /\ x <= l ==> abs x <= l`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:real^2->real^1) integrable_on ball(a,r) /\ q integrable_on (s DIFF cball(a,r))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (ball(a:real^2,r) UNION (s DIFF cball(a,r))) (q:real^2->real^1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `sphere(a:real^2,r)` THEN REWRITE_TAC[NEGLIGIBLE_SPHERE] THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_UNION_SPHERE) THEN
    UNDISCH_TAC `cball(a:real^2,r) SUBSET s` THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_DIFF; IN_BALL; IN_SPHERE; IN_CBALL] THEN
    MESON_TAC[REAL_LT_IMP_LE; REAL_LE_LT];
    MATCH_MP_TAC INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^2->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[]]);;

(* The projected competitor Pg(w0 + h) on a disc: continuity, values in S, *)
(* W^{1,2} and the energy estimate HMD_COMPETITOR_ENERGY.                   *)

let CMR_PROJ_COMPETITOR = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) KK (c:real^2) rho w0 h delta.
     cm_target S G d /\ hmd_pgdata S d d1 B Pg /\ &0 <= KK /\
     (!y Z X Y. y IN S /\ norm Z <= d1 / &2
        ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
            (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
            <= X dot (G y ** X) +
               KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)) /\
     &0 < rho /\ cm_cmap S (ball(c,rho)) w0 /\
     h continuous_on cball(c,rho) /\ wan_w12 (ball(c,rho)) h /\
     (!x. x IN cball(c,rho) ==> norm(h x) <= delta) /\ delta <= d1 / &2
     ==> (\x. Pg(w0 x + h x)) continuous_on cball(c,rho) /\
         wan_w12 (ball(c,rho)) (\x. Pg(w0 x + h x)) /\
         (!x. x IN cball(c,rho) ==> Pg(w0 x + h x) IN S) /\
         wan_gdir (ball(c,rho)) G (\x. Pg(w0 x + h x)) <=
         wan_gdir (ball(c,rho)) G w0 +
         KK * (delta * wan_dir (ball(c,rho)) w0 +
               sqrt(wan_dir (ball(c,rho)) w0) * sqrt(wan_dir (ball(c,rho)) h) +
               wan_dir (ball(c,rho)) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  UNDISCH_TAC `cm_cmap S (ball(c:real^2,rho)) (w0:real^2->real^K)` THEN
  ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN cball(c:real^2,rho)
                    ==> (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) IN S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `delta:real` THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + h x)) =
                  Pg o (\x. w0 x + h x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HMD_COMPETITOR_ENERGY THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `d1:real`; `B:real`; `{}:real^2->bool`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; NEGLIGIBLE_EMPTY; DIFF_EMPTY;
                  ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_W12] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]);;

(* Gluing the competitor into the larger disc.                              *)

let CMR_GLUE_COMPETITOR = prove
 (`!S (G:real^K->real^K^K) Lam (c:real^2) rho R (z0:real^2->real^K) v1.
     CMR_GCOND G Lam /\ &0 < rho /\ rho < R /\ cm_cmap S (ball(c,R)) v1 /\
     z0 continuous_on cball(c,rho) /\ wan_w12 (ball(c,rho)) z0 /\
     (!x. x IN cball(c,rho) ==> z0 x IN S) /\
     (!x. x IN sphere(c,rho) ==> z0 x = v1 x)
     ==> cm_wmap S (ball(c,R)) (\x. if x IN ball(c,rho) then z0 x else v1 x) /\
         wan_w120 (ball(c,R)) (\x. (if x IN ball(c,rho) then z0 x else v1 x) - v1 x) /\
         wan_gdir (ball(c,R)) G (\x. if x IN ball(c,rho) then z0 x else v1 x) =
         wan_gdir (ball(c,rho)) G z0 + wan_gdir (ball(c,R) DIFF cball(c,rho)) G v1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v1:real^2->real^K)` THEN
  ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(c:real^2,rho) SUBSET ball(c,R) /\ ball(c:real^2,rho) SUBSET ball(c,R) /\
                cball(c:real^2,rho) SUBSET cball(c,R)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(c:real^2,rho)) (\x. (z0:real^2->real^K) x - v1 x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT) THEN
    REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[VECTOR_SUB_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,R)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(c:real^2,R)` THEN
      ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_GLUE_W12) THEN REWRITE_TAC[WAN_GLUE_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(c:real^2,R)`; `c:real^2`; `rho:real`;
                             `v1:real^2->real^K`; `z0:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[cm_wmap] THEN EXISTS_TAC `{}:real^2->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    SUBGOAL_THEN
     `(\x. (if x IN ball(c:real^2,rho) then (z0:real^2->real^K) x else v1 x) - v1 x) =
      (\x. if x IN ball(c,rho) then z0 x - v1 x else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[VECTOR_SUB_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT) THEN
    REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `cball(c:real^2,R) = cball(c,rho) UNION (cball(c,R) DIFF ball(c,rho))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`c:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      SIMP_TAC[CLOSED_CBALL; CLOSED_DIFF; OPEN_BALL; CONTINUOUS_ON_CONST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,R)` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN
        ASM_CASES_TAC `x IN ball(c:real^2,rho)` THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `x IN cball(c:real^2,rho)` THEN UNDISCH_TAC `~(x IN ball(c:real^2,rho))` THEN
        REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_SPHERE; IN_BALL] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `(\x. if x IN ball(c:real^2,rho) then (z0:real^2->real^K) x - v1 x else vec 0) =
        (\x. (if x IN ball(c,rho) then z0 x else v1 x) - v1 x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[VECTOR_SUB_REFL];
        MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]]];
    MP_TAC(ISPECL [`ball(c:real^2,R)`; `c:real^2`; `rho:real`; `G:real^K->real^K^K`;
                   `\x. if x IN ball(c:real^2,rho) then (z0:real^2->real^K) x else v1 x`;
                   `Lam:real`] CMR_GDIR_SPLIT_BALL) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN
    MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN SIMP_TAC[IN_DIFF; IN_CBALL; IN_BALL] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Bounds for the quantities in the error term.                             *)

let CMR_PB_ERRFACTS = prove
 (`!(G:real^K->real^K^K) e lam Lam (c:real^2) R rho (v:real^2->real^K) v1 w0.
     CMR_GCOND G Lam /\ &0 < lam /\ (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     &0 < rho /\ rho <= R /\
     wan_w12 (ball(c,R)) v /\ wan_w12 (ball(c,R)) v1 /\
     wan_gdir (ball(c,R)) G v <= e /\ wan_gdir (ball(c,R)) G v1 <= e /\
     wan_w12 (ball(c,rho)) w0 /\ wan_gdir (ball(c,rho)) G w0 <= wan_gdir (ball(c,rho)) G v
     ==> &0 <= Lam /\ &0 <= wan_dir (ball(c,rho)) w0 /\
         &0 <= wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1 /\
         &0 <= wan_dir (ball(c,R)) (\x. v1 x - v x) /\
         wan_dir (ball(c,rho)) w0 <=
         Lam / lam * (wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1) /\
         wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1 <= &2 * abs e / lam /\
         wan_dir (ball(c,R)) (\x. v1 x - v x) <=
         &2 * (wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o
      check (fun th -> is_forall(concl th) && free_in `Lam:real` (concl th))) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                       xi dot (G z ** xi) <= Lam * norm xi pow 2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s (u:real^2->real^K). open s /\ wan_w12 s u
        ==> lam * wan_dir s u <= wan_gdir s G u /\ wan_gdir s G u <= Lam * wan_dir s u /\
            &0 <= wan_dir s u`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[WAN_DIR_POS] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`; `lam:real`;
                   `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * wan_dir (ball(c:real^2,R)) (v:real^2->real^K) <= wan_gdir (ball(c,R)) G v /\
    wan_gdir (ball(c,R)) G v <= Lam * wan_dir (ball(c,R)) v /\ &0 <= wan_dir (ball(c,R)) v /\
    lam * wan_dir (ball(c:real^2,R)) (v1:real^2->real^K) <= wan_gdir (ball(c,R)) G v1 /\
    &0 <= wan_dir (ball(c,R)) v1 /\
    lam * wan_dir (ball(c:real^2,rho)) (w0:real^2->real^K) <= wan_gdir (ball(c,rho)) G w0 /\
    &0 <= wan_dir (ball(c,rho)) w0 /\
    wan_gdir (ball(c:real^2,rho)) G v <= Lam * wan_dir (ball(c,rho)) v`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `wan_w12 (ball(c:real^2,rho)) (v:real^2->real^K)` ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(c:real^2,R)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (ball(c:real^2,rho)) (v:real^2->real^K) <= wan_dir (ball(c,R)) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DIR_MONO_P THEN REWRITE_TAC[OPEN_BALL] THEN
    ASM_SIMP_TAC[SUBSET_BALL; CMR_W12_PARTIALS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,R)`; `v1:real^2->real^K`; `v:real^2->real^K`]
                CMR_DIR_SUB_LE_P) THEN
  ASM_SIMP_TAC[OPEN_BALL; CMR_W12_PARTIALS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * c = (a * c) * b`] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(c:real^2,rho)) G (w0:real^2->real^K)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(c:real^2,rho)) G (v:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lam * wan_dir (ball(c:real^2,rho)) (v:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * abs e) / lam` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]];
    ASM_REAL_ARITH_TAC]);;

(* The per-ball inequality for fixed target data (G-energies on the discs). *)

let CMR_PBALL_CORE = prove
 (`!S (G:real^K->real^K^K) d e lam Lam d1 B (Pg:real^K->real^K) KK (c:real^2) R
    (v:real^2->real^K) v1.
     cm_target S G d /\ cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     hmd_pgdata S d d1 B Pg /\ &0 <= KK /\
     (!y Z X Y. y IN S /\ norm Z <= d1 / &2
        ==> (frechet_derivative Pg (at (y + Z)) (X + Y)) dot
            (G(Pg(y + Z)) ** frechet_derivative Pg (at (y + Z)) (X + Y))
            <= X dot (G y ** X) +
               KK * (norm Z * norm X pow 2 + norm X * norm Y + norm Y pow 2)) /\
     &0 < R /\ cm_cmap S (ball(c,R)) v /\ cm_cmap S (ball(c,R)) v1 /\
     wan_gdir (ball(c,R)) G v <= e /\ wan_gdir (ball(c,R)) G v1 <= e /\
     wan_dir (ball(c,R)) (\x. v1 x - v x) <= d1 pow 2 / (&8 * pi) /\
     (!rho. R / &2 < rho /\ rho < R ==> ?x. x IN sphere(c,rho) /\ v x = v1 x)
     ==> ?rho. R / &2 < rho /\ rho < R /\
               wan_gdir (ball(c,rho)) G v1 - wan_gdir (ball(c,rho)) G (cmr_minw S G c rho v)
               <= (wan_gdir (ball(c,R)) G v1 - wan_gdir (ball(c,R)) G (cmr_minw S G c R v1)) +
                  KK * (sqrt(&2 * pi) * (Lam / lam) * sqrt(&2 * abs e / lam) +
                        &2 * sqrt(Lam / lam) + &4 * sqrt(&2)) *
                  sqrt(wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1) *
                  sqrt(wan_dir (ball(c,R)) (\x. v1 x - v x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN
  REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 (ball(c:real^2,R)) (v:real^2->real^K) /\ wan_w12 (ball(c,R)) (v1:real^2->real^K) /\
    v continuous_on cball(c,R) /\ v1 continuous_on cball(c,R) /\
    (!x. x IN cball(c,R) ==> v x IN S) /\ (!x. x IN cball(c,R) ==> v1 x IN S)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v:real^2->real^K)` THEN
    UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v1:real^2->real^K)` THEN
    ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `Y = wan_dir (ball(c:real^2,R)) (\x. (v1:real^2->real^K) x - v x)` THEN
  ABBREV_TAC `X = wan_dir (ball(c:real^2,R)) (v:real^2->real^K) +
                  wan_dir (ball(c,R)) (v1:real^2->real^K)` THEN
  (* the harmonic extension of v1 - v from a good circle *)
  MP_TAC(ISPECL [`c:real^2`; `R:real`; `\x. (v1:real^2->real^K) x - v x`] CMR_CIRCLE_HARM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,R)` THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `rho:real` o
        check (fun th -> is_forall(concl th) && free_in `v1:real^2->real^K` (concl th) &&
                         can (find_term ((=) `sphere:real^2#real->real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `h:real^2->real^K` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= R /\ cball(c:real^2,rho) SUBSET ball(c,R)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * pi * Y) <= d1 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `d1 / &2 = sqrt(&2 * pi * d1 pow 2 / (&8 * pi))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      SUBGOAL_THEN `&2 * pi * d1 pow 2 / (&8 * pi) = (d1 / &2) pow 2` SUBST1_TAC THENL
       [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the minimizer of v on the small disc *)
  SUBGOAL_THEN `cm_cmap S (ball(c:real^2,rho)) (v:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_CMAP_SUB_BALL THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,rho)) G (v:real^2->real^K) <= e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wan_gdir (ball(c:real^2,R)) G (v:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `rho:real`;
                 `v:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w0 = cmr_minw S G (c:real^2) rho (v:real^2->real^K)` THEN STRIP_TAC THEN
  (* the projected competitor on the small disc *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `KK:real`; `c:real^2`; `rho:real`; `w0:real^2->real^K`;
                 `h:real^2->real^K`; `sqrt(&2 * pi * Y)`] CMR_PROJ_COMPETITOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN sphere(c:real^2,rho)
        ==> (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) = v1 x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w0:real^2->real^K) x + h x = v1 x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(v1:real^2->real^K) x IN S` ASSUME_TAC THENL
     [UNDISCH_TAC `!x. x IN cball(c:real^2,R) ==> (v1:real^2->real^K) x IN S` THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`c:real^2`; `rho:real`] SPHERE_SUBSET_CBALL) THEN
      MP_TAC(ISPECL [`c:real^2`; `R:real`] BALL_SUBSET_CBALL) THEN
      UNDISCH_TAC `cball(c:real^2,rho) SUBSET ball(c,R)` THEN
      UNDISCH_TAC `x IN sphere(c:real^2,rho)` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!y. y IN S ==> (Pg:real^K->real^K) y = y` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the glued competitor on the large disc and the minimizer of v1 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `c:real^2`; `rho:real`;
                 `R:real`; `\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + h x)`;
                 `v1:real^2->real^K`] CMR_GLUE_COMPETITOR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `R:real`;
                 `v1:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m1 = cmr_minw S G (c:real^2) R (v1:real^2->real^K)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_gdir (ball(c:real^2,R)) G (m1:real^2->real^K) <=
    wan_gdir (ball(c,R)) G (\x. if x IN ball(c:real^2,rho)
                     then (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) else v1 x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S G (ball(c:real^2,R)) (m1:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `(\x. if x IN ball(c:real^2,rho)
                     then (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) else v1 x)` o CONJUNCT2) THEN
    ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ball(c:real^2,R)`;
                   `\x. (if x IN ball(c:real^2,rho)
                         then (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) else v1 x) - v1 x`;
                   `\x. (m1:real^2->real^K) x - v1 x`] WAN_W120_SUB) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,R)`; `c:real^2`; `rho:real`; `G:real^K->real^K^K`;
                 `v1:real^2->real^K`; `Lam:real`] CMR_GDIR_SPLIT_BALL) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  (* the error term *)
  ABBREV_TAC `dw = wan_dir (ball(c:real^2,rho)) (w0:real^2->real^K)` THEN
  ABBREV_TAC `dh = wan_dir (ball(c:real^2,rho)) (h:real^2->real^K)` THEN
  SUBGOAL_THEN
   `KK * (sqrt(&2 * pi * Y) * dw + sqrt dw * sqrt dh + dh)
    <= KK * (sqrt(&2 * pi) * (Lam / lam) * sqrt(&2 * abs e / lam) +
             &2 * sqrt(Lam / lam) + &4 * sqrt(&2)) * sqrt X * sqrt Y`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `wan_gdir (ball(c:real^2,rho)) G (w0:real^2->real^K) <= wan_gdir (ball(c,rho)) G v`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cm_minimizer S G (ball(c:real^2,rho)) (w0:real^2->real^K)` THEN
      REWRITE_TAC[cm_minimizer; cm_gen] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^2->real^K` o CONJUNCT2) THEN
      ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMR_CMAP_WMAP THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`ball(c:real^2,rho)`; `\x. (w0:real^2->real^K) x - v x`]
                      WAN_W120_NEG) THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `e:real`; `lam:real`; `Lam:real`; `c:real^2`;
                   `R:real`; `rho:real`; `v:real^2->real^K`; `v1:real^2->real^K`;
                   `w0:real^2->real^K`] CMR_PB_ERRFACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= dh` ASSUME_TAC THENL
     [EXPAND_TAC "dh" THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMR_PB_ARITH THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_ABS_POS; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC
   `wan_gdir (ball(c:real^2,R)) G (\x. if x IN ball(c:real^2,rho)
                     then (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) else v1 x) =
    wan_gdir (ball(c,rho)) G (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + h x)) +
    wan_gdir (ball(c,R) DIFF cball(c,rho)) G (v1:real^2->real^K)` THEN
  UNDISCH_TAC
   `wan_gdir (ball(c:real^2,rho)) G (\x. (Pg:real^K->real^K)((w0:real^2->real^K) x + h x)) <=
    wan_gdir (ball(c,rho)) G w0 + KK * (sqrt(&2 * pi * Y) * dw + sqrt dw * sqrt dh + dh)` THEN
  UNDISCH_TAC
   `wan_gdir (ball(c:real^2,R)) G (m1:real^2->real^K) <=
    wan_gdir (ball(c,R)) G (\x. if x IN ball(c:real^2,rho)
                     then (Pg:real^K->real^K)((w0:real^2->real^K) x + h x) else v1 x)` THEN
  UNDISCH_TAC
   `KK * (sqrt(&2 * pi * Y) * dw + sqrt dw * sqrt dh + dh)
    <= KK * (sqrt(&2 * pi) * (Lam / lam) * sqrt(&2 * abs e / lam) +
             &2 * sqrt(Lam / lam) + &4 * sqrt(&2)) * sqrt X * sqrt Y` THEN
  REAL_ARITH_TAC);;

(* The per-ball inequality (CM (3.24)/(3.29) in the Poisson form), with     *)
(* constants depending only on the target and the replacement threshold.    *)

let CMR_PBALL = prove
 (`!S (G:real^K->real^K^K) d e.
     cm_target S G d /\ cmw_repex S G e
     ==> ?Cp tau. &0 < Cp /\ &0 < tau /\
           !(c:real^2) R (v:real^2->real^K) v1.
             &0 < R /\ cm_cmap S (ball(c,R)) v /\ cm_cmap S (ball(c,R)) v1 /\
             wan_gdir (ball(c,R)) G v <= e /\ wan_gdir (ball(c,R)) G v1 <= e /\
             wan_dir (ball(c,R)) (\x. v1 x - v x) <= tau /\
             (!rho. R / &2 < rho /\ rho < R ==> ?x. x IN sphere(c,rho) /\ v x = v1 x)
             ==> ?rho. R / &2 < rho /\ rho < R /\
                   cm_gen G (ball(c,rho)) v1 - cm_gen G (ball(c,rho)) (cmr_minw S G c rho v)
                   <= (cm_gen G (ball(c,R)) v1 - cm_gen G (ball(c,R)) (cmr_minw S G c R v1)) +
                      Cp * sqrt(wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1) *
                      sqrt(wan_dir (ball(c,R)) (\x. v1 x - v x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lg:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  MP_TAC(REWRITE_RULE[HMD_PG_STATEMENT] HMD_PG_HOLDS) THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_TAC `Pg:real^K->real^K`))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`] HMD_PW_COMPOSITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `KK:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < d1` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_pgdata]; ALL_TAC] THEN
  ABBREV_TAC `C0 = KK * (sqrt(&2 * pi) * (Lg / lam) * sqrt(&2 * abs e / lam) +
                         &2 * sqrt(Lg / lam) + &4 * sqrt(&2))` THEN
  SUBGOAL_THEN `&0 <= C0` ASSUME_TAC THENL
   [EXPAND_TAC "C0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN TRY(MATCH_MP_TAC SQRT_POS_LE) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_ABS_POS; REAL_POS; REAL_LT_IMP_LE] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `C0 / &2 + &1` THEN EXISTS_TAC `d1 pow 2 / (&8 * pi)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `lam:real`;
                 `Lg:real`; `d1:real`; `B:real`; `Pg:real^K->real^K`; `KK:real`;
                 `c:real^2`; `R:real`; `v:real^2->real^K`; `v1:real^2->real^K`]
                CMR_PBALL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[cm_gen] THEN
  ABBREV_TAC `sX = sqrt(wan_dir (ball(c:real^2,R)) (v:real^2->real^K) +
                        wan_dir (ball(c,R)) (v1:real^2->real^K))` THEN
  ABBREV_TAC `sY = sqrt(wan_dir (ball(c:real^2,R)) (\x. (v1:real^2->real^K) x - v x))` THEN
  SUBGOAL_THEN `&0 <= sX * sY` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sX"; "sY"] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v:real^2->real^K)` THEN
    UNDISCH_TAC `cm_cmap S (ball(c:real^2,R)) (v1:real^2->real^K)` THEN
    REWRITE_TAC[cm_cmap] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[WAN_DIR_POS; REAL_LE_ADD; WAN_W12_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `KK * (sqrt(&2 * pi) * (Lg / lam) * sqrt(&2 * abs e / lam) +
          &2 * sqrt(Lg / lam) + &4 * sqrt(&2)) * sX * sY
    <= &2 * ((C0 / &2 + &1) * sX * sY)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `KK * (sqrt(&2 * pi) * (Lg / lam) * sqrt(&2 * abs e / lam) +
            &2 * sqrt(Lg / lam) + &4 * sqrt(&2)) * sX * sY = C0 * (sX * sY) /\
      &2 * ((C0 / &2 + &1) * sX * sY) = (C0 + &2) * (sX * sY)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "C0" THEN CONJ_TAC THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC
   `wan_gdir (ball(c:real^2,rho)) G (v1:real^2->real^K) -
    wan_gdir (ball(c,rho)) G (cmr_minw S G c rho (v:real^2->real^K))
    <= (wan_gdir (ball(c,R)) G v1 - wan_gdir (ball(c,R)) G (cmr_minw S G c R v1)) +
       KK * (sqrt(&2 * pi) * (Lg / lam) * sqrt(&2 * abs e / lam) +
             &2 * sqrt(Lg / lam) + &4 * sqrt(&2)) * sX * sY` THEN
  REAL_ARITH_TAC);;

