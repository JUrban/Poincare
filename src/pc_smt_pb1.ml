(* ========================================================================= *)
(* pc_smt_pb1: S3b, part 1.  Complete flows in the vf_rflow notation, S3b   *)
(* (iii) (a forward invariant closed disc contains a zero of the field:     *)
(* Brouwer fixed points of the time 2^-n maps accumulate at a zero), and    *)
(* S3b (i) (transversal returns of bounded forward half-orbits).            *)
(* ========================================================================= *)

needs "src/pc_smt_rn.ml";;
needs "src/pc_ode_vf.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_RFLOW_DOMAIN = prove
 (`!v:real^N->real^N.
        (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> ode_vf_domain v (:real^N) = (:real^(1,N)finite_sum)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ode_vf_domain; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[PASTECART_FST_SND]);;

let SMT_RFLOW_BASIC = prove
 (`!v:real^N->real^N.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> (!x. vf_rflow v (&0) x = x) /\
            (!s t x. vf_rflow v t (vf_rflow v s x) = vf_rflow v (s + t) x) /\
            smooth_family (:real^N) (vf_rflow v) /\
            (!x t. ((\s. vf_rflow v (drop s) x) has_vector_derivative
                    v(vf_rflow v t x)) (at (lift t)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (v:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[vf_rflow; LIFT_NUM] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`] ODE_VF_MAXIMAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    REPEAT GEN_TAC THEN REWRITE_TAC[vf_rflow; LIFT_ADD] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`; `lift s`]
      ODE_VF_GROUP) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV; vf_rflow; LIFT_DROP] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] ODE_VF_FLOW_SMOOTH) THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMT_RFLOW_DOMAIN];
    REPEAT GEN_TAC THEN REWRITE_TAC[vf_rflow; LIFT_DROP] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`] ODE_VF_MAXIMAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV]]);;

let SMT_RFLOW_CONTINUOUS = prove
 (`!v:real^N->real^N.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> (!t. smooth_map_on (:real^N) (vf_rflow v t)) /\
            (!t. (vf_rflow v t) continuous_on (:real^N)) /\
            (!x. (\s. vf_rflow v (drop s) x) continuous_on (:real^1))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMT_RFLOW_BASIC) THEN
  SUBGOAL_THEN `!t. smooth_map_on (:real^N) (vf_rflow (v:real^N->real^N) t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMT_FAMILY_SLICE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC `(v:real^N->real^N)(vf_rflow v (drop s) x)` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `drop s`]) THEN REWRITE_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* S3b (iii).  D is compact (a closed disc); Brouwer gives                  *)
(* x_n in D fixed by the time 2^-n map; x_n is then fixed by every time      *)
(* 2^-m with m <= n; a limit point l is fixed by every time 2^-m, and the    *)
(* difference quotients along 2^-m vanish, so v(l) = 0.                      *)
(* ------------------------------------------------------------------------- *)

let SMT_RFLOW_MULT_PERIOD = prove
 (`!v:real^N->real^N q x k.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        vf_rflow v q x = x
        ==> vf_rflow v (&k * q) x = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id")
   (CONJUNCTS_THEN2 (LABEL_TAC "grp") (K ALL_TAC))) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REMOVE_THEN "grp" (K ALL_TAC) THEN ASM_REWRITE_TAC[]]);;

let SMT_INVARIANT_DISK_ZERO = prove
 (`!n:N->bool. SMT_INVARIANT_DISK_ZERO_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[SMT_INVARIANT_DISK_ZERO_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->real^N`; `D:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inv")))) THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "der")))) THEN
  SUBGOAL_THEN `compact(D:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^N->bool`; `cball(vec 0:real^N,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  (* Brouwer at the dyadic times *)
  SUBGOAL_THEN `!n. ?x:real^N. x IN D /\ vf_rflow v (inv(&2 pow n)) x = x` MP_TAC THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`D:real^N->bool`; `cball(vec 0:real^N,&1)`]
      HOMEOMORPHIC_FIXPOINT_PROPERTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_BALL THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV; ETA_AX];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        USE_THEN "inv" MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS]]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `xs:num->real^N` (LABEL_TAC "xs"))] THEN
  SUBGOAL_THEN
   `!m n. m <= n ==> vf_rflow v (inv(&2 pow m)) ((xs:num->real^N) n) = xs n`
  (LABEL_TAC "per") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `inv(&2 pow m) = &(2 EXP (n - m)) * inv(&2 pow n)` SUBST1_TAC THENL
     [UNDISCH_TAC `m:num <= n` THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ADD_SUB2; REAL_POW_ADD; GSYM REAL_OF_NUM_POW] THEN
      MP_TAC(SPECL [`&2`; `d:num`] REAL_POW_NZ) THEN
      MP_TAC(SPECL [`&2`; `m:num`] REAL_POW_NZ) THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC SMT_RFLOW_MULT_PERIOD THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "xs" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* a limit point *)
  MP_TAC(ISPEC `D:real^N->bool` compact) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `xs:num->real^N`) THEN
  ANTS_TAC THENL [USE_THEN "xs" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` (X_CHOOSE_THEN `rr:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!m. vf_rflow v (inv(&2 pow m)) (l:real^N) = l` (LABEL_TAC "fix") THENL
   [X_GEN_TAC `m:num` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. vf_rflow v (inv(&2 pow m)) ((xs:num->real^N) ((rr:num->num) n))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN CONJ_TAC THENL
       [UNDISCH_TAC `!t. (vf_rflow (v:real^N->real^N) t) continuous_on (:real^N)` THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        SUBGOAL_THEN `(\n. (xs:num->real^N) ((rr:num->num) n)) = xs o rr` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `(xs:num->real^N) o (rr:num->num)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; o_THM] THEN EXISTS_TAC `m:num` THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "per" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `rr:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `l:real^N` THEN ASM_REWRITE_TAC[] THEN
  (* v(l) = 0 *)
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < x) /\ &0 <= x ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  USE_THEN "der" (MP_TAC o SPECL [`l:real^N`; `&0`]) THEN
  REWRITE_TAC[LIFT_NUM; HAS_VECTOR_DERIVATIVE_AT_1D; LIM_AT; VECTOR_SUB_RZERO;
              DROP_VEC] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(MP_TAC o SPEC `norm((v:real^N->real^N) l)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`inv(&2)`; `d:real`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift(inv(&2 pow m))`) THEN
  USE_THEN "fix" (fun th -> REWRITE_TAC[DIST_0; NORM_LIFT; LIFT_DROP; th;
                                         VECTOR_SUB_REFL; VECTOR_MUL_RZERO;
                                         REAL_LT_REFL]) THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM; REAL_LT_INV_EQ] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; GSYM REAL_POW_INV]);;

(* ------------------------------------------------------------------------- *)
(* Bounded forward orbits.  The derivative of the height                     *)
(* (gamma(t) - q) . w, a speed bound, omega-limit points along integer       *)
(* times, and the transversal neighbourhood of a regular point.              *)
(* ------------------------------------------------------------------------- *)

let SMT_RFLOW_DOT_DERIV = prove
 (`!(v:real^N->real^N) x q w t.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> ((\s. (vf_rflow v s x - q) dot w) has_real_derivative
             (v(vf_rflow v t x) dot w)) (atreal t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^N`; `t:real`] o last o CONJUNCTS o
    MATCH_MP SMT_RFLOW_BASIC) THEN
  DISCH_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  MP_TAC(ISPECL [`\s:real^1. vf_rflow (v:real^N->real^N) (drop s) x`;
                 `\z:real^N. lift((z - q) dot w)`;
                 `(v:real^N->real^N)(vf_rflow v t x)`;
                 `\h:real^N. lift(h dot w)`; `lift t`]
    ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN
    MP_TAC(ISPECL [`\z:real^N. z`; `\h:real^N. h`; `\z:real^N. (q:real^N)`;
                   `\h:real^N. vec 0:real^N`;
                   `at (vf_rflow (v:real^N->real^N) t x)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO];
    REWRITE_TAC[o_DEF]]);;

let SMT_ORBIT_LIPSCHITZ = prove
 (`!(v:real^N->real^N) x.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        bounded (IMAGE (\t. vf_rflow v t x) {t | &0 <= t})
        ==> ?M. &0 < M /\
                !a b. &0 <= a /\ &0 <= b
                      ==> norm(vf_rflow v a x - vf_rflow v b x) <= M * abs(a - b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "der" o last o CONJUNCTS) THEN
  ABBREV_TAC `K = closure(IMAGE (\t. vf_rflow (v:real^N->real^N) t x) {t | &0 <= t})` THEN
  SUBGOAL_THEN `compact(K:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[COMPACT_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded(IMAGE (v:real^N->real^N) K)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. vf_rflow (v:real^N->real^N) (drop s) x`;
                 `\s:real^1. (v:real^N->real^N)(vf_rflow v (drop s) x)`;
                 `{s:real^1 | &0 <= drop s}`; `B:real`] VECTOR_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; IS_INTERVAL_1; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      USE_THEN "der" (MP_TAC o SPECL [`x:real^N`; `drop s`]) THEN
      REWRITE_TAC[LIFT_DROP];
      X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "K" THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `drop s` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`lift a`; `lift b`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]]);;

let SMT_ORBIT_OMEGA = prove
 (`!(v:real^N->real^N) x.
        bounded (IMAGE (\t. vf_rflow v t x) {t | &0 <= t})
        ==> ?q rr. (!m n. m < n ==> rr m < rr n) /\
                   ((\n. vf_rflow v (&(rr n)) x) --> q) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPACT_CLOSURE; compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. vf_rflow (v:real^N->real^N) (&n) x`) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `&n:real` THEN
    REWRITE_TAC[REAL_POS];
    REWRITE_TAC[o_DEF] THEN MESON_TAC[]]);;

let SMT_TRANSVERSAL_NBHD = prove
 (`!(v:real^N->real^N) q.
        v continuous (at q) /\ ~(v q = vec 0)
        ==> ?e. &0 < e /\
                !z. norm(z - q) <= e ==> norm(v q) pow 2 / &2 <= v z dot v q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm((v:real^N->real^N) q) / &2` o
    REWRITE_RULE[continuous_at]) THEN
  ASM_SIMP_TAC[REAL_HALF; NORM_POS_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(v:real^N->real^N) z - v q`; `(v:real^N->real^N) q`]
    NORM_CAUCHY_SCHWARZ_ABS) THEN
  REWRITE_TAC[DOT_LSUB; GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `norm((v:real^N->real^N) z - v q) * norm(v q) <=
                norm(v q) / &2 * norm(v q)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Crossings of the transversal segment                                      *)
(*   Sigma = {z | w . z = w . q} INTER cball(q,e/2),   w = v q.              *)
(* The height (gamma - q) . w increases at rate at least |w|^2/2 while       *)
(* gamma stays in cball(q,e); an orbit point close to q is followed and      *)
(* preceded by a crossing within time tau; crossings are isolated from the   *)
(* right; first hits of closed sets along a continuous curve.                *)
(* ------------------------------------------------------------------------- *)

let SMT_SIGMA_IN = prove
 (`!(w:real^N) q e z.
        z IN {y | w dot y = w dot q} INTER cball(q,e) <=>
        (z - q) dot w = &0 /\ norm(z - q) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_CBALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; DOT_LSUB] THEN
  MP_TAC(ISPECL [`w:real^N`; `z:real^N`] DOT_SYM) THEN
  MP_TAC(ISPECL [`w:real^N`; `q:real^N`] DOT_SYM) THEN REAL_ARITH_TAC);;

let SMT_ORBIT_HEIGHT_INC = prove
 (`!(v:real^N->real^N) x q e a b.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        (!z. norm(z - q) <= e ==> norm(v q) pow 2 / &2 <= v z dot v q) /\
        a <= b /\ (!s. a <= s /\ s <= b ==> norm(vf_rflow v s x - q) <= e)
        ==> norm(v q) pow 2 / &2 * (b - a) <=
            (vf_rflow v b x - q) dot v q - (vf_rflow v a x - q) dot v q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "tr") (CONJUNCTS_THEN2 ASSUME_TAC
   (LABEL_TAC "path"))))) THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (vf_rflow (v:real^N->real^N) s x - q) dot v q`;
                 `\s. (v:real^N->real^N)(vf_rflow v s x) dot v q`;
                 `a:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(v:real^N->real^N)(vf_rflow v s x) dot v q` THEN
      MATCH_MP_TAC SMT_RFLOW_DOT_DERIV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMT_RFLOW_DOT_DERIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [USE_THEN "tr" MATCH_MP_TAC THEN USE_THEN "path" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SMT_ORBIT_CROSS_NEAR = prove
 (`!(v:real^N->real^N) x q e M tau t.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < e /\ &0 < M /\ &0 < tau /\ M * tau = e / &4 /\
        (!z. norm(z - q) <= e ==> norm(v q) pow 2 / &2 <= v z dot v q) /\
        (!a b. &0 <= a /\ &0 <= b
               ==> norm(vf_rflow v a x - vf_rflow v b x) <= M * abs(a - b)) /\
        tau <= t /\ norm(vf_rflow v t x - q) < e / &4 /\
        norm(vf_rflow v t x - q) * norm(v q) < tau * norm(v q) pow 2 / &2
        ==> ?s. t - tau < s /\ s < t + tau /\
                (vf_rflow v s x - q) dot v q = &0 /\
                norm(vf_rflow v s x - q) <= e / &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "tr") (CONJUNCTS_THEN2 (LABEL_TAC "lip")
   STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN
   `!s. t - tau <= s /\ s <= t + tau
        ==> norm(vf_rflow (v:real^N->real^N) s x - q) <= e / &2`
  (LABEL_TAC "path") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "lip" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * abs(s - t) <= e / &4` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * tau` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`vf_rflow (v:real^N->real^N) s x`; `vf_rflow (v:real^N->real^N) t x`;
                   `q:real^N`]
      (NORM_ARITH `!a b q:real^N. norm(a - q) <= norm(a - b) + norm(b - q)`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((v:real^N->real^N) q) pow 2 / &2 * tau <=
    (vf_rflow v (t + tau) x - q) dot v q - (vf_rflow v t x - q) dot v q /\
    norm((v:real^N->real^N) q) pow 2 / &2 * tau <=
    (vf_rflow v t x - q) dot v q - (vf_rflow v (t - tau) x - q) dot v q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`; `q:real^N`; `e:real`;
                     `t:real`; `t + tau`] SMT_ORBIT_HEIGHT_INC);
      MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`; `q:real^N`; `e:real`;
                     `t - tau`; `t:real`] SMT_ORBIT_HEIGHT_INC)] THEN
    REWRITE_TAC[REAL_ARITH `(t + tau) - t = tau`; REAL_ARITH `t - (t - tau) = tau`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x <= e`) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "path" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vf_rflow (v:real^N->real^N) t x - q`; `(v:real^N->real^N) q`]
    NORM_CAUCHY_SCHWARZ_ABS) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s. (vf_rflow (v:real^N->real^N) s x - q) dot v q`;
                 `t - tau`; `t + tau`; `&0`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(v:real^N->real^N)(vf_rflow v s x) dot v q` THEN
      MATCH_MP_TAC SMT_RFLOW_DOT_DERIV THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `~(s = t - tau) /\ ~(s = t + tau)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `s:real` THEN
  UNDISCH_TAC `s IN real_interval[t - tau,t + tau]` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    USE_THEN "path" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let SMT_ORBIT_CROSS_ISOLATED = prove
 (`!(v:real^N->real^N) x q e M s t.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < e /\ &0 < M /\ ~(v q = vec 0) /\
        (!z. norm(z - q) <= e ==> norm(v q) pow 2 / &2 <= v z dot v q) /\
        (!a b. &0 <= a /\ &0 <= b
               ==> norm(vf_rflow v a x - vf_rflow v b x) <= M * abs(a - b)) /\
        &0 <= s /\ s < t /\ M * (t - s) <= e / &2 /\
        (vf_rflow v s x - q) dot v q = &0 /\ norm(vf_rflow v s x - q) <= e / &2
        ==> &0 < (vf_rflow v t x - q) dot v q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr")
   (CONJUNCTS_THEN2 (LABEL_TAC "lip") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`; `q:real^N`; `e:real`;
                 `s:real`; `t:real`] SMT_ORBIT_HEIGHT_INC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "lip" (MP_TAC o SPECL [`u:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * abs(u - s) <= e / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * (t - s)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`vf_rflow (v:real^N->real^N) u x`; `vf_rflow (v:real^N->real^N) s x`;
                   `q:real^N`]
      (NORM_ARITH `!a b q:real^N. norm(a - q) <= norm(a - b) + norm(b - q)`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= b ==> &0 < b`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT];
    ASM_REAL_ARITH_TAC]);;

let SMT_FIRST_HIT = prove
 (`!(f:real^1->real^N) S a b.
        f continuous_on (:real^1) /\ closed S /\ a <= b /\ f(lift b) IN S
        ==> ?c. a <= c /\ c <= b /\ f(lift c) IN S /\
                !t. a <= t /\ t < c ==> ~(f(lift t) IN S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{t | a <= t /\ t <= b /\ (f:real^1->real^N)(lift t) IN S}`
    COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `IMAGE lift {t | a <= t /\ t <= b /\ (f:real^1->real^N)(lift t) IN S} =
        {u | u IN interval[lift a,lift b] /\ f u IN S}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
        MESON_TAC[LIFT_DROP];
        REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[lift a,lift b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
          ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV]]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `c:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* S3b (i).  A bounded forward half-orbit of a nonvanishing                  *)
(* field has two consecutive crossings s1 < s2 of the transversal segment    *)
(* Sigma at a regular omega-limit point (crossing near orbit points close to *)
(* q, isolation from the right, first hit after the isolation time); in the  *)
(* plane either the orbit is periodic, or the chord of the two crossings is  *)
(* transversal, the arc is injective and meets the chord only at its ends.   *)
(* ------------------------------------------------------------------------- *)

let SMT_SEGMENT_IN_SIGMA = prove
 (`!(w:real^N) q e a b.
        a IN {y | w dot y = w dot q} INTER cball(q,e) /\
        b IN {y | w dot y = w dot q} INTER cball(q,e)
        ==> segment[a,b] SUBSET {y | w dot y = w dot q} INTER cball(q,e)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `{y:real^N | w dot y = w dot q} INTER cball(q,e)`
    CONVEX_CONTAINS_SEGMENT) THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; CONVEX_CBALL]);;

let SMT_TRANSVERSAL_ALGEBRA = prove
 (`!(a:real^2) b w V.
        (b - a) dot w = &0 /\ ~(b = a) /\ &0 < V dot w
        ==> ~((b - a)$1 * V$2 - (b - a)$2 * V$1 = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((V:real^2)$1 * (w:real^2)$1 + V$2 * w$2 = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~((b:real^2) = a)` THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
  UNDISCH_TAC
   `((b:real^2)$1 - (a:real^2)$1) * (w:real^2)$1 + (b$2 - a$2) * w$2 = &0` THEN
  CONV_TAC REAL_RING);;

let SMT_ORBIT_CONSECUTIVE = prove
 (`!(v:real^N->real^N) x.
        smooth_map_on (:real^N) v /\ (!y. ~(v y = vec 0)) /\
        (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        bounded (IMAGE (\t. vf_rflow v t x) {t | &0 <= t})
        ==> ?q e s1 s2.
              &0 < e /\
              (!z. norm(z - q) <= e ==> norm(v q) pow 2 / &2 <= v z dot v q) /\
              &0 <= s1 /\ s1 < s2 /\
              vf_rflow v s1 x IN {y | v q dot y = v q dot q} INTER cball(q,e / &2) /\
              vf_rflow v s2 x IN {y | v q dot y = v q dot q} INTER cball(q,e / &2) /\
              (!t. s1 < t /\ t < s2
                   ==> ~(vf_rflow v t x IN
                         {y | v q dot y = v q dot q} INTER cball(q,e / &2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`] SMT_ORBIT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip"))) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`] SMT_ORBIT_OMEGA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `rr:num->num`
    (CONJUNCTS_THEN2 (LABEL_TAC "mono") (LABEL_TAC "conv")))) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `q:real^N`] SMT_TRANSVERSAL_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")))] THEN
  MAP_EVERY EXISTS_TAC [`q:real^N`; `e:real`] THEN ASM_REWRITE_TAC[SMT_SIGMA_IN] THEN
  (* constants *)
  ABBREV_TAC `tau = e / (&4 * M)` THEN
  SUBGOAL_THEN `&0 < tau /\ M * tau = e / &4 /\ M * (&2 * tau) = e / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm((v:real^N->real^N) q)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `d = min (e / &4) (tau * norm((v:real^N->real^N) q) / &2)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_HALF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. norm(vf_rflow (v:real^N->real^N) t x - q) < d
        ==> norm(vf_rflow v t x - q) < e / &4 /\
            norm(vf_rflow v t x - q) * norm(v q) < tau * norm(v q) pow 2 / &2`
  (LABEL_TAC "dprop") THENL
   [GEN_TAC THEN EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(tau * norm((v:real^N->real^N) q) / &2) * norm(v q)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* orbit points close to q at arbitrarily late times *)
  USE_THEN "conv" (MP_TAC o SPEC `d:real` o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[dist] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "close")) THEN
  SUBGOAL_THEN
   `!K. ?t. &K <= t /\ norm(vf_rflow (v:real^N->real^N) t x - q) < d`
  (LABEL_TAC "late") THENL
   [X_GEN_TAC `K:num` THEN EXISTS_TAC `&((rr:num->num) (N + K)):real` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      USE_THEN "mono" (MP_TAC o SPEC `N + K:num` o MATCH_MP MONOTONE_BIGGER) THEN
      ARITH_TAC;
      USE_THEN "close" MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  (* a first crossing *)
  X_CHOOSE_TAC `K1:num` (SPEC `tau:real` REAL_ARCH_SIMPLE) THEN
  USE_THEN "late" (X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC o SPEC `K1:num`) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`; `q:real^N`; `e:real`; `M:real`;
                 `tau:real`; `t1:real`] SMT_ORBIT_CROSS_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "dprop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `&0 <= s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* a later crossing *)
  X_CHOOSE_TAC `K3:num` (SPEC `s1 + &3 * tau + &1` REAL_ARCH_SIMPLE) THEN
  USE_THEN "late" (X_CHOOSE_THEN `t3:real` STRIP_ASSUME_TAC o SPEC `K3:num`) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `x:real^N`; `q:real^N`; `e:real`; `M:real`;
                 `tau:real`; `t3:real`] SMT_ORBIT_CROSS_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "dprop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s3:real` STRIP_ASSUME_TAC)] THEN
  (* the first hit after the isolation time *)
  MP_TAC(ISPECL [`\u:real^1. vf_rflow (v:real^N->real^N) (drop u) x`;
                 `{y:real^N | v q dot y = v q dot q} INTER cball(q,e / &2)`;
                 `s1 + &2 * tau`; `s3:real`] SMT_FIRST_HIT) THEN
  REWRITE_TAC[LIFT_DROP; SMT_SIGMA_IN] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_HYPERPLANE; CLOSED_CBALL];
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `s2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (LABEL_TAC "first")))))] THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `s2:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t < s1 + &2 * tau` THENL
   [MATCH_MP_TAC(TAUT `~p ==> ~(p /\ q)`) THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    SUBGOAL_THEN `M * (t - s1) <= e / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * (&2 * tau)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC SMT_ORBIT_CROSS_ISOLATED THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `M:real`; `s1:real`] THEN ASM_REWRITE_TAC[];
    USE_THEN "first" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let SMT_TRANSVERSE_RETURN = prove
 (`SMT_TRANSVERSE_RETURN_STATEMENT`,
  REWRITE_TAC[SMT_TRANSVERSE_RETURN_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`v:real^2->real^2`; `x:real^2`] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `?t0 T. &0 < T /\ vf_rflow (v:real^2->real^2) (t0 + T) x = vf_rflow v t0 x` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(LABEL_TAC "np" o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`]) THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `x:real^2`] SMT_ORBIT_CONSECUTIVE) THEN
  ASM_REWRITE_TAC[SMT_SIGMA_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^2` (X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (LABEL_TAC "between"))))))))))) THEN
  SUBGOAL_THEN `~(vf_rflow (v:real^2->real^2) s2 x = vf_rflow v s1 x)` ASSUME_TAC THENL
   [USE_THEN "np" (MP_TAC o SPECL [`s1:real`; `s2 - s1`]) THEN
    REWRITE_TAC[REAL_ARITH `s1 + (s2 - s1) = s2`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN segment[vf_rflow (v:real^2->real^2) s1 x,vf_rflow v s2 x]
        ==> (z - q) dot v q = &0 /\ norm(z - q) <= e / &2`
  (LABEL_TAC "seg") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(v:real^2->real^2) q`; `q:real^2`; `e / &2`;
                   `vf_rflow (v:real^2->real^2) s1 x`; `vf_rflow (v:real^2->real^2) s2 x`]
      SMT_SEGMENT_IN_SIGMA) THEN
    ASM_REWRITE_TAC[SMT_SIGMA_IN] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[SMT_SIGMA_IN];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `s2 - s1`] THEN
  REWRITE_TAC[REAL_ARITH `s1 + (s2 - s1) = s2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    (* transversality on the chord *)
    REWRITE_TAC[transversal_on] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMT_TRANSVERSAL_ALGEBRA THEN EXISTS_TAC `(v:real^2->real^2) q` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(vf_rflow (v:real^2->real^2) s1 x - q) dot v q = &0` THEN
      UNDISCH_TAC `(vf_rflow (v:real^2->real^2) s2 x - q) dot v q = &0` THEN
      REWRITE_TAC[DOT_LSUB] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `norm((v:real^2->real^2) q) pow 2 / &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT];
        USE_THEN "tr" MATCH_MP_TAC THEN
        USE_THEN "seg" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]];
    (* injectivity of the arc *)
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `a < b \/ a = b \/ b < a`) THEN
    ASM_REWRITE_TAC[] THENL
     [USE_THEN "np" (MP_TAC o SPECL [`s1 + a`; `b - a`]) THEN
      REWRITE_TAC[REAL_ARITH `(s1 + a) + (b - a) = s1 + b`] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT];
      USE_THEN "np" (MP_TAC o SPECL [`s1 + b`; `a - b`]) THEN
      REWRITE_TAC[REAL_ARITH `(s1 + b) + (a - b) = s1 + a`] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT]];
    (* the open arc misses the chord *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "between" (MP_TAC o SPEC `s1 + t`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "seg" (MP_TAC o SPEC `vf_rflow (v:real^2->real^2) (s1 + t) x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONV_TAC TAUT]);;

