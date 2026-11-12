(* ========================================================================= *)
(* pc_smt_pb2: S3b, part 2.  S3b (ii) (the arc of a return and its chord,    *)
(* or a periodic orbit, bound a closed disc which is forward or backward     *)
(* invariant) and S3b for complete fields.                                   *)
(*                                                                           *)
(* An invariance criterion for closures of open sets under a                 *)
(* continuous flow, time reversal of flows, and connected sets in the        *)
(* complement of a set.                                                      *)
(* ========================================================================= *)

needs "src/pc_smt_pb1.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_INVARIANT_CRITERION = prove
 (`!(FL:real->real^N->real^N) U.
        open U /\
        (!x. FL (&0) x = x) /\
        (!x. (\s. FL (drop s) x) continuous_on (:real^1)) /\
        (!s t x. FL s (FL t x) = FL (t + s) x) /\
        (!p. p IN frontier U
             ==> ?d. &0 < d /\ !s. &0 < s /\ s < d ==> FL s p IN closure U)
        ==> !t x. &0 <= t /\ x IN closure U ==> FL t x IN closure U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id")
   (CONJUNCTS_THEN2 (LABEL_TAC "cont") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
   (LABEL_TAC "fr"))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{s | &0 <= s /\ s <= t /\ (FL:real->real^N->real^N) s x IN closure U}`
    COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `IMAGE lift {s | &0 <= s /\ s <= t /\ (FL:real->real^N->real^N) s x IN closure U} =
        {u | u IN interval[vec 0,lift t] /\ (\s. FL (drop s) x) u IN closure U}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP;
                    DROP_VEC] THEN
        MESON_TAC[LIFT_DROP];
        REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,lift t]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
          REWRITE_TAC[CLOSED_INTERVAL; CLOSED_CLOSURE] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV]]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "sup"))) THEN
  SUBGOAL_THEN `c < t` ASSUME_TAC THENL
   [ASM_CASES_TAC `c:real = t` THENL
     [UNDISCH_TAC `(FL:real->real^N->real^N) c x IN closure U` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(FL:real->real^N->real^N) c x IN U` THENL
   [(* interior point: the orbit stays in U a little longer *)
    UNDISCH_TAC `open(U:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(FL:real->real^N->real^N) c x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "cont" (MP_TAC o SPEC `x:real^N`) THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV; WITHIN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `lift c`) THEN REWRITE_TAC[continuous_at; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "sup" (MP_TAC o SPEC `min t (c + d / &2)`) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `lift(min t (c + d / &2))`) THEN
        REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* frontier point *)
  SUBGOAL_THEN `(FL:real->real^N->real^N) c x IN frontier U` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; INTERIOR_OPEN; IN_DIFF]; ALL_TAC] THEN
  USE_THEN "fr" (MP_TAC o SPEC `(FL:real->real^N->real^N) c x`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fwd"))) THEN
  USE_THEN "fwd" (MP_TAC o SPEC `min (t - c) d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  USE_THEN "sup" (MP_TAC o SPEC `c + min (t - c) d / &2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let SMT_RFLOW_REVERSE = prove
 (`!v:real^N->real^N.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> smooth_map_on (:real^N) (\x. --(v x)) /\
            (!y. ode_vf_maxint (\x. --(v x)) (:real^N) y = (:real^1)) /\
            (!t x. vf_rflow (\x. --(v x)) t x = vf_rflow v (--t) x)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. --((v:real^N->real^N) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (\x. --((v:real^N->real^N) x))`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "der")))) THEN
  SUBGOAL_THEN
   `!x:real^N u. u IN ode_vf_maxint (\x. --((v:real^N->real^N) x)) (:real^N) x /\
                 vf_rflow v (--drop u) x = ode_vf_flow (\x. --(v x)) (:real^N) u x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`\x. --((v:real^N->real^N) x)`; `(:real^N)`; `(:real^1)`;
                   `\u. vf_rflow (v:real^N->real^N) (--drop u) x`; `vec 0:real^1`]
      ODE_VF_UNIQUE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV; IN_UNIV; WITHIN_UNIV; VECTOR_SUB_RZERO;
                    DROP_VEC; REAL_NEG_0] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `u:real^1` THEN
    SUBGOAL_THEN `(\u. vf_rflow (v:real^N->real^N) (--drop u) x) =
                  (\s. vf_rflow v (drop s) x) o (\u. --u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\u:real^1. --u`; `\s:real^1. vf_rflow (v:real^N->real^N) (drop s) x`;
                   `--(vec 1):real^1`; `(v:real^N->real^N)(vf_rflow v (--drop u) x)`;
                   `u:real^1`] VECTOR_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[DROP_NEG; DROP_VEC; VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_NEG THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID];
      USE_THEN "der" (MP_TAC o SPECL [`x:real^N`; `--drop(u:real^1)`]) THEN
      REWRITE_TAC[LIFT_NEG; LIFT_DROP]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[EXTENSION; IN_UNIV] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[vf_rflow] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`x:real^N`; `lift t`]) THEN
    REWRITE_TAC[LIFT_DROP; vf_rflow] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[]]);;

let SMT_CONNECTED_INSIDE_OUTSIDE = prove
 (`!s c:real^N->bool.
        connected c /\ c INTER s = {}
        ==> c SUBSET inside s \/ c SUBSET outside s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `!y:real^N. y IN c ==> connected_component ((:real^N) DIFF s) x y`
  ASSUME_TAC THENL
   [REWRITE_TAC[connected_component] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN inside s \/ x IN outside s` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[INSIDE_SAME_COMPONENT];
    DISJ2_TAC THEN ASM_MESON_TAC[OUTSIDE_SAME_COMPONENT]]);;

(* ------------------------------------------------------------------------- *)
(* The closed curve.  The orbit arc over [0,TT] as a path, the               *)
(* loop (arc followed by the chord back, or the periodic orbit), and the     *)
(* Jordan facts for a simple closed path: the inside is a bounded open       *)
(* connected set with frontier the curve, and its closure is a closed disc   *)
(* (Jordan-Schoenflies against the unit circle).                             *)
(* ------------------------------------------------------------------------- *)

let SMT_ORBIT_PATH = prove
 (`!(v:real^N->real^N) a TT.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < TT
        ==> path (\u. vf_rflow v (TT * drop u) a) /\
            pathstart (\u. vf_rflow v (TT * drop u) a) = a /\
            pathfinish (\u. vf_rflow v (TT * drop u) a) = vf_rflow v TT a /\
            path_image (\u. vf_rflow v (TT * drop u) a) =
            IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "id" o CONJUNCT1) THEN
  REWRITE_TAC[path; pathstart; pathfinish; path_image; DROP_VEC; REAL_MUL_RZERO;
              REAL_MUL_RID] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\u. vf_rflow (v:real^N->real^N) (TT * drop u) a) =
                  (\s. vf_rflow v (drop s) a) o (\u. TT % u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `TT * drop u` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `lift(t / TT)` THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_DIV;
                   REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID]]]);;

let SMT_RETURN_LOOP = prove
 (`!(v:real^N->real^N) a TT.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < TT /\
        (!s t. s IN real_interval[&0,TT] /\ t IN real_interval[&0,TT] /\
               vf_rflow v s a = vf_rflow v t a ==> s = t \/ {s,t} = {&0,TT}) /\
        (~(vf_rflow v TT a = a)
         ==> (!t. &0 < t /\ t < TT ==> ~(vf_rflow v t a IN segment[a,vf_rflow v TT a])))
        ==> ?c. simple_path c /\ pathfinish c = pathstart c /\
                path_image c = IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                               segment[a,vf_rflow v TT a]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (LABEL_TAC "miss"))))) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `a:real^N`; `TT:real`] SMT_ORBIT_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = \u. vf_rflow (v:real^N->real^N) (TT * drop u) a` THEN STRIP_TAC THEN
  (* injectivity of g on [0,1] up to the endpoints *)
  SUBGOAL_THEN
   `!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
          (g:real^1->real^N) x = g y
          ==> drop x = drop y \/ (drop x = &0 /\ drop y = &1) \/
              (drop x = &1 /\ drop y = &0)`
  (LABEL_TAC "ginj") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`TT * drop(x:real^1)`; `TT * drop(y:real^1)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `{a:real,b} = {c,d} <=> a = c /\ b = d \/ a = d /\ b = c`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `TT * x = TT <=> TT * x = TT * &1`] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_ENTIRE; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_CASES_TAC `vf_rflow (v:real^N->real^N) TT a = a` THENL
   [(* periodic: the orbit itself *)
    EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[SEGMENT_REFL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[simple_path] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN DISCH_TAC THEN
      USE_THEN "ginj" (MP_TAC o SPECL [`x:real^1`; `y:real^1`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC];
      MATCH_MP_TAC(SET_RULE `(a:real^N) IN s ==> s = s UNION {a}`) THEN
      REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN EXISTS_TAC `&0` THEN
      MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* return: arc followed by the chord *)
  USE_THEN "miss" (MP_TAC o C MP (ASSUME `~(vf_rflow (v:real^N->real^N) TT a = a)`)) THEN
  DISCH_TAC THEN
  EXISTS_TAC `(g:real^1->real^N) ++ linepath(vf_rflow v TT a,a)` THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_JOIN;
               PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  CONJ_TAC THENL
   [ALL_TAC; AP_TERM_TAC THEN MATCH_ACCEPT_TAC(CONJUNCT1 SEGMENT_SYM)] THEN
  MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
  ASM_SIMP_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH; ARC_LINEPATH] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[arc] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((g:real^1->real^N) (vec 0) = g (vec 1))` ASSUME_TAC THENL
     [UNDISCH_TAC `pathstart (g:real^1->real^N) = a` THEN
      UNDISCH_TAC `pathfinish (g:real^1->real^N) = vf_rflow v TT a` THEN
      REWRITE_TAC[pathstart; pathfinish] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "ginj" (MP_TAC o SPECL [`x:real^1`; `y:real^1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `x:real^1 = vec 0 /\ y:real^1 = vec 1` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ALL_TAC] THEN
      UNDISCH_TAC `(g:real^1->real^N) x = g y` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `x:real^1 = vec 1 /\ y:real^1 = vec 0` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ALL_TAC] THEN
      UNDISCH_TAC `(g:real^1->real^N) x = g y` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_CASES_TAC `t = &0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real = TT` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `segment[a,vf_rflow (v:real^N->real^N) TT a] = segment[vf_rflow v TT a,a]`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC(CONJUNCT1 SEGMENT_SYM); ALL_TAC] THEN
    UNDISCH_TAC `z IN segment[vf_rflow (v:real^N->real^N) TT a,a]` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT]);;

let SMT_SIMPLE_LOOP_FACTS = prove
 (`!c:real^1->real^2.
        simple_path c /\ pathfinish c = pathstart c
        ==> open(inside(path_image c)) /\ connected(inside(path_image c)) /\
            bounded(inside(path_image c)) /\ ~(inside(path_image c) = {}) /\
            frontier(inside(path_image c)) = path_image c /\
            frontier(outside(path_image c)) = path_image c /\
            inside(path_image c) INTER outside(path_image c) = {} /\
            inside(path_image c) UNION outside(path_image c) =
            (:real^2) DIFF path_image c /\
            closure(inside(path_image c)) homeomorphic cball(vec 0:real^2,&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_LT_01; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_TAC `f':real^2->real^2`)) THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `circlepath(vec 0:real^2,&1)`;
                 `f:real^2->real^2`; `f':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_POS; SIMPLE_PATH_CIRCLEPATH;
               REAL_ARITH `~(&1 = &0)`; INSIDE_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->real^2`; `k':real^2->real^2`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  ONCE_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
  ASM_REWRITE_TAC[IMAGE_UNION; BALL_UNION_SPHERE]);;

(* ------------------------------------------------------------------------- *)
(* The chord.  A transversal chord has a normal w with                       *)
(* v . w > 0 along it; the height (gamma - q) . w increases while gamma      *)
(* stays where v . w >= c; a trajectory through a point p with v p . w > 0   *)
(* immediately enters the open half-ball on the w side of p.                 *)
(* ------------------------------------------------------------------------- *)

let SMT_IVT_SIGN = prove
 (`!(f:real^1->real^1) a b.
        f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> ~(drop(f x) = &0)) /\ &0 < drop(f a)
        ==> !x. x IN interval[a,b] ==> &0 < drop(f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `(x:real^1) IN interval[a,b]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^1. y IN interval[a,x] /\ drop((f:real^1->real^1) y) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `x:real^1`; `&0`; `1`]
      IVT_DECREASING_COMPONENT_ON_1) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[a:real^1,b]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^1) IN interval[a,x]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let SMT_CHORD_NORMAL = prove
 (`!(v:real^2->real^2) a b.
        smooth_map_on (:real^2) v /\ ~(a = b) /\ transversal_on v a b
        ==> ?w. ~(w = vec 0) /\ (b - a) dot w = &0 /\
                !z. z IN segment[a,b] ==> &0 < v z dot w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[transversal_on] THEN STRIP_TAC THEN
  ABBREV_TAC `n = vector[--((b - a:real^2)$2); (b - a)$1]:real^2` THEN
  SUBGOAL_THEN
   `!z:real^2. (b - a:real^2)$1 * z$2 - (b - a)$2 * z$1 = z dot n`
  (LABEL_TAC "nd") THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(b - a:real^2) dot n = &0 /\ ~(n = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      UNDISCH_TAC `~(a:real^2 = b)` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT;
                  VECTOR_SUB_COMPONENT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN segment[a,b] ==> ~((v:real^2->real^2) z dot n = &0)`
  (LABEL_TAC "nz") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "nd" (fun th -> REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = \x:real^1. lift((v:real^2->real^2)(linepath(a,b) x) dot n)` THEN
  SUBGOAL_THEN `(f:real^1->real^1) continuous_on interval[vec 0,vec 1]` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    SUBGOAL_THEN `(\x:real^1. lift((v:real^2->real^2)(linepath(a,b) x) dot n)) =
                  (lift o (\y. n dot y)) o v o linepath(a,b)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[DOT_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_LINEPATH] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN interval[vec 0:real^1,vec 1] ==> ~(drop((f:real^1->real^1) x) = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[LIFT_DROP] THEN USE_THEN "nz" MATCH_MP_TAC THEN
    MATCH_MP_TAC LINEPATH_IN_PATH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN segment[a,b] ==> ?x. x IN interval[vec 0,vec 1] /\
                                                    z = linepath(a,b) x`
  (LABEL_TAC "par") THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop((f:real^1->real^1)(vec 0)) = (v:real^2->real^2) a dot n` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_DROP; linepath; DROP_VEC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^2->real^2) a dot n = &0)` ASSUME_TAC THENL
   [USE_THEN "nz" MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (v:real^2->real^2) a dot n` THENL
   [EXISTS_TAC `n:real^2` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `vec 0:real^1`; `vec 1:real^1`] SMT_IVT_SIGN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_DROP];
    SUBGOAL_THEN `(v:real^2->real^2) a dot n < &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `--n:real^2` THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_RNEG] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\x. --((f:real^1->real^1) x)`; `vec 0:real^1`; `vec 1:real^1`]
      SMT_IVT_SIGN) THEN
    REWRITE_TAC[DROP_NEG] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_EQ_0] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[CONTINUOUS_ON_NEG]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC]);;

let SMT_ORBIT_HEIGHT_INC_W = prove
 (`!(v:real^N->real^N) x q w c e a b.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        (!z. norm(z - q) <= e ==> c <= v z dot w) /\
        a <= b /\ (!s. a <= s /\ s <= b ==> norm(vf_rflow v s x - q) <= e)
        ==> c * (b - a) <=
            (vf_rflow v b x - q) dot w - (vf_rflow v a x - q) dot w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "tr") (CONJUNCTS_THEN2 ASSUME_TAC
   (LABEL_TAC "path"))))) THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (vf_rflow (v:real^N->real^N) s x - q) dot w`;
                 `\s. (v:real^N->real^N)(vf_rflow v s x) dot w`;
                 `a:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(v:real^N->real^N)(vf_rflow v s x) dot w` THEN
      MATCH_MP_TAC SMT_RFLOW_DOT_DERIV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMT_RFLOW_DOT_DERIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [USE_THEN "tr" MATCH_MP_TAC THEN USE_THEN "path" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SMT_TRANSVERSAL_NBHD_W = prove
 (`!(v:real^N->real^N) p w.
        v continuous (at p) /\ &0 < v p dot w
        ==> ?e. &0 < e /\ !z. norm(z - p) <= e ==> (v p dot w) / &2 <= v z dot w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < (v:real^N->real^N) p dot w` THEN
    ASM_REWRITE_TAC[DOT_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `((v:real^N->real^N) p dot w) / (&2 * norm(w:real^N))` o
    REWRITE_RULE[continuous_at]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(v:real^N->real^N) z - v p`; `w:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REWRITE_TAC[DOT_LSUB] THEN
  SUBGOAL_THEN `norm((v:real^N->real^N) z - v p) * norm(w:real^N) <=
                ((v p dot w) / (&2 * norm w)) * norm w`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((v:real^N->real^N) p dot w) / (&2 * norm(w:real^N))) * norm w =
                (v p dot w) / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(w:real^N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SMT_CROSS_INTO = prove
 (`!(v:real^N->real^N) p w r.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < v p dot w /\ &0 < r
        ==> ?d. &0 < d /\
                !s. &0 < s /\ s < d
                    ==> norm(vf_rflow v s p - p) < r /\ &0 < (vf_rflow v s p - p) dot w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "id" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `p:real^N`; `w:real^N`] SMT_TRANSVERSAL_NBHD_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")))] THEN
  MP_TAC(SPEC `p:real^N` (ASSUME
   `!x:real^N. (\s. vf_rflow (v:real^N->real^N) (drop s) x) continuous_on (:real^1)`)) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV; WITHIN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
  REWRITE_TAC[continuous_at; DROP_VEC] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(MP_TAC o SPEC `min e r`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. &0 <= u /\ u <= s ==> norm(vf_rflow (v:real^N->real^N) u p - p) < e /\
                              norm(vf_rflow v u p - p) < r`
  (LABEL_TAC "near") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift u`) THEN
    REWRITE_TAC[DIST_0; NORM_LIFT; LIFT_DROP; dist] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "near" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `p:real^N`; `p:real^N`; `w:real^N`;
                 `((v:real^N->real^N) p dot w) / &2`; `e:real`; `&0`; `s:real`]
    SMT_ORBIT_HEIGHT_INC_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "near" (MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; DOT_LZERO; REAL_SUB_RZERO; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= b ==> &0 < b`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let SMT_HALFBALL_CONNECTED = prove
 (`!(p:real^N) q w r.
        connected {z | norm(z - p) < r /\ &0 < (z - q) dot w}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
  SUBGOAL_THEN `{z:real^N | norm(z - p) < r /\ &0 < (z - q) dot w} =
                ball(p,r) INTER {z | w dot z > w dot q}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; DOT_LSUB] THEN
    MP_TAC(ISPECL [`w:real^N`; `x:real^N`] DOT_SYM) THEN
    MP_TAC(ISPECL [`w:real^N`; `q:real^N`] DOT_SYM) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_GT]]);;

(* ------------------------------------------------------------------------- *)
(* The side of the chord.  Gamma = arc UNION chord, the chord                *)
(* from a to b = gamma(TT) with normal w (v . w > 0 on it).  Near b the arc  *)
(* lies on the side (z - a) . w <= 0; open half-balls on the w side of       *)
(* chord points other than a miss Gamma for small radii, and so do chords   *)
(* shifted by d w for small d > 0.  Hence if the w side near one chord point *)
(* lies in the inside of Gamma, so does the w side near every chord point    *)
(* other than a.                                                             *)
(* ------------------------------------------------------------------------- *)

let SMT_SEGMENT_DOT = prove
 (`!(a:real^N) b w z. (b - a) dot w = &0 /\ z IN segment[a,b] ==> (z - a) dot w = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
                  DOT_LMUL; REAL_MUL_RZERO]);;

let SMT_SEGMENT_POS = prove
 (`!(a:real^N) b p.
        ~(a = b) /\ p IN segment[a,b] /\ ~(p = a) ==> &0 < (p - a) dot (b - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
                  DOT_LMUL] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [ASM_CASES_TAC `u = &0` THENL
     [UNDISCH_TAC `~(p:real^N = a)` THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[DOT_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]]);;

let SMT_ARC_IMAGE_COMPACT = prove
 (`!(v:real^N->real^N) a c d.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> compact(IMAGE (\t. vf_rflow v t a) (real_interval[c,d]))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMT_RFLOW_CONTINUOUS) THEN
  SUBGOAL_THEN `IMAGE (\t. vf_rflow (v:real^N->real^N) t a) (real_interval[c,d]) =
                IMAGE (\s. vf_rflow v (drop s) a) (interval[lift c,lift d])`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[LIFT_DROP];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let SMT_ARC_CORNER = prove
 (`!(v:real^N->real^N) a TT w.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < TT /\ &0 < v(vf_rflow v TT a) dot w
        ==> ?eps. &0 < eps /\ eps < TT /\
                  !s. TT - eps <= s /\ s <= TT
                      ==> (vf_rflow v s a - vf_rflow v TT a) dot w <= &0`,
  REPEAT GEN_TAC THEN ABBREV_TAC `b = vf_rflow (v:real^N->real^N) TT a` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `b:real^N`; `w:real^N`] SMT_TRANSVERSAL_NBHD_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")))] THEN
  MP_TAC(SPEC `a:real^N` (ASSUME
   `!x:real^N. (\s. vf_rflow (v:real^N->real^N) (drop s) x) continuous_on (:real^1)`)) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV; WITHIN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `lift TT`) THEN REWRITE_TAC[continuous_at; LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (TT / &2) (d / &2)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `a:real^N`; `b:real^N`; `w:real^N`;
                 `((v:real^N->real^N) b dot w) / &2`; `e:real`; `s:real`; `TT:real`]
    SMT_ORBIT_HEIGHT_INC_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift u`) THEN
    REWRITE_TAC[DIST_LIFT; LIFT_DROP; dist] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_LZERO] THEN
  SUBGOAL_THEN `&0 <= ((v:real^N->real^N) b dot w) / &2 * (TT - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SMT_HALFBALL_AVOIDS = prove
 (`!(v:real^2->real^2) a TT b w p eps.
        smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        vf_rflow v TT a = b /\ (b - a) dot w = &0 /\ &0 < eps /\ eps < TT /\
        (!s. TT - eps <= s /\ s <= TT ==> (vf_rflow v s a - b) dot w <= &0) /\
        (!t. t IN real_interval[&0,TT] /\ vf_rflow v t a IN segment[a,b]
             ==> t = &0 \/ t = TT) /\
        p IN segment[a,b] /\ ~(p = a)
        ==> ?r. &0 < r /\
                !z. norm(z - p) < r /\ &0 < (z - a) dot w
                    ==> ~(z IN IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                               segment[a,b])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "near") (CONJUNCTS_THEN2 (LABEL_TAC "seg")
   STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "id" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT - eps])`;
                 `p:real^2`] SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SMT_ARC_IMAGE_COMPACT THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]; ALL_TAC] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `~(p:real^2 = a)` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]);
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `TT - eps <= s` THENL
     [USE_THEN "near" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < (z - a:real^2) dot w` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(b - a:real^2) dot w = &0` THEN
      REWRITE_TAC[DOT_LSUB] THEN REAL_ARITH_TAC;
      USE_THEN "far" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN EXISTS_TAC `s:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `z:real^2`] SMT_SEGMENT_DOT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SMT_SHIFTED_AVOIDS = prove
 (`!(v:real^2->real^2) a TT b w p1 p2 eps.
        smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        vf_rflow v TT a = b /\ (b - a) dot w = &0 /\ ~(w = vec 0) /\ ~(a = b) /\
        &0 < eps /\ eps < TT /\
        (!s. TT - eps <= s /\ s <= TT ==> (vf_rflow v s a - b) dot w <= &0) /\
        (!t. t IN real_interval[&0,TT] /\ vf_rflow v t a IN segment[a,b]
             ==> t = &0 \/ t = TT) /\
        p1 IN segment[a,b] /\ ~(p1 = a) /\ p2 IN segment[a,b] /\ ~(p2 = a)
        ==> ?d0. &0 < d0 /\
                 !d z. &0 < d /\ d <= d0 /\ z IN segment[p1 + d % w,p2 + d % w]
                       ==> ~(z IN IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                                  segment[a,b])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "near") (CONJUNCTS_THEN2 (LABEL_TAC "seg")
   STRIP_ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "id" o CONJUNCT1) THEN
  (* the base chord [p1,p2] stays away from a *)
  SUBGOAL_THEN `!z:real^2. z IN segment[p1,p2] ==> &0 < (z - a) dot (b - a)`
  (LABEL_TAC "pos") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `((&1 - u) % p1 + u % p2) - a:real^2 = (&1 - u) % (p1 - a) + u % (p2 - a)`;
     DOT_LADD; DOT_LMUL] THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `p1:real^2`] SMT_SEGMENT_POS) THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `p2:real^2`] SMT_SEGMENT_POS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `u = &0` THENL
     [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1:real^2,p2] SUBSET segment[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[p1:real^2,p2]`;
                 `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT - eps])`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SEGMENT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SMT_ARC_IMAGE_COMPACT THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
      STRIP_TAC THENL
       [USE_THEN "pos" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[VECTOR_SUB_REFL; DOT_LZERO; REAL_LT_REFL];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `dd / (&2 * norm(w:real^2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `z:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z0:real^2. z0 IN segment[p1,p2] /\ z = z0 + d % w` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `z IN segment[p1 + d % w:real^2,p2 + d % w]` THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN REWRITE_TAC[SEGMENT_TRANSLATION; IN_IMAGE] THEN
    MESON_TAC[VECTOR_ADD_SYM];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `((z0 + d % w) - a:real^2) dot w = d * (w dot w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `z0:real^2`] SMT_SEGMENT_DOT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + d % w) - a:real^2 = (z0 - a) + d % w`;
                DOT_LADD; DOT_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((z0 + d % w) - a:real^2) dot w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[DOT_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `TT - eps <= s` THENL
     [USE_THEN "near" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < ((z0 + d % w) - a:real^2) dot w` THEN
      UNDISCH_TAC `(b - a:real^2) dot w = &0` THEN
      UNDISCH_TAC `z0 + d % w = vf_rflow (v:real^2->real^2) s a` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LSUB] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `s <= TT - eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sep" (MP_TAC o SPECL [`z0:real^2`; `z0 + d % w:real^2`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[dist; VECTOR_ARITH `z0 - (z0 + d % w):real^2 = --(d % w)`;
                  NORM_NEG; NORM_MUL] THEN
      SUBGOAL_THEN `abs d * norm(w:real^2) <= dd / &2` MP_TAC THENL
       [SUBGOAL_THEN `abs d = d` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `dd / (&2 * norm(w:real^2)) * norm w` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD];
        ASM_REAL_ARITH_TAC]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `z0 + d % w:real^2`]
      SMT_SEGMENT_DOT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The side lemma and the forward case.  If near the midpoint                *)
(* of the chord the w side lies in the inside of Gamma, then near every      *)
(* chord point other than a the w side lies in the inside, trajectories      *)
(* through frontier points enter the closure of the inside, and the closure  *)
(* of the inside is forward invariant.                                       *)
(* ------------------------------------------------------------------------- *)

let SMT_CHORD_SIDE = prove
 (`!(v:real^2->real^2) a TT b w eps m p rm.
        smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        vf_rflow v TT a = b /\ (b - a) dot w = &0 /\ ~(w = vec 0) /\ ~(a = b) /\
        &0 < eps /\ eps < TT /\
        (!s. TT - eps <= s /\ s <= TT ==> (vf_rflow v s a - b) dot w <= &0) /\
        (!t. t IN real_interval[&0,TT] /\ vf_rflow v t a IN segment[a,b]
             ==> t = &0 \/ t = TT) /\
        m IN segment[a,b] /\ ~(m = a) /\ p IN segment[a,b] /\ ~(p = a) /\ &0 < rm /\
        (!z. norm(z - m) < rm /\ &0 < (z - a) dot w
             ==> z IN inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                             segment[a,b])) /\
        inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION segment[a,b]) INTER
        outside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION segment[a,b]) = {}
        ==> ?r. &0 < r /\
                !z. norm(z - p) < r /\ &0 < (z - a) dot w
                    ==> z IN inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                                    segment[a,b])`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
                  segment[a,b]` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mid")
   ASSUME_TAC)))))))))))))))) THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `b:real^2`; `w:real^2`;
                 `p:real^2`; `eps:real`] SMT_HALFBALL_AVOIDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hb"))) THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `b:real^2`; `w:real^2`;
                 `m:real^2`; `p:real^2`; `eps:real`] SMT_SHIFTED_AVOIDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `d = min d0 (min (rm / (&2 * norm(w:real^2))) (r0 / (&2 * norm w)))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= d0 /\ d * norm(w:real^2) < rm /\ d * norm w < r0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rm / (&2 * norm(w:real^2)) /\ &0 < r0 / (&2 * norm w) /\
                  (rm / (&2 * norm w)) * norm w < rm /\ (r0 / (&2 * norm w)) * norm w < r0`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(rm / (&2 * norm(w:real^2))) * norm w = rm / &2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `(r0 / (&2 * norm(w:real^2))) * norm w = r0 / &2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    EXPAND_TAC "d" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(rm / (&2 * norm(w:real^2))) * norm w` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(r0 / (&2 * norm(w:real^2))) * norm w` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^2. q IN segment[a,b] ==> ((q + d % w) - a) dot w = d * (w dot w)`
  (LABEL_TAC "lift") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `q:real^2`] SMT_SEGMENT_DOT) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(q + d % w) - a:real^2 = (q - a) + d % w`;
                    DOT_LADD; DOT_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * ((w:real^2) dot w)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^2. norm((q + d % w) - q) = d * norm(w:real^2)` (LABEL_TAC "nd") THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_ADD_SUB; NORM_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the shifted chord lies in the inside *)
  SUBGOAL_THEN `segment[m + d % w,p + d % w:real^2] SUBSET inside G` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^2->bool`; `segment[m + d % w,p + d % w:real^2]`]
      SMT_CONNECTED_INSIDE_OUTSIDE) THEN
    REWRITE_TAC[CONNECTED_SEGMENT] THEN ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^2` THEN
      STRIP_TAC THEN USE_THEN "sh" (MP_TAC o SPECL [`d:real`; `z:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `m + d % w:real^2 IN inside G` ASSUME_TAC THENL
     [USE_THEN "mid" MATCH_MP_TAC THEN USE_THEN "nd" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "lift" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m + d % w:real^2`; `p + d % w:real^2`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `inside G INTER outside G:real^2->bool = {}` THEN
    UNDISCH_TAC `m + d % w:real^2 IN inside G` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the half-ball at p *)
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:real^2->bool`;
                 `{z:real^2 | norm(z - p) < r0 /\ &0 < (z - a) dot w}`]
    SMT_CONNECTED_INSIDE_OUTSIDE) THEN
  REWRITE_TAC[SMT_HALFBALL_CONNECTED] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    USE_THEN "hb" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the outside case is impossible *)
  SUBGOAL_THEN `p + d % w:real^2 IN inside G /\ p + d % w IN outside G` MP_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `segment[m + d % w,p + d % w:real^2] SUBSET inside G` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "nd" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "lift" (fun th -> ASM_SIMP_TAC[th])];
    UNDISCH_TAC `inside G INTER outside G:real^2->bool = {}` THEN SET_TAC[]]);;

let SMT_CHORD_BALL_AVOIDS_ARC = prove
 (`!(v:real^2->real^2) a TT b p.
        smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        vf_rflow v TT a = b /\
        (!t. t IN real_interval[&0,TT] /\ vf_rflow v t a IN segment[a,b]
             ==> t = &0 \/ t = TT) /\
        p IN segment[a,b] /\ ~(p = a) /\ ~(p = b)
        ==> ?r. &0 < r /\
                !z. norm(z - p) < r
                    ==> ~(z IN IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "seg")
   STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "id" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT])`;
                 `p:real^2`] SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SMT_ARC_IMAGE_COMPACT THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `~(p:real^2 = a)` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]);
        UNDISCH_TAC `~(p:real^2 = b)` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[dist] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC);;

let SMT_MIDPOINT_DICHOTOMY = prove
 (`!(G:real^2->bool) a b w r.
        open(inside G) /\ frontier(inside G) = G /\
        segment[a,b] SUBSET G /\ (b - a) dot w = &0 /\ ~(w = vec 0) /\ &0 < r /\
        (!z. norm(z - midpoint(a,b)) < r /\ ~((z - a) dot w = &0) ==> ~(z IN G))
        ==> (?r. &0 < r /\
                 !z. norm(z - midpoint(a,b)) < r /\ &0 < (z - a) dot w
                     ==> z IN inside G) \/
            (?r. &0 < r /\
                 !z. norm(z - midpoint(b,a)) < r /\ &0 < (z - b) dot --w
                     ==> z IN inside G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "av"))))))) THEN
  SUBGOAL_THEN `midpoint(b,a) = midpoint(a:real^2,b)` SUBST1_TAC THENL
   [MATCH_ACCEPT_TAC MIDPOINT_SYM; ALL_TAC] THEN
  ABBREV_TAC `m:real^2 = midpoint(a,b)` THEN
  SUBGOAL_THEN `!z:real^2. (z - b) dot --w = --((z - a) dot w)` (LABEL_TAC "neg") THENL
   [GEN_TAC THEN REWRITE_TAC[DOT_RNEG] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(b - a:real^2) dot w = &0` THEN REWRITE_TAC[DOT_LSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a point of the inside close to m off the line *)
  SUBGOAL_THEN `?z:real^2. z IN inside G /\ norm(z - m) < r /\ ~((z - a) dot w = &0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(m:real^2) IN closure(inside G)` MP_TAC THENL
     [SUBGOAL_THEN `(m:real^2) IN G` MP_TAC THENL
       [EXPAND_TAC "m" THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
        ASM SET_TAC[];
        UNDISCH_TAC `frontier(inside G:real^2->bool) = G` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(y - a:real^2) dot w = &0` THENL
     [UNDISCH_TAC `open(inside G:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      ABBREV_TAC `tau = min e (r / &2) / (&2 * norm(w:real^2))` THEN
      SUBGOAL_THEN `&0 < tau /\ tau * norm(w:real^2) < e /\ tau * norm w < r / &2`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "tau" THEN
        SUBGOAL_THEN `min e (r / &2) / (&2 * norm(w:real^2)) * norm w = min e (r / &2) / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXISTS_TAC `y + tau % w:real^2` THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `ball(y:real^2,e) SUBSET inside G` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `y - (y + t % w):real^2 = --(t % w)`;
                    NORM_NEG; NORM_MUL] THEN
        SUBGOAL_THEN `abs tau = tau` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `norm(y - m:real^2) + norm(tau % w:real^2)` THEN
        REWRITE_TAC[NORM_ARITH `norm((y + u) - m:real^2) <= norm(y - m) + norm(u)`] THEN
        UNDISCH_TAC `dist(y:real^2,m) < r / &2` THEN
        REWRITE_TAC[dist; NORM_MUL] THEN
        SUBGOAL_THEN `abs tau = tau` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[VECTOR_ARITH `(y + t % w) - a:real^2 = (y - a) + t % w`;
                        DOT_LADD; DOT_LMUL; REAL_ADD_LID] THEN
        REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
        ASM_REWRITE_TAC[DOT_EQ_0] THEN ASM_REAL_ARITH_TAC];
      EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist(y:real^2,m) < r / &2` THEN REWRITE_TAC[dist] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the two half-balls at m *)
  SUBGOAL_THEN
   `!c:real^2->bool. connected c /\ c SUBSET {y | norm(y - m) < r /\ ~((y - a) dot w = &0)} /\
                     z IN c
                     ==> c SUBSET inside G`
  (LABEL_TAC "comp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^2->bool`; `c:real^2->bool`] SMT_CONNECTED_INSIDE_OUTSIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      USE_THEN "av" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `c SUBSET {y:real^2 | norm(y - m) < r /\ ~((y - a) dot w = &0)}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c SUBSET outside(G:real^2->bool)` THEN
    UNDISCH_TAC `(z:real^2) IN c` THEN UNDISCH_TAC `(z:real^2) IN inside G` THEN
    MP_TAC(ISPEC `G:real^2->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 < (z - a:real^2) dot w \/ (z - a) dot w < &0 \/
                             (z - a) dot w = &0`) THENL
   [DISJ1_TAC THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "comp" (MP_TAC o SPEC `{y:real^2 | norm(y - m) < r /\ &0 < (y - a) dot w}`) THEN
    REWRITE_TAC[SMT_HALFBALL_CONNECTED] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
   [DISJ2_TAC THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "comp" (MP_TAC o SPEC `{y:real^2 | norm(y - m) < r /\ &0 < (y - b) dot --w}`) THEN
    REWRITE_TAC[SMT_HALFBALL_CONNECTED] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN USE_THEN "neg" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      USE_THEN "neg" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[]];
    UNDISCH_TAC `~((z - a:real^2) dot w = &0)` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The forward case of S3b (ii).                                             *)
(* ------------------------------------------------------------------------- *)

let SMT_RETURN_FORWARD = prove
 (`!(v:real^2->real^2) a TT b w.
        smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
        &0 < TT /\ vf_rflow v TT a = b /\ ~(a = b) /\
        (!s t. s IN real_interval[&0,TT] /\ t IN real_interval[&0,TT] /\
               vf_rflow v s a = vf_rflow v t a ==> s = t) /\
        (!t. &0 < t /\ t < TT ==> ~(vf_rflow v t a IN segment[a,b])) /\
        ~(w = vec 0) /\ (b - a) dot w = &0 /\ (!z. z IN segment[a,b] ==> &0 < v z dot w) /\
        (?r. &0 < r /\
             !z. norm(z - midpoint(a,b)) < r /\ &0 < (z - a) dot w
                 ==> z IN inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                                 segment[a,b]))
        ==> !t x. &0 <= t /\
                  x IN closure(inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                                      segment[a,b]))
                  ==> vf_rflow v t x IN
                      closure(inside(IMAGE (\t. vf_rflow v t a) (real_interval[&0,TT]) UNION
                                     segment[a,b]))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
                  segment[a,b]` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* the loop and the Jordan facts *)
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`] SMT_RETURN_LOOP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!s t. s IN real_interval[&0,TT] /\ t IN real_interval[&0,TT] /\
            vf_rflow (v:real^2->real^2) s a = vf_rflow v t a ==> s = t`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^2` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPEC `c:real^1->real^2` SMT_SIMPLE_LOOP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,TT] /\ vf_rflow (v:real^2->real^2) t a IN segment[a,b]
        ==> t = &0 \/ t = TT`
  (LABEL_TAC "ends") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real = TT` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `t:real` (ASSUME
     `!t. &0 < t /\ t < TT ==> ~(vf_rflow (v:real^2->real^2) t a IN segment[a,b])`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the corner at b *)
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `w:real^2`] SMT_ARC_CORNER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(ASSUME `!z. z IN segment[a,b] ==> &0 < (v:real^2->real^2) z dot w`) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT];
    DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `midpoint(a,b) IN segment[a:real^2,b] /\ ~(midpoint(a,b) = a)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT; MIDPOINT_EQ_ENDPOINT]; ALL_TAC] THEN
  (* the w side near every chord point other than a *)
  SUBGOAL_THEN
   `!p. p IN segment[a,b] /\ ~(p = a)
        ==> ?r. &0 < r /\ !z. norm(z - p) < r /\ &0 < (z - a) dot w ==> z IN inside G`
  (LABEL_TAC "side") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `b:real^2`; `w:real^2`;
                   `eps:real`; `midpoint(a:real^2,b)`; `p:real^2`; `r:real`]
      SMT_CHORD_SIDE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->bool) SUBSET closure(inside G)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier(inside G:real^2->bool) = G` THEN REWRITE_TAC[frontier] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the invariance criterion *)
  MATCH_MP_TAC SMT_INVARIANT_CRITERION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(?s0. vf_rflow (v:real^2->real^2) s0 a = p /\ &0 <= s0 /\ s0 < TT) \/
                (p IN segment[a,b] /\ ~(p = a))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^2) IN G` THEN SUBST1_TAC(SYM(ASSUME
     `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
      segment[a,b] = G`)) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_REAL_INTERVAL] THEN STRIP_TAC THENL
     [ASM_CASES_TAC `x:real = TT` THENL
       [DISJ2_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `~(a:real^2 = b)` THEN MESON_TAC[];
        DISJ1_TAC THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `p:real^2 = a` THENL
       [DISJ1_TAC THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]);
        DISJ2_TAC THEN ASM_REWRITE_TAC[]]];
    (* a point of the arc before b *)
    EXISTS_TAC `TT - s0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ASSUME `(G:real^2->bool) SUBSET closure(inside G)`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBST1_TAC(SYM(ASSUME
     `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
      segment[a,b] = G`)) THEN REWRITE_TAC[IN_UNION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    DISJ1_TAC THEN EXISTS_TAC `s0 + s` THEN
    UNDISCH_TAC `vf_rflow (v:real^2->real^2) s0 a = p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    (* a chord point other than a *)
    USE_THEN "side" (MP_TAC o SPEC `p:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hp"))) THEN
    MP_TAC(ISPECL [`v:real^2->real^2`; `p:real^2`; `w:real^2`; `rp:real`]
      SMT_CROSS_INTO) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ci"))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    USE_THEN "hp" MATCH_MP_TAC THEN
    USE_THEN "ci" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `p:real^2`] SMT_SEGMENT_DOT) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[DOT_LSUB] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* S3b (ii).  The inside U of the loop (arc and chord, or the                *)
(* periodic orbit) is a bounded connected open set with frontier the loop    *)
(* and closure a closed disc; it is forward invariant if the w side of the   *)
(* chord near its midpoint lies in U, and backward invariant otherwise (the  *)
(* forward case for the reversed field and the reversed arc); a periodic     *)
(* orbit is invariant, so its inside closure is invariant both ways.         *)
(* ------------------------------------------------------------------------- *)

let SMT_RETURN_DISK = prove
 (`SMT_RETURN_DISK_STATEMENT`,
  REWRITE_TAC[SMT_RETURN_DISK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`v:real^2->real^2`; `a:real^2`; `TT:real`] THEN
  ABBREV_TAC `b = vf_rflow (v:real^2->real^2) TT a` THEN
  ABBREV_TAC `G = IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
                  segment[a,b]` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "ret")))))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* the loop and the Jordan facts *)
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`] SMT_RETURN_LOOP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [DISCH_TAC THEN USE_THEN "ret" (MP_TAC o C MP (ASSUME `~(b:real^2 = a)`)) THEN
    SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `c:real^1->real^2` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPEC `c:real^1->real^2` SMT_SIMPLE_LOOP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  EXISTS_TAC `inside G:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(G:real^2->bool) SUBSET closure(inside G)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier(inside G:real^2->bool) = G` THEN REWRITE_TAC[frontier] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `b:real^2 = a` THENL
   [(* a periodic orbit *)
    DISJ1_TAC THEN MATCH_MP_TAC SMT_INVARIANT_CRITERION THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN EXISTS_TAC `TT:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ASSUME `(G:real^2->bool) SUBSET closure(inside G)`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `?s0. vf_rflow (v:real^2->real^2) s0 a = p /\ &0 <= s0 /\ s0 <= TT`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^2) IN G` THEN
      SUBST1_TAC(SYM(ASSUME
       `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
        segment[a,b] = G`)) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; IN_REAL_INTERVAL; SEGMENT_REFL; IN_SING] THEN
      STRIP_TAC THENL
       [EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `vf_rflow (v:real^2->real^2) s0 a = p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    SUBST1_TAC(SYM(ASSUME
     `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
      segment[a,b] = G`)) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_REAL_INTERVAL] THEN DISJ1_TAC THEN
    ASM_CASES_TAC `s0 + s <= TT` THENL
     [EXISTS_TAC `s0 + s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `s0 + s - TT` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `vf_rflow (v:real^2->real^2) TT a = a` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a return to the transversal chord *)
  USE_THEN "ret" (MP_TAC o C MP (ASSUME `~(b:real^2 = a)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "miss")) THEN
  SUBGOAL_THEN
   `!s t. s IN real_interval[&0,TT] /\ t IN real_interval[&0,TT] /\
          vf_rflow (v:real^2->real^2) s a = vf_rflow v t a ==> s = t`
  (LABEL_TAC "inj1") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{s:real,t} = {&0,TT}` THEN
    REWRITE_TAC[SET_RULE `{a:real,b} = {c,d} <=> a = c /\ b = d \/ a = d /\ b = c`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `vf_rflow (v:real^2->real^2) s a = vf_rflow v t a` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `b:real^2`] SMT_CHORD_NORMAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(b:real^2 = a)` THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,TT] /\ vf_rflow (v:real^2->real^2) t a IN segment[a,b]
        ==> t = &0 \/ t = TT`
  (LABEL_TAC "ends") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real = TT` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "miss" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(a,b) IN segment[a:real^2,b] /\ ~(midpoint(a,b) = a) /\
                ~(midpoint(a,b) = b)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT; MIDPOINT_EQ_ENDPOINT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `b:real^2`; `midpoint(a:real^2,b)`]
    SMT_CHORD_BALL_AVOIDS_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
  MP_TAC(ISPECL [`G:real^2->bool`; `a:real^2`; `b:real^2`; `w:real^2`; `r:real`]
    SMT_MIDPOINT_DICHOTOMY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME
       `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
        segment[a,b] = G`)) THEN SET_TAC[];
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      SUBST1_TAC(SYM(ASSUME
       `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
        segment[a,b] = G`)) THEN
      REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `w:real^2`; `z:real^2`] SMT_SEGMENT_DOT) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [(* the w side: forward invariance *)
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`v:real^2->real^2`; `a:real^2`; `TT:real`; `b:real^2`; `w:real^2`]
      SMT_RETURN_FORWARD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the other side: backward invariance from the reversed field *)
  DISJ2_TAC THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_REVERSE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))) THEN
  SUBGOAL_THEN
   `!t. vf_rflow (\x. --((v:real^2->real^2) x)) t b = vf_rflow v (TT - t) a`
  (LABEL_TAC "back") THENL
   [GEN_TAC THEN USE_THEN "rev" (fun th -> REWRITE_TAC[th]) THEN
    SUBST1_TAC(SYM(ASSUME `vf_rflow (v:real^2->real^2) TT a = b`)) THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\t. vf_rflow (\x. --((v:real^2->real^2) x)) t b) (real_interval[&0,TT]) UNION
    segment[b,a] = G`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `IMAGE (\t. vf_rflow (v:real^2->real^2) t a) (real_interval[&0,TT]) UNION
      segment[a,b] = G`)) THEN
    USE_THEN "back" (fun th -> REWRITE_TAC[th]) THEN BINOP_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real^2` THEN EQ_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `TT - t` THEN ASM_REWRITE_TAC[REAL_ARITH `TT - (TT - t) = t`] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_ACCEPT_TAC(CONJUNCT1 SEGMENT_SYM)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --((v:real^2->real^2) x)`; `b:real^2`; `TT:real`; `a:real^2`;
                 `--w:real^2`] SMT_RETURN_FORWARD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `segment[b,a] = segment[a:real^2,b]` (LABEL_TAC "sab") THENL
     [MATCH_ACCEPT_TAC(CONJUNCT1 SEGMENT_SYM); ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `TT - s = TT - t ==> s = t`) THEN
      USE_THEN "inj1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s IN real_interval[&0,TT]` THEN
      UNDISCH_TAC `t IN real_interval[&0,TT]` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "miss" (MP_TAC o SPEC `TT - t`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sab" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[VECTOR_NEG_EQ_0] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DOT_RNEG; REAL_NEG_EQ_0] THEN
      UNDISCH_TAC `(b - a:real^2) dot w = &0` THEN REWRITE_TAC[DOT_LSUB] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
      USE_THEN "sab" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `r':real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:real^2`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--t:real`; `x:real^2`]) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* S3b for complete fields.  A periodic point of a nonvanishing              *)
(* field has a minimal period (no periods below the crossing time of the     *)
(* transversal through it, first hit after that); a bounded forward          *)
(* half-orbit gives a periodic orbit or a return (S3b (i)), hence an         *)
(* invariant closed disc (S3b (ii)), hence a zero of v or of -v (S3b (iii)). *)
(* ------------------------------------------------------------------------- *)

let SMT_MINIMAL_PERIOD = prove
 (`!(v:real^N->real^N) p TT.
        smooth_map_on (:real^N) v /\ (!y. ~(v y = vec 0)) /\
        (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        &0 < TT /\ vf_rflow v TT p = p
        ==> ?T0. &0 < T0 /\ vf_rflow v T0 p = p /\
                 !s t. s IN real_interval[&0,T0] /\ t IN real_interval[&0,T0] /\
                       vf_rflow v s p = vf_rflow v t p
                       ==> s = t \/ {s,t} = {&0,T0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  MP_TAC(ISPEC `v:real^N->real^N` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* no small periods *)
  MP_TAC(ISPECL [`v:real^N->real^N`; `p:real^N`; `(v:real^N->real^N) p`; `&1`]
    SMT_CROSS_INTO) THEN
  ASM_REWRITE_TAC[DOT_POS_LT; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))) THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < d ==> ~(vf_rflow (v:real^N->real^N) s p = p)`
  (LABEL_TAC "np") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "small" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_LZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= TT` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "np" (MP_TAC o SPEC `TT:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the first return after d / 2 *)
  MP_TAC(ISPECL [`\u:real^1. vf_rflow (v:real^N->real^N) (drop u) p`; `{p:real^N}`;
                 `d / &2`; `TT:real`] SMT_FIRST_HIT) THEN
  REWRITE_TAC[LIFT_DROP; IN_SING; CLOSED_SING] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "first"))))) THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < T0 ==> ~(vf_rflow (v:real^N->real^N) s p = p)`
  (LABEL_TAC "all") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s < d` THENL
     [USE_THEN "np" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      USE_THEN "first" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ s < t /\ t <= T0 /\ vf_rflow (v:real^N->real^N) s p = vf_rflow v t p
          ==> s = &0 /\ t = T0`
  (LABEL_TAC "ord") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `vf_rflow (v:real^N->real^N) (t - s) p = p` ASSUME_TAC THENL
     [USE_THEN "grp" (MP_TAC o SPECL [`t:real`; `--s`; `p:real^N`]) THEN
      UNDISCH_TAC `vf_rflow (v:real^N->real^N) s p = vf_rflow v t p` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_ADD_RINV; REAL_SUB_REFL; REAL_ARITH `t + --s = t - s`] THEN
      USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    ASM_CASES_TAC `t - s < T0` THENL
     [USE_THEN "all" (MP_TAC o SPEC `t - s`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `s < t \/ s = t \/ t < s`) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THENL
   [USE_THEN "ord" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "ord" (MP_TAC o SPECL [`t:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[INSERT_COMM]]]);;

let SMT_NO_BOUNDED_COMPLETE = prove
 (`!(v:real^2->real^2) x.
        smooth_map_on (:real^2) v /\ (!y. ~(v y = vec 0)) /\
        (!y. ode_vf_maxint v (:real^2) y = (:real^1))
        ==> ~bounded(IMAGE (\t. vf_rflow v t x) {t | &0 <= t})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  (* no invariant closed disc *)
  SUBGOAL_THEN
   `!D:real^2->bool.
        D homeomorphic cball(vec 0:real^2,&1) /\
        ((!t y. &0 <= t /\ y IN D ==> vf_rflow v t y IN D) \/
         (!t y. t <= &0 /\ y IN D ==> vf_rflow v t y IN D))
        ==> F`
  (LABEL_TAC "nodisc") THENL
   [GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [MP_TAC(REWRITE_RULE[SMT_INVARIANT_DISK_ZERO_STATEMENT]
        (ISPEC `(:2)` SMT_INVARIANT_DISK_ZERO)) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^2->real^2`; `D:real^2->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MP_TAC(ISPEC `v:real^2->real^2` SMT_RFLOW_REVERSE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "rev"))) THEN
      MP_TAC(REWRITE_RULE[SMT_INVARIANT_DISK_ZERO_STATEMENT]
        (ISPEC `(:2)` SMT_INVARIANT_DISK_ZERO)) THEN
      DISCH_THEN(MP_TAC o SPECL [`\x. --((v:real^2->real^2) x)`; `D:real^2->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "rev" (fun th -> REWRITE_TAC[th]) THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_NEG_EQ_0] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`v:real^2->real^2`; `x:real^2`]
    (REWRITE_RULE[SMT_TRANSVERSE_RETURN_STATEMENT] SMT_TRANSVERSE_RETURN)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `TT:real` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `TT:real` STRIP_ASSUME_TAC))) THENL
   [(* a periodic orbit *)
    MP_TAC(ISPECL [`v:real^2->real^2`; `vf_rflow (v:real^2->real^2) t0 x`; `TT:real`]
      SMT_MINIMAL_PERIOD) THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `T0:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`v:real^2->real^2`; `vf_rflow (v:real^2->real^2) t0 x`; `T0:real`]
      (REWRITE_RULE[SMT_RETURN_DISK_STATEMENT] SMT_RETURN_DISK)) THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "nodisc" MATCH_MP_TAC THEN EXISTS_TAC `closure U:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    (* a return *)
    SUBGOAL_THEN
     `?U:real^2->bool.
        closure U homeomorphic cball(vec 0:real^2,&1) /\
        ((!t y. &0 <= t /\ y IN closure U ==> vf_rflow (v:real^2->real^2) t y IN closure U) \/
         (!t y. t <= &0 /\ y IN closure U ==> vf_rflow v t y IN closure U))`
    (X_CHOOSE_THEN `U:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [MP_TAC(SPECL [`v:real^2->real^2`; `vf_rflow (v:real^2->real^2) t0 x`; `TT:real`]
        (REWRITE_RULE[SMT_RETURN_DISK_STATEMENT] SMT_RETURN_DISK)) THEN
      USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN DISJ1_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[]];
      USE_THEN "nodisc" MATCH_MP_TAC THEN EXISTS_TAC `closure U:real^2->bool` THEN
      ASM_REWRITE_TAC[]]]);;

