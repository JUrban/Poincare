(* ========================================================================= *)
(* Unit pc_rfa_r1: the chart C^m bounds R1 (PDE_REQ_DERIV_BOUNDS) from       *)
(* global bounds of |nabla^j Rm| on the manifold and the metric equivalence  *)
(* along the flow: a calculus of uniformly jet-bounded families, the         *)
(* coordinate jet bound for tensors, the evolution of the Christoffel        *)
(* symbols in a fixed chart, and the induction on the order.                 *)
(* ========================================================================= *)

needs "src/pc_rfa_shi.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_rf_extend.ml";;
needs "src/pc_pde_seeley.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Uniformly jet-bounded families.  rfa_jb Js V K m f: for every             *)
(* t in I the function f t is smooth on the open set V, and its partial      *)
(* derivatives of order <= m are bounded on K uniformly in t.               *)
(* ========================================================================= *)

let rfa_jb = new_definition
 `rfa_jb (Js:real->bool) (V:real^N->bool) (K:real^N->bool) (m:num)
         (f:real->real^N->real) <=>
    (!t. t IN Js ==> smooth_map_on V (\z. lift(f t z))) /\
    ?C. !t l y. t IN Js /\ l IN pde_index_lists m (:N) /\ y IN K
                ==> abs(drop(iterated_partial l (\z. lift(f t z)) y)) <= C`;;

let rfa_pd = new_definition
 `rfa_pd (i:num) (f:real->real^N->real) =
    \t z. drop(partial_derivative i (\z. lift(f t z)) z)`;;

let RFA_PD_LIFT = prove
 (`!i (f:real->real^N->real) t.
     (\z. lift(rfa_pd i f t z)) = partial_derivative i (\z. lift(f t z))`,
  REWRITE_TAC[rfa_pd; LIFT_DROP; ETA_AX]);;

let RFA_JB_ZERO = prove
 (`!Js V K (f:real->real^N->real).
     rfa_jb Js V K 0 f <=>
     (!t. t IN Js ==> smooth_map_on V (\z. lift(f t z))) /\
     ?C. !t y. t IN Js /\ y IN K ==> abs(f t y) <= C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_jb] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `C:real` THEN
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE; LENGTH_EQ_NIL] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `[]:num list`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[ALL; iterated_partial; LIFT_DROP];
    ASM_REWRITE_TAC[iterated_partial; LIFT_DROP] THEN ASM_SIMP_TAC[]]);;

let RFA_JB_MONO = prove
 (`!Js V K m n (f:real->real^N->real).
     m <= n /\ rfa_jb Js V K n f ==> rfa_jb Js V K m f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_jb] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:num`; `n:num`; `(:N)`] PDE_INDEX_LISTS_MONO) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RFA_LIST_SNOC = prove
 (`!l:(num)list. ~(l = []) ==> ?l1 x. l = APPEND l1 [x]`,
  MESON_TAC[APPEND_BUTLAST_LAST]);;

let RFA_JB_SUC = prove
 (`!Js V K m (f:real->real^N->real).
     open V
     ==> (rfa_jb Js V K (SUC m) f <=>
          rfa_jb Js V K 0 f /\
          !i. 1 <= i /\ i <= dimindex(:N) ==> rfa_jb Js V K m (rfa_pd i f))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_jb]) THEN
    REWRITE_TAC[rfa_jb; RFA_PD_LIFT] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `APPEND l [i:num]`; `y:real^N`]) THEN
    REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l IN pde_index_lists m (:N)` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH_APPEND; ALL_APPEND; ALL;
                LENGTH] THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RFA_JB_ZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `C0:real`)) MP_TAC) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[rfa_jb; RFA_PD_LIFT;
    TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`; FORALL_AND_THM]) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_TAC `Ci:num->real`) THEN
  REWRITE_TAC[rfa_jb] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `abs C0 + sum(1..dimindex(:N)) (\i. abs((Ci:num->real) i))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (\i. abs((Ci:num->real) i))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `l:num list = []` THENL
   [ASM_REWRITE_TAC[iterated_partial; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 <= sum(1..dimindex(:N)) (\i. abs((Ci:num->real) i))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LIST_SNOC) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num list` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `APPEND l1 [i:num] IN pde_index_lists (SUC m) (:N)` THEN
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN
  STRIP_TAC THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Ci:num->real) i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= s /\ &0 <= abs c ==> x <= abs c + s`) THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    MP_TAC(ISPECL [`\i. abs((Ci:num->real) i)`;
                   `sum(1..dimindex(:N)) (\i. abs((Ci:num->real) i))`;
                   `1..dimindex(:N)`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS; REAL_LE_REFL; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFA_JB_EQ = prove
 (`!Js V K m (f:real->real^N->real) h.
     open V /\ K SUBSET V /\ (!t z. t IN Js /\ z IN V ==> f t z = h t z) /\
     rfa_jb Js V K m f
     ==> rfa_jb Js V K m h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_jb] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. lift((f:real->real^N->real) t z)` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                   `\z. lift((h:real->real^N->real) t z)`;
                   `\z. lift((f:real->real^N->real) t z)`]
           TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[]]);;

let RFA_JB_ADD = prove
 (`!Js V K m (f:real->real^N->real) h.
     open V /\ K SUBSET V /\ rfa_jb Js V K m f /\ rfa_jb Js V K m h
     ==> rfa_jb Js V K m (\t z. f t z + h t z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_jb] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `C1:real`))
                     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `C2:real`))))) THEN
  REWRITE_TAC[LIFT_ADD] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `C1 + C2:real` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                 `\z. lift((f:real->real^N->real) t z)`;
                 `\z. lift((h:real->real^N->real) t z)`]
         PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= a /\ abs y <= b ==> abs(x + y) <= a + b`) THEN
  ASM_SIMP_TAC[]);;

let RFA_ITERATED_PARTIAL_CONST = prove
 (`!l (c:real^P).
     iterated_partial l (\z:real^M. c) = if l = [] then (\z. c) else (\z. vec 0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT; FRECHET_DERIVATIVE_CONST_AT]);;

let RFA_JB_CONST = prove
 (`!Js V K m c. open V ==> rfa_jb Js V K m (\t (z:real^N). c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_jb; SMOOTH_MAP_ON_CONST] THEN
  EXISTS_TAC `abs c` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[RFA_ITERATED_PARTIAL_CONST] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let RFA_JB_MUL0 = prove
 (`!Js V K (f:real->real^N->real) h.
     open V /\ rfa_jb Js V K 0 f /\ rfa_jb Js V K 0 h
     ==> rfa_jb Js V K 0 (\t z. f t z * h t z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RFA_JB_ZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `C1:real`))
                     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `C2:real`)))) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[];
    EXISTS_TAC `abs C1 * abs C2` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN ASM_SIMP_TAC[]]);;

let RFA_JB_MUL = prove
 (`!m Js V K (f:real->real^N->real) h.
     open V /\ K SUBSET V /\ rfa_jb Js V K m f /\ rfa_jb Js V K m h
     ==> rfa_jb Js V K m (\t z. f t z * h t z)`,
  INDUCT_TAC THENL [MESON_TAC[RFA_JB_MUL0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RFA_JB_SUC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_JB_MUL0 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN Js ==> smooth_map_on V (\z. lift((f:real->real^N->real) t z)) /\
                    smooth_map_on V (\z. lift((h:real->real^N->real) t z))`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfa_jb]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t z. rfa_pd i (f:real->real^N->real) t z * h t z +
                    f t z * rfa_pd i (h:real->real^N->real) t z` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[rfa_pd; partial_derivative] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFA_FRECHET_LIFT_MUL THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfa_jb Js V K (SUC m) (f:real->real^N->real)` THEN
      ASM_SIMP_TAC[RFA_JB_SUC];
      MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN
      ASM_REWRITE_TAC[ARITH_RULE `m <= SUC m`]];
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN
      ASM_REWRITE_TAC[ARITH_RULE `m <= SUC m`];
      UNDISCH_TAC `rfa_jb Js V K (SUC m) (h:real->real^N->real)` THEN
      ASM_SIMP_TAC[RFA_JB_SUC]]]);;

let RFA_JB_CMUL = prove
 (`!Js V K m c (f:real->real^N->real).
     open V /\ K SUBSET V /\ rfa_jb Js V K m f
     ==> rfa_jb Js V K m (\t z. c * f t z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `\(t:real) (z:real^N). (c:real)`; `f:real->real^N->real`] RFA_JB_MUL) THEN
  ASM_SIMP_TAC[RFA_JB_CONST]);;

let RFA_JB_NEG = prove
 (`!Js V K m (f:real->real^N->real).
     open V /\ K SUBSET V /\ rfa_jb Js V K m f
     ==> rfa_jb Js V K m (\t z. --(f t z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t z. --(&1) * (f:real->real^N->real) t z` THEN
  ASM_SIMP_TAC[RFA_JB_CMUL] THEN REAL_ARITH_TAC);;

let RFA_JB_SUB = prove
 (`!Js V K m (f:real->real^N->real) h.
     open V /\ K SUBSET V /\ rfa_jb Js V K m f /\ rfa_jb Js V K m h
     ==> rfa_jb Js V K m (\t z. f t z - h t z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t z. (f:real->real^N->real) t z + --(h t z)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_SIMP_TAC[RFA_JB_NEG]);;

let RFA_JB_SUM = prove
 (`!Js V K m (fi:num->real->real^N->real) n.
     open V /\ K SUBSET V /\
     (!i. 1 <= i /\ i <= n ==> rfa_jb Js V K m (fi i))
     ==> rfa_jb Js V K m (\t z. sum(1..n) (\i. fi i t z))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN SIMP_TAC[RFA_JB_CONST]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* ========================================================================= *)
(* Integration in time.  Spatial jets of a jointly smooth                    *)
(* family are jointly smooth and their time derivatives are the jets of the  *)
(* time derivative; hence jet bounds for the time derivative on (a,b) and    *)
(* the initial data give jet bounds on [a,b).                                *)
(* ========================================================================= *)

let rfa_jet = new_definition
 `rfa_jet (l:num list) (f:real->real^N->real) =
    \t z. drop(iterated_partial l (\z. lift(f t z)) z)`;;

let RFA_JET_LIFT = prove
 (`!l (f:real->real^N->real) t.
     (\z. lift(rfa_jet l f t z)) = iterated_partial l (\z. lift(f t z))`,
  REWRITE_TAC[rfa_jet; LIFT_DROP; ETA_AX]);;

let RFA_JET_CONS = prove
 (`!i l (f:real->real^N->real).
     rfa_jet (CONS i l) f = rfa_pd i (rfa_jet l f)`,
  REWRITE_TAC[rfa_jet; rfa_pd; iterated_partial; LIFT_DROP; ETA_AX]);;

let RFA_JET_JOINT_SMOOTH = prove
 (`!W (f:real->real^N->real) l.
     open W /\
     smooth_map_on W (\w. lift(f (drop(fstcart w)) (sndcart w)))
     ==> smooth_map_on W (\w. lift(rfa_jet l f (drop(fstcart w)) (sndcart w)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[rfa_jet; iterated_partial; LIFT_DROP]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[RFA_JET_CONS; rfa_pd; LIFT_DROP; partial_derivative] THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `\w. lift(rfa_jet t (f:real->real^N->real)
                             (drop(fstcart w)) (sndcart w))`;
                 `basis h:real^N`] LRG_JOINT_PARTIAL) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let RFA_JET_DT = prove
 (`!U a b (f:real->real^N->real) f' l t z.
     open U /\ a < t /\ t < b /\ z IN U /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
       (\w. lift(f (drop(fstcart w)) (sndcart w))) /\
     (!s y. a < s /\ s < b /\ y IN U ==> ((\r. f r y) has_real_derivative f' s y) (atreal s))
     ==> ((\s. rfa_jet l f s z) has_real_derivative rfa_jet l f' t z) (atreal t)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[rfa_jet; iterated_partial; LIFT_DROP] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_JET_CONS; rfa_pd; partial_derivative] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `\s:real (y:real^N) (u:num->real^N). rfa_jet t (f:real->real^N->real) s y`;
                 `\(y:real^N) (u:num->real^N). rfa_jet t (f':real->real^N->real) t' y`;
                 `t':real`; `z:real^N`; `(\m. vec 0):num->real^N`; `basis h:real^N`]
         RFA_DT_SPACE_DERIV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_JET_JOINT_SMOOTH THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFA_JET_SLICE_CONTINUOUS = prove
 (`!W (f:real->real^N->real) l y s.
     open W /\ smooth_map_on W (\w. lift(f (drop(fstcart w)) (sndcart w))) /\
     pastecart (lift s) y IN W
     ==> (\r. rfa_jet l f r y) real_continuous (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `\w. lift(rfa_jet l (f:real->real^N->real) (drop(fstcart w)) (sndcart w))`;
                 `\x:real^1. x`; `y:real^N`; `s:real`] RFA_TSLICE_CONTINUOUS) THEN
  ASM_SIMP_TAC[RFA_JET_JOINT_SMOOTH; LINEAR_ID] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; ETA_AX]);;

let RFA_W_SLICE_SMOOTH = prove
 (`!W (Fm:real^(1,N)finite_sum->real^P) V t0.
     open W /\ open V /\ smooth_map_on W Fm /\
     (!y. y IN V ==> pastecart (lift t0) y IN W)
     ==> smooth_map_on V (\y. Fm(pastecart (lift t0) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t0) y)) =
                Fm o (\y:real^N. pastecart (lift t0) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let RFA_JB_TIME = prove
 (`!V K a b W m (f:real->real^N->real) f'.
     open V /\ compact K /\ K SUBSET V /\ a < b /\ open W /\
     (!t z. a <= t /\ t < b /\ z IN V ==> pastecart (lift t) z IN W) /\
     smooth_map_on W (\w. lift(f (drop(fstcart w)) (sndcart w))) /\
     (!s y. a < s /\ s < b /\ y IN V
            ==> ((\r. f r y) has_real_derivative f' s y) (atreal s)) /\
     rfa_jb {t | a < t /\ t < b} V K m f'
     ==> rfa_jb {t | a <= t /\ t < b} V K m f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))))) THEN
  REWRITE_TAC[rfa_jb; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `C1:real`)) THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> smooth_map_on V (\z. lift((f:real->real^N->real) t z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\w. lift((f:real->real^N->real) (drop(fstcart w)) (sndcart w))`;
                   `V:real^N->bool`; `t:real`] RFA_W_SLICE_SMOOTH) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!l. ?bl. !y. y IN K ==> abs(rfa_jet l (f:real->real^N->real) a y) <= bl`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `\z. lift((f:real->real^N->real) a z)`;
                   `K:real^N->bool`; `l:num list`] PDE_SMOOTH_PARTIAL_BOUNDED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `bb:real`) THEN EXISTS_TAC `bb:real` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_jet] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(iterated_partial l (\z. lift((f:real->real^N->real) a z)) y)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[NORM_REAL; GSYM drop; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `bl:num list->real`) THEN
  EXISTS_TAC `sum(pde_index_lists m (:N)) (\l. abs((bl:num list->real) l)) +
              (b - a) * abs C1` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(rfa_jet l (f:real->real^N->real) a y) <=
                sum(pde_index_lists m (:N)) (\l. abs((bl:num list->real) l))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((bl:num list->real) l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`\l. abs((bl:num list->real) l)`;
                     `sum(pde_index_lists m (:N)) (\l. abs((bl:num list->real) l))`;
                     `pde_index_lists m (:N)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_ABS_POS; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b - a) * abs C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(iterated_partial l (\z. lift((f:real->real^N->real) t z)) y) =
                rfa_jet l f t y` SUBST1_TAC THENL [REWRITE_TAC[rfa_jet]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. rfa_jet l (f:real->real^N->real) r y`;
                 `\r. rfa_jet l (f':real->real^N->real) r y`; `a:real`; `t:real`]
         REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC RFA_JET_SLICE_CONTINUOUS THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC RFA_JET_DT THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1] THEN
      REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(rfa_jet l (f':real->real^N->real) xi y) <= C1` MP_TAC THENL
   [REWRITE_TAC[rfa_jet] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs(rfa_jet l (f':real->real^N->real) xi y * (t - a)) <= (b - a) * abs C1`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfa_jet l (f:real->real^N->real) t y - rfa_jet l f a y =
               rfa_jet l (f':real->real^N->real) xi y * (t - a)` THEN
  UNDISCH_TAC `abs(rfa_jet l (f:real->real^N->real) a y) <=
               sum(pde_index_lists m (:N)) (\l. abs((bl:num list->real) l))` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The coordinate jet bound.  Partial derivatives of tensor                  *)
(* components are covariant derivative components plus Christoffel terms;   *)
(* hence bounds on the components of nabla^j T (j <= m) and jet bounds of    *)
(* order m-1 on the Christoffel symbols give jet bounds of order m on T.     *)
(* ========================================================================= *)

let RFA_PD_TENSOR_COMP = prove
 (`!k U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) z (al:num->num) i.
     metric_field U G /\ ltensor_field k U Tf /\
     (!u. smooth_map_on U (\x. lift(Tf x u))) /\ z IN U /\
     al IN index_tuples k (:N) /\ 1 <= i /\ i <= dimindex(:N)
     ==> drop(frechet_derivative (\x. lift(Tf x (\r. basis(al r)))) (at z) (basis i)) =
         lnabla k G Tf z (\r. if r = k + 1 then basis i else basis(al r)) +
         sum(1..k) (\r. sum(1..dimindex(:N))
                     (\s. (christoffel G z (basis i) (basis(al r)))$s *
                          Tf z (\j. if j = r then basis s else basis(al j))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> (Tf:real^N->(num->real^N)->real) x
              (\r. if r = k + 1 then basis i else basis(al r)) =
            Tf x (\r. basis(al r))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field k U (Tf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lnabla] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\x. lift((Tf:real^N->(num->real^N)->real) x
                  (\r. if r = k + 1 then basis i else basis(al r)))) (at z) =
    frechet_derivative (\x. lift(Tf x (\r. basis(al r)))) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `k + 1 = k + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `y = x ==> d = (d - x) + y`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~(r = k + 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(Tf:real^N->(num->real^N)->real) z
                (\j. if j = r then christoffel G z (basis i) (basis(al r))
                     else basis(al j))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`(Tf:real^N->(num->real^N)->real) z`; `r:num`;
                   `\j. basis((al:num->num) j):real^N`;
                   `christoffel (G:real^N->real^N^N) z (basis i) (basis((al:num->num) r))`]
           LRG_SLOT_EXPAND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field k U (Tf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:num`; `\j. basis((al:num->num) j):real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
    check (fun th -> concl th = `ltensor_field k U (Tf:real^N->(num->real^N)->real)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m:num = r` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let RFA_INDEX_TUPLES_EXT = prove
 (`!k (al:num->num) i.
     al IN index_tuples k (:N) /\ 1 <= i /\ i <= dimindex(:N)
     ==> (\r. if r = k + 1 then i else al r) IN index_tuples (k + 1) (:N)`,
  REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))
                             STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY(USE_THEN "in" MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
  TRY(USE_THEN "out" MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN TRY ASM_ARITH_TAC);;

let RFA_INDEX_TUPLES_UPD = prove
 (`!k (al:num->num) r s.
     al IN index_tuples k (:N) /\ 1 <= r /\ r <= k /\ 1 <= s /\ s <= dimindex(:N)
     ==> (\j. if j = r then s else al j) IN index_tuples k (:N)`,
  REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))
                             STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY(USE_THEN "in" MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
  TRY(USE_THEN "out" MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN TRY ASM_ARITH_TAC);;

let RFA_COORD_JET = prove
 (`!m k (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real) Js V K.
     open V /\ K SUBSET V /\
     (!t. t IN Js ==> metric_field V (G t)) /\
     (!t. t IN Js ==> ltensor_field k V (Tf t) /\
                      (!u. smooth_map_on V (\z. lift(Tf t z u)))) /\
     (!j al. j <= m /\ al IN index_tuples (k + j) (:N)
             ==> rfa_jb Js V K 0
                   (\t z. lnabla_iter k j (G t) (Tf t) z (\r. basis(al r)))) /\
     (1 <= m
      ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                  1 <= s /\ s <= dimindex(:N)
                  ==> rfa_jb Js V K (m - 1)
                        (\t z. (christoffel (G t) z (basis i) (basis j))$s))
     ==> !al. al IN index_tuples k (:N)
              ==> rfa_jb Js V K m (\t z. Tf t z (\r. basis(al r)))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "nb") (K ALL_TAC)))))) THEN
    X_GEN_TAC `al:num->num` THEN DISCH_TAC THEN
    USE_THEN "nb" (MP_TAC o SPECL [`0`; `al:num->num`]) THEN
    REWRITE_TAC[LE_REFL; ADD_CLAUSES; lnabla_iter] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tf")
    (CONJUNCTS_THEN2 (LABEL_TAC "nb") (LABEL_TAC "gam")))))) THEN
  SUBGOAL_THEN
   `!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
            1 <= s /\ s <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. (christoffel ((G:real->real^N->real^N^N) t) z (basis i) (basis j))$s)`
  (LABEL_TAC "gm") THENL
   [USE_THEN "gam" (MP_TAC o C MP (ARITH_RULE `1 <= SUC m`)) THEN
    REWRITE_TAC[ARITH_RULE `SUC m - 1 = m`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1 <= m
    ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                1 <= s /\ s <= dimindex(:N)
                ==> rfa_jb Js V K (m - 1)
                      (\t z. (christoffel ((G:real->real^N->real^N^N) t) z (basis i) (basis j))$s)`
  (LABEL_TAC "gm1") THENL
   [DISCH_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MONO THEN
    EXISTS_TAC `m:num` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    USE_THEN "gm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `al:num->num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RFA_JB_SUC] THEN CONJ_TAC THENL
   [USE_THEN "nb" (MP_TAC o SPECL [`0`; `al:num->num`]) THEN
    REWRITE_TAC[LE_0; ADD_CLAUSES; lnabla_iter] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t z. lnabla k ((G:real->real^N->real^N^N) t) ((Tf:real->real^N->(num->real^N)->real) t) z (\r. if r = k + 1 then basis i else basis(al r)) +
          sum(1..k) (\r. sum(1..dimindex(:N))
            (\s. (christoffel (G t) z (basis i) (basis(al r)))$s *
                 Tf t z (\j. if j = r then basis s else basis(al j))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[rfa_pd; partial_derivative] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFA_PD_TENSOR_COMP THEN EXISTS_TAC `V:real^N->bool` THEN
    USE_THEN "tf" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPECL [`k + 1`; `(G:real->real^N->real^N^N)`;
      `\t. lnabla k ((G:real->real^N->real^N^N) t) ((Tf:real->real^N->(num->real^N)->real) t)`; `Js:real->bool`; `V:real^N->bool`;
      `K:real^N->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN
        USE_THEN "tf" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`j:num`; `be:num->num`] THEN STRIP_TAC THEN
        REWRITE_TAC[RFA_LNABLA_ITER_SHIFT] THEN USE_THEN "nb" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(be:num->num) IN index_tuples ((k + 1) + j) (:N)` THEN
        REWRITE_TAC[ARITH_RULE `(k + 1) + j = k + j + 1`]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `\r. if r = k + 1 then i else (al:num->num) r`) THEN
    ASM_SIMP_TAC[RFA_INDEX_TUPLES_EXT] THEN REWRITE_TAC[COND_RAND];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "gm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(al:num->num) IN index_tuples k (:N)` THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`k:num`; `(G:real->real^N->real^N^N)`; `(Tf:real->real^N->(num->real^N)->real)`; `Js:real->bool`;
                                 `V:real^N->bool`; `K:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\j. if j = r then s else (al:num->num) j`) THEN
  ASM_SIMP_TAC[RFA_INDEX_TUPLES_UPD] THEN REWRITE_TAC[COND_RAND]);;

(* ========================================================================= *)
(* Smoothness of the Christoffel symbols of a family of                      *)
(* matrices given by a smooth map on an open set W of (t,y), where the       *)
(* matrices are invertible.                                                  *)
(* ========================================================================= *)

let RFA_W_MDERIV_SMOOTH = prove
 (`!W (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod) w0.
     open W /\ smooth_map_on W Fm
     ==> smooth_map_on W
           (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                (mderiv (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                        (sndcart w) w0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv; VECTORIZE_MATRIFY; o_DEF] THEN
  REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod`; `w0:real^N`]
         LRG_JOINT_PARTIAL) THEN
  ASM_REWRITE_TAC[]);;

let RFA_W_MDERIV_ENTRY_SMOOTH = prove
 (`!W (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod) w0 v c k.
     open W /\ smooth_map_on W Fm
     ==> smooth_map_on W
           (\w. lift((mderiv (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                             (sndcart w) w0 ** v)$k)) /\
         smooth_map_on W
           (\w. lift(c dot (mderiv (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                                   (sndcart w) w0 ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod`; `w0:real^N`]
         RFA_W_MDERIV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift((mderiv (\y. matrify((Fm:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                     (pastecart (fstcart w) y)):real^N^N)
                       (sndcart w) w0 ** v)$k)) =
      (\m:real^(N,N)finite_prod. lift(((matrify m:real^N^N) ** v)$k)) o
      (\w. vectorize(mderiv (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                            (sndcart w) w0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_MUL_COMPONENT];
    SUBGOAL_THEN
     `(\w. lift(c dot (mderiv (\y. matrify((Fm:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                            (pastecart (fstcart w) y)):real^N^N)
                              (sndcart w) w0 ** v))) =
      (\m:real^(N,N)finite_prod. lift(c dot ((matrify m:real^N^N) ** v))) o
      (\w. vectorize(mderiv (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                            (sndcart w) w0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT]]);;

let RFA_W_CHRISTOFFEL_SMOOTH = prove
 (`!W (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod) u v.
     open W /\ smooth_map_on W Fm /\
     (!w. w IN W ==> ~(det(matrify(Fm w):real^N^N) = &0))
     ==> smooth_map_on W
           (\w. christoffel (\y. matrify(Fm(pastecart (fstcart w) y)):real^N^N)
                            (sndcart w) u v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[christoffel; PASTECART_FST_SND] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\w. matrify((Fm:real^(1,N)finite_sum->real^(N,N)finite_prod) w):real^N^N`]
           LRG_SMOOTH_MATRIX_INV) THEN
    ASM_REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE
    (ASSUME `open(W:real^(1,N)finite_sum->bool)`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RFA_W_MDERIV_ENTRY_SMOOTH];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[RFA_W_MDERIV_ENTRY_SMOOTH]]);;

(* ========================================================================= *)
(* The metric of a flow from a in a fixed chart: an open set W               *)
(* of (t,y) containing [a,b) x V on which the smooth extension FF is         *)
(* invertible; the Christoffel symbols of the extension, their agreement     *)
(* with those of the flow, and their time derivative.                        *)
(* ========================================================================= *)

let RFA_EXT_DET_OPEN = prove
 (`!V a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open V /\ &0 < e /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> ?W. open W /\
             (!t y. a <= t /\ t < b /\ y IN V ==> pastecart (lift t) y IN W) /\
             smooth_map_on W FF /\
             (!w. w IN W ==> ~(det(matrify(FF w):real^N^N) = &0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  EXISTS_TAC `{w | w IN O /\
                   lift(det(matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                            :real^N^N)) IN (:real^1) DIFF {vec 0}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. lift(matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                :real^N^N$i$j)) =
      (\m:real^(N,N)finite_prod. lift(basis i dot ((matrify m:real^N^N) ** basis j))) o FF`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFB_BASIS_DOT_MATRIX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON;
                 LRG_LINEAR_MATRIFY_DOT];
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "O" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[MATRIFY_VECTORIZE; LIFT_EQ; GSYM LIFT_NUM] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`; `y:real^N`]
             LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; GSYM LIFT_NUM; LIFT_EQ] THEN
    SIMP_TAC[]]);;

(* The Christoffel symbols of the extension: smooth on W, equal to those of  *)
(* the flow on [a,b) x V, with time derivative the components of ldgamma.   *)

let RFA_GAMF_FACTS = prove
 (`!V a b (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) W i j s.
     open V /\ lricci_flow V a b Gc /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y)) /\
     open W /\ smooth_map_on W FF /\
     (!w. w IN W ==> ~(det(matrify(FF w):real^N^N) = &0)) /\
     1 <= s /\ s <= dimindex(:N)
     ==> smooth_map_on W
           (\w. lift((\t y. (christoffel (\z. matrify(FF(pastecart (lift t) z)):real^N^N)
                                         y (basis i) (basis j))$s)
                     (drop(fstcart w)) (sndcart w))) /\
         (!t y. a <= t /\ t < b /\ y IN V
                ==> (christoffel (\z. matrify(FF(pastecart (lift t) z)):real^N^N)
                                 y (basis i) (basis j))$s =
                    (christoffel (Gc t) y (basis i) (basis j))$s) /\
         (!t y. a < t /\ t < b /\ y IN V
                ==> ((\r. (christoffel (\z. matrify(FF(pastecart (lift r) z)):real^N^N)
                                       y (basis i) (basis j))$s)
                     has_real_derivative (ldgamma Gc t y (basis i) (basis j))$s)
                    (atreal t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t < b /\ y IN V
          ==> christoffel (\z. matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                       (pastecart (lift t) z)):real^N^N)
                          y (basis i) (basis j) =
              christoffel ((Gc:real->real^N->real^N^N) t) y (basis i) (basis j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_W_CHRISTOFFEL_SMOOTH THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. (christoffel ((Gc:real->real^N->real^N^N) r) y (basis i) (basis j))$s` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gc:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `basis i:real^N`; `basis j:real^N`]
         LRG_FLOW_GAMMA_VDERIV) THEN
  ASM_REWRITE_TAC[GSYM ldgamma] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. christoffel ((Gc:real->real^N->real^N^N) r) y (basis i) (basis j)`;
                 `ldgamma (Gc:real->real^N->real^N^N) t y (basis i) (basis j)`;
                 `t:real`; `s:num`] LRG_VDERIV_COMPONENT_REAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Component bounds from tensor norms, the jets of the inverse               *)
(* metric, and the jets of the metric from those of the Christoffel symbols. *)
(* ========================================================================= *)

let RFA_JB_TSUBSET = prove
 (`!Js Js' V K m (f:real->real^N->real).
     Js' SUBSET Js /\ rfa_jb Js V K m f ==> rfa_jb Js' V K m f`,
  REWRITE_TAC[rfa_jb; SUBSET] THEN MESON_TAC[]);;

let RFA_COMP_BOUND = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (al:num->num) C L.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\
     al IN index_tuples k (:N) /\ ltnorm2 k G tf y <= C /\ &0 <= L /\
     (!p. 1 <= p /\ p <= dimindex(:N) ==> G y$p$p <= L)
     ==> abs(tf y (\r. basis(al r))) <= C * L pow k + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `\r. basis((al:num->num) r):real^N`] LRG_LTNORM2_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 <= product(1..k) (\m. basis((al:num->num) m) dot ((G:real^N->real^N^N) y **
                                                          basis(al m))) /\
    product(1..k) (\m. basis((al:num->num) m) dot ((G:real^N->real^N^N) y ** basis(al m)))
    <= L pow k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!m. 1 <= m /\ m <= k
          ==> &0 <= basis((al:num->num) m) dot ((G:real^N->real^N^N) y ** basis(al m)) /\
              basis(al m) dot (G y ** basis(al m)) <= L`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `1 <= (al:num->num) m /\ al m <= dimindex(:N)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(al:num->num) IN index_tuples k (:N)` THEN
        REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `basis((al:num->num) m):real^N`] RFA_METRIC_QPOS) THEN
      ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
      MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 k (G:real^N->real^N^N) tf y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 k (G:real^N->real^N^N) tf y *
    product(1..k) (\m. basis((al:num->num) m) dot (G y ** basis(al m))) <=
    C * L pow k`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = (tf:real^N->(num->real^N)->real) y (\r. basis((al:num->num) r))` THEN
  MP_TAC(SPEC `abs x - &1` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `x:real` REAL_POW2_ABS) THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

(* Jets of the inverse metric: d_e g^pq = -(g^pc Gamma(e,c)^q + g^dq Gamma(e,d)^p). *)

let RFA_JB_GINV = prove
 (`!m Js V K (G:real->real^N->real^N^N).
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K 0 (\t z. matrix_inv(G t z)$p$q)) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. (christoffel (G t) z (basis i) (basis j))$s))
     ==> !n p q. n <= m + 1 /\ 1 <= p /\ p <= dimindex(:N) /\
                 1 <= q /\ q <= dimindex(:N)
                 ==> rfa_jb Js V K n (\t z. matrix_inv(G t z)$p$q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g0") (LABEL_TAC "gam"))))) THEN
  INDUCT_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "g0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATCH_MP RFA_JB_SUC (ASSUME `open(V:real^N->bool)`)] THEN CONJ_TAC THENL
   [USE_THEN "g0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:num` THEN STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t z. --(sum(1..dimindex(:N))
               (\c. matrix_inv((G:real->real^N->real^N^N) t z)$p$c *
                    (christoffel (G t) z (basis e) (basis c))$q) +
             sum(1..dimindex(:N))
               (\d. matrix_inv(G t z)$d$q *
                    (christoffel (G t) z (basis e) (basis d))$p))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field V ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfa_pd; partial_derivative] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                   `p:num`; `q:num`] LRG_HAS_DERIVATIVE_GINV_ENTRY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[LIFT_DROP] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_GINV_MDERIV_GINV THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_NEG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `m:num` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "gam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `m:num` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "gam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Index tuples of length 3 and 5, and the time derivative of the           *)
(* Christoffel symbols in components of nabla Ric and nabla Rm.              *)

let rfa_tup3 = new_definition
 `rfa_tup3 (x:num) y z =
    \r. if r = 1 then x else if r = 2 then y else if r = 3 then z else 0`;;

let rfa_tup5 = new_definition
 `rfa_tup5 (p:num) x q y z =
    \r. if r = 1 then p else if r = 2 then x else if r = 3 then q
        else if r = 4 then y else if r = 5 then z else 0`;;

let RFA_TUP3_IN = prove
 (`!x y z. 1 <= x /\ x <= dimindex(:N) /\ 1 <= y /\ y <= dimindex(:N) /\
           1 <= z /\ z <= dimindex(:N)
           ==> rfa_tup3 x y z IN index_tuples 3 (:N)`,
  REWRITE_TAC[rfa_tup3; index_tuples; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_TUP5_IN = prove
 (`!p x q y z. 1 <= p /\ p <= dimindex(:N) /\ 1 <= x /\ x <= dimindex(:N) /\
               1 <= q /\ q <= dimindex(:N) /\ 1 <= y /\ y <= dimindex(:N) /\
               1 <= z /\ z <= dimindex(:N)
               ==> rfa_tup5 p x q y z IN index_tuples 5 (:N)`,
  REWRITE_TAC[rfa_tup5; index_tuples; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_N3_R5 = prove
 (`!U (G:real^N->real^N^N) y x w z.
     metric_field U G /\ y IN U
     ==> lnabla 2 G (lric2 G) y (\r. basis(rfa_tup3 x w z r)) =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q *
           lnabla 4 G (lrm4 G) y (\r. basis(rfa_tup5 p x q w z r))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         RFA_NABLA_RIC_CONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ltcontr; ltperm] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD; ARITH] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o REWRITE_RULE[ltensor_field] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[swap; rfa_tup3; rfa_tup5; ARITH]);;

let RFA_LDGAMMA_N3 = prove
 (`!U a b (G:real->real^N->real^N^N) t y i j s.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
     1 <= s /\ s <= dimindex(:N)
     ==> (ldgamma G t y (basis i) (basis j))$s =
         --(sum(1..dimindex(:N)) (\k. matrix_inv(G t y)$s$k *
              (lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 j k i r)) +
               lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 i k j r)) -
               lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 i j k r)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real->real^N->real^N^N) t y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ldgamma (G:real->real^N->real^N^N) t y (basis i) (basis j) =
    matrix_inv(G t y) ** (G t y ** ldgamma G t y (basis i) (basis j))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `matrix_inv((G:real->real^N->real^N^N) t y) ** G t y = mat 1`
    ASSUME_TAC THENL [ASM_MESON_TAC[MATRIX_INV_LEFT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\l. (G:real->real^N->real^N^N) t y$k$l * ldgamma G t y (basis i) (basis j)$l) =
    (G t y ** ldgamma G t y (basis i) (basis j))$k`
  SUBST1_TAC THENL [ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `basis i:real^N`; `basis j:real^N`; `k:num`]
         LRG_FLOW_DGAMMA) THEN
  ASM_REWRITE_TAC[GSYM ldgamma] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!w w'. (!m. 1 <= m /\ m <= 3 ==> w m = w' m)
           ==> lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y w =
               lnabla 2 (G t) (lric2 (G t)) y w'`
  (LABEL_TAC "ag") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
      (\m. if m = 1 then basis j else if m = 2 then basis k else basis i) =
    lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 j k i r)) /\
    lnabla 2 (G t) (lric2 (G t)) y
      (\m. if m = 1 then basis i else if m = 2 then basis k else basis j) =
    lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 i k j r)) /\
    lnabla 2 (G t) (lric2 (G t)) y
      (\m. if m = 1 then basis i else if m = 2 then basis j else basis k) =
    lnabla 2 (G t) (lric2 (G t)) y (\r. basis(rfa_tup3 i j k r))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "ag" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[rfa_tup3; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The chart C^m bounds in a fixed chart: the Christoffel                    *)
(* symbols by induction on the order (time integration of their evolution), *)
(* then the metric entries by the coordinate jet bound for the metric.       *)
(* ========================================================================= *)

let RFA_GINV_ENTRY_BOUND = prove
 (`!(A:real^N^N) L.
     invertible A /\ &0 <= L /\ (!v. norm v pow 2 <= L * (v dot (A ** v)))
     ==> !p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(matrix_inv A$p$q) <= L`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `w = matrix_inv(A:real^N^N) ** basis q` THEN
  SUBGOAL_THEN `(A:real^N^N) ** w = basis q` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(A:real^N^N) ** matrix_inv A = mat 1` SUBST1_TAC THENL
     [ASM_MESON_TAC[MATRIX_INV_RIGHT]; REWRITE_TAC[MATRIX_VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(A:real^N^N)$p$q = (w:real^N)$p` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA; ASSUME `1 <= q`;
             ASSUME `q <= dimindex(:N)`; ASSUME `1 <= p`; ASSUME `p <= dimindex(:N)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) pow 2 <= L * norm w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * ((w:real^N) dot ((A:real^N^N) ** w))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DOT_BASIS] THEN
    MP_TAC(ISPECL [`w:real^N`; `q:num`] COMPONENT_LE_NORM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) <= L` ASSUME_TAC THENL
   [ASM_CASES_TAC `norm(w:real^N) = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `norm(w:real^N) pow 2 <= L * norm w` THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `p:num`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC);;

(* Jets of the components of nabla Rm from the covariant bounds and          *)
(* the jets of the Christoffel symbols one order lower.                      *)

let RFA_R5_JB = prove
 (`!m Js V K (Gc:real->real^N->real^N^N) Lm.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (Gc t)) /\ &0 <= Lm /\
     (!t y p. t IN Js /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) ==> Gc t y$p$p <= Lm) /\
     (!j. ?C. !t y. t IN Js /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C) /\
     (1 <= m
      ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                  1 <= s /\ s <= dimindex(:N)
                  ==> rfa_jb Js V K (m - 1)
                        (\t z. (christoffel (Gc t) z (basis i) (basis j))$s))
     ==> !al. al IN index_tuples 5 (:N)
              ==> rfa_jb Js V K m
                    (\t z. lnabla 4 (Gc t) (lrm4 (Gc t)) z (\r. basis(al r)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Cr:num->real`) THEN
  MP_TAC(ISPECL [`m:num`; `5`; `Gc:real->real^N->real^N^N`;
                 `\t. lnabla 4 ((Gc:real->real^N->real^N^N) t) (lrm4 (Gc t))`;
                 `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`] RFA_COORD_JET) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`4`; `V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`;
                   `lrm4 ((Gc:real->real^N->real^N^N) t)`] LNABLA_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD; ARITH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `al:num->num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. lnabla_iter 5 j ((Gc:real->real^N->real^N^N) t) (lnabla 4 (Gc t) (lrm4 (Gc t))) =
        lnabla_iter 4 (j + 1) (Gc t) (lrm4 (Gc t))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `5 = 4 + 1`; RFA_LNABLA_ITER_SHIFT]; ALL_TAC] THEN
  REWRITE_TAC[RFA_JB_ZERO] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`4`; `V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`;
                   `lrm4 ((Gc:real->real^N->real^N^N) t)`] LRG_LNABLA_ITER_FIELD) THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `(Cr:num->real) (j + 1) * Lm pow (4 + (j + 1)) + &1` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_COMP_BOUND THEN EXISTS_TAC `V:real^N->bool` THEN
  EXISTS_TAC `(Gc:real->real^N->real^N^N) t` THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`4`; `V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`;
                   `lrm4 ((Gc:real->real^N->real^N^N) t)`] LRG_LNABLA_ITER_FIELD) THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD];
    UNDISCH_TAC `(al:num->num) IN index_tuples (5 + j) (:N)` THEN
    REWRITE_TAC[ARITH_RULE `5 + j = 4 + j + 1`];
    REWRITE_TAC[GSYM lrm_deriv_norm2] THEN ASM_SIMP_TAC[]]);;

(* Uniform bounds of the inverse metric entries from the lower metric bound. *)

let RFA_R1_GINV0 = prove
 (`!Js V K (Gc:real->real^N->real^N^N) Lm.
     (!t. t IN Js ==> metric_field V (Gc t)) /\ K SUBSET V /\ &0 <= Lm /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v)))
     ==> !p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> rfa_jb Js V K 0 (\t z. matrix_inv(Gc t z)$p$q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[RFA_JB_ZERO] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Lm:real` THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `invertible((Gc:real->real^N->real^N^N) t y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`; `y:real^N`]
           LRG_METRIC_INVERTIBLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Gc:real->real^N->real^N^N) t y`; `Lm:real`] RFA_GINV_ENTRY_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Jets of the components of nabla Ric (through nabla Rm and the inverse     *)
(* metric).                                                                  *)

let RFA_R1_N3_JB = prove
 (`!m Js V K (Gc:real->real^N->real^N^N).
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. matrix_inv(Gc t z)$p$q)) /\
     (!al. al IN index_tuples 5 (:N)
           ==> rfa_jb Js V K m
                 (\t z. lnabla 4 (Gc t) (lrm4 (Gc t)) z (\r. basis(al r))))
     ==> !x1 x2 x3. 1 <= x1 /\ x1 <= dimindex(:N) /\ 1 <= x2 /\ x2 <= dimindex(:N) /\
                    1 <= x3 /\ x3 <= dimindex(:N)
                    ==> rfa_jb Js V K m
                          (\t y. lnabla 2 (Gc t) (lric2 (Gc t)) y
                                   (\r. basis(rfa_tup3 x1 x2 x3 r)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gi") (LABEL_TAC "r5"))))) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t y. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
            matrix_inv((Gc:real->real^N->real^N^N) t y)$p$q *
            lnabla 4 (Gc t) (lrm4 (Gc t)) y (\r. basis(rfa_tup5 p x1 q x2 x3 r))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_N3_R5 THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "r5" (MP_TAC o SPEC `rfa_tup5 p x1 q x2 x3`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC RFA_TUP5_IN THEN ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

(* Jets of the components of the time derivative of the Christoffel symbols *)
(* on the open time interval.                                                *)

let RFA_R1_DGAMMA_JB = prove
 (`!m V K a b (Gc:real->real^N->real^N^N).
     open V /\ K SUBSET V /\ lricci_flow V a b Gc /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb {t | a <= t /\ t < b} V K m (\t z. matrix_inv(Gc t z)$p$q)) /\
     (!al. al IN index_tuples 5 (:N)
           ==> rfa_jb {t | a <= t /\ t < b} V K m
                 (\t z. lnabla 4 (Gc t) (lrm4 (Gc t)) z (\r. basis(al r))))
     ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                 1 <= s /\ s <= dimindex(:N)
                 ==> rfa_jb {t | a < t /\ t < b} V K m
                       (\t z. (ldgamma Gc t z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mf")
    (CONJUNCTS_THEN2 (LABEL_TAC "gi") (LABEL_TAC "r5")))))) THEN
  SUBGOAL_THEN `{t | a < t /\ t < b} SUBSET {t | a <= t /\ t < b}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb {t | a < t /\ t < b} V K m
                (\t z. matrix_inv((Gc:real->real^N->real^N^N) t z)$p$q)`
  (LABEL_TAC "gi0") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_TSUBSET THEN
    EXISTS_TAC `{t | a <= t /\ t < b}` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x1 x2 x3. 1 <= x1 /\ x1 <= dimindex(:N) /\ 1 <= x2 /\ x2 <= dimindex(:N) /\
               1 <= x3 /\ x3 <= dimindex(:N)
               ==> rfa_jb {t | a < t /\ t < b} V K m
                     (\t y. lnabla 2 ((Gc:real->real^N->real^N^N) t) (lric2 (Gc t)) y
                              (\r. basis(rfa_tup3 x1 x2 x3 r)))`
  (LABEL_TAC "n3") THENL
   [MATCH_MP_TAC RFA_R1_N3_JB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_TSUBSET THEN
      EXISTS_TAC `{t | a <= t /\ t < b}` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "r5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t y. --(sum(1..dimindex(:N)) (\k. matrix_inv((Gc:real->real^N->real^N^N) t y)$s$k *
             (lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 j k i r)) +
              lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 i k j r)) -
              lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 i j k r)))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
    STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_LDGAMMA_N3 THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_NEG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "gi0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC] THEN
  USE_THEN "n3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* One step of the induction on the order: the Christoffel symbols are       *)
(* uniformly C^m on the half-open time interval if they are C^(m-1).         *)

let RFA_R1_GAMMA_STEP = prove
 (`!m V K a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) Lm.
     open V /\ compact K /\ K SUBSET V /\ a < b /\ &0 < e /\ lricci_flow V a b Gc /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y)) /\
     &0 <= Lm /\
     (!t y p. a <= t /\ t < b /\ y IN K /\ 1 <= p /\ p <= dimindex(:N)
              ==> Gc t y$p$p <= Lm) /\
     (!t y v. a <= t /\ t < b /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. a <= t /\ t < b /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C) /\
     (1 <= m
      ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                  1 <= s /\ s <= dimindex(:N)
                  ==> rfa_jb {t | a <= t /\ t < b} V K (m - 1)
                        (\t z. (christoffel (Gc t) z (basis i) (basis j))$s))
     ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                 1 <= s /\ s <= dimindex(:N)
                 ==> rfa_jb {t | a <= t /\ t < b} V K m
                       (\t z. (christoffel (Gc t) z (basis i) (basis j))$s)`,
  INTRO_TAC "!m V K a b e Gc FF Lm; oV cK KV ab e0 rf mf ffs ffeq L0 diag pos rmb ih" THEN
  SUBGOAL_THEN
   `!t. t IN {t | a <= t /\ t < b} ==> metric_field V ((Gc:real->real^N->real^N^N) t)`
  (LABEL_TAC "mfJ") THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb {t | a <= t /\ t < b} V K 0
                (\t z. matrix_inv((Gc:real->real^N->real^N^N) t z)$p$q)`
  (LABEL_TAC "gi00") THENL
   [MATCH_MP_TAC RFA_R1_GINV0 THEN EXISTS_TAC `Lm:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb {t | a <= t /\ t < b} V K m
                (\t z. matrix_inv((Gc:real->real^N->real^N^N) t z)$p$q)`
  (LABEL_TAC "gi") THENL
   [ASM_CASES_TAC `m = 0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m - 1`; `{t | a <= t /\ t < b}`; `V:real^N->bool`; `K:real^N->bool`;
                   `Gc:real->real^N->real^N^N`] RFA_JB_GINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!al. al IN index_tuples 5 (:N)
         ==> rfa_jb {t | a <= t /\ t < b} V K m
               (\t z. lnabla 4 ((Gc:real->real^N->real^N^N) t) (lrm4 (Gc t)) z
                        (\r. basis(al r)))`
  (LABEL_TAC "r5") THENL
   [MATCH_MP_TAC RFA_R5_JB THEN EXISTS_TAC `Lm:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
            1 <= s /\ s <= dimindex(:N)
            ==> rfa_jb {t | a < t /\ t < b} V K m
                  (\t z. (ldgamma (Gc:real->real^N->real^N^N) t z (basis i) (basis j))$s)`
  (LABEL_TAC "dg") THENL
   [MATCH_MP_TAC RFA_R1_DGAMMA_JB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `e:real`;
                 `Gc:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] RFA_EXT_DET_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `s:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gc:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `W:real^(1,N)finite_sum->bool`; `i:num`; `j:num`; `s:num`]
         RFA_GAMF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "geq") ASSUME_TAC)) THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t y. (christoffel (\z. matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                        (pastecart (lift t) z)):real^N^N)
                                 y (basis i) (basis j))$s` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "geq" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_TIME THEN
  MAP_EVERY EXISTS_TAC
   [`W:real^(1,N)finite_sum->bool`;
    `\t z. (ldgamma (Gc:real->real^N->real^N^N) t z (basis i) (basis j))$s`] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "dg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_R1_GAMMA = prove
 (`!V K a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) Lm.
     open V /\ compact K /\ K SUBSET V /\ a < b /\ &0 < e /\ lricci_flow V a b Gc /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y)) /\
     &0 <= Lm /\
     (!t y p. a <= t /\ t < b /\ y IN K /\ 1 <= p /\ p <= dimindex(:N)
              ==> Gc t y$p$p <= Lm) /\
     (!t y v. a <= t /\ t < b /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. a <= t /\ t < b /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C)
     ==> !m i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                   1 <= s /\ s <= dimindex(:N)
                   ==> rfa_jb {t | a <= t /\ t < b} V K m
                         (\t z. (christoffel (Gc t) z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  MATCH_MP_TAC RFA_R1_GAMMA_STEP THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                        `Lm:real`] THEN
  ASM_REWRITE_TAC[ARITH; SUC_SUB1]);;

let RFA_TUP2_IN = prove
 (`!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
         ==> rfa_tup3 p q 0 IN index_tuples 2 (:N)`,
  REWRITE_TAC[rfa_tup3; index_tuples; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

(* The metric entries are uniformly C^m once the Christoffel symbols are     *)
(* uniformly C^(m-1) (the metric is parallel).                               *)

let RFA_R1_METRIC_JB = prove
 (`!m Js V K (Gc:real->real^N->real^N^N) Lm.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!t y p q. t IN Js /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                1 <= q /\ q <= dimindex(:N) ==> abs(Gc t y$p$q) <= Lm) /\
     (1 <= m
      ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                  1 <= s /\ s <= dimindex(:N)
                  ==> rfa_jb Js V K (m - 1)
                        (\t z. (christoffel (Gc t) z (basis i) (basis j))$s))
     ==> !p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> rfa_jb Js V K m (\t z. Gc t z$p$q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "bd") ASSUME_TAC)))) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `2`; `Gc:real->real^N->real^N^N`;
                 `\t. lmetric2 ((Gc:real->real^N->real^N^N) t)`;
                 `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`] RFA_COORD_JET) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC LRG_LMETRIC2_FIELD THEN
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num`; `al:num->num`] THEN STRIP_TAC THEN
    REWRITE_TAC[RFA_JB_ZERO] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`2`; `V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`;
                     `lmetric2 ((Gc:real->real^N->real^N^N) t)`] LRG_LNABLA_ITER_FIELD) THEN
      ASM_SIMP_TAC[LRG_LMETRIC2_FIELD];
      ALL_TAC] THEN
    ASM_CASES_TAC `l = 0` THENL
     [EXISTS_TAC `Lm:real` THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[lnabla_iter; lmetric2] THEN
      UNDISCH_TAC `(al:num->num) IN index_tuples (2 + l) (:N)` THEN
      ASM_REWRITE_TAC[index_tuples; IN_ELIM_THM; ADD_CLAUSES] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX] THEN USE_THEN "bd" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `&0` THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?l'. l = SUC l'` (X_CHOOSE_THEN `l':num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `l - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`]
           LRG_LNABLA_ITER_METRIC) THEN
    ANTS_TAC THENL [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> SIMP_TAC[th; ASSUME `(y:real^N) IN V`]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rfa_tup3 p q 0`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC RFA_TUP2_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t z. lmetric2 ((Gc:real->real^N->real^N^N) t) z (\r. basis(rfa_tup3 p q 0 r))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[lmetric2; rfa_tup3; ARITH] THEN
  MATCH_MP_TAC RFB_BASIS_DOT_MATRIX THEN ASM_REWRITE_TAC[]);;

(* The chart C^m bounds in a fixed chart (all orders).                       *)

let RFA_R1_LOCAL = prove
 (`!V K a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) Lm.
     open V /\ compact K /\ K SUBSET V /\ a < b /\ &0 < e /\ lricci_flow V a b Gc /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y)) /\
     &0 <= Lm /\
     (!t y p q. a <= t /\ t < b /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                1 <= q /\ q <= dimindex(:N) ==> abs(Gc t y$p$q) <= Lm) /\
     (!t y v. a <= t /\ t < b /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. a <= t /\ t < b /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C)
     ==> !m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                 ==> rfa_jb {t | a <= t /\ t < b} V K m (\t z. Gc t z$p$q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `K:real^N->bool`; `a:real`; `b:real`; `e:real`;
                 `Gc:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`; `Lm:real`]
         RFA_R1_GAMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= l ==> x <= l`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  X_GEN_TAC `m:num` THEN MATCH_MP_TAC RFA_R1_METRIC_JB THEN EXISTS_TAC `Lm:real` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC]);;

(* ========================================================================= *)
(* From the chart jet bounds to the norm of the iterated                     *)
(* partials of the vectorized metric; entry and lower bounds from the       *)
(* metric equivalence; the chart form of the metric equivalence.            *)
(* ========================================================================= *)

(* Iterated partials commute with taking a component.  This is the special *)
(* case L = lift o component of PDE_ITERATED_PARTIAL_LINEAR_COMPOSE of      *)
(* pc_rf_glue.ml, which is not in the load closure of this unit (a heavy    *)
(* unit of the PDE layer).                                                  *)

let RFA_ITERATED_PARTIAL_LIFT_COMPONENT = prove
 (`!l s (f:real^M->real^N) k x.
     open s /\ smooth_map_on s f /\ x IN s
     ==> iterated_partial l (\z. lift(f z$k)) x = lift(iterated_partial l f x$k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h (\z. lift(iterated_partial t (f:real^M->real^N) z$k)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_COMPONENT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

(* Uniform jet bounds of all entries give a uniform bound of the norms of  *)
(* the iterated partials of the vectorized matrix field.                    *)

let RFA_JB_VEC_NORM = prove
 (`!Js V K m (Gc:real->real^N->real^N^N).
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. Gc t z$p$q))
     ==> ?C. !t l y. t IN Js /\ l IN pde_index_lists m (:N) /\ y IN K
                     ==> norm(iterated_partial l
                                ((vectorize:real^N^N->real^(N,N)finite_prod) o Gc t) y) <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (LABEL_TAC "jb")))) THEN
  SUBGOAL_THEN
   `!p q. ?C. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> !t l y. t IN Js /\ l IN pde_index_lists m (:N) /\ y IN K
                          ==> abs(drop(iterated_partial l
                                   (\z. lift((Gc:real->real^N->real^N^N) t z$p$q)) y)) <= C`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `rfa_jb Js V K m (\t z. (Gc:real->real^N->real^N^N) t z$p$q)` MP_TAC THENL
     [USE_THEN "jb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfa_jb] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:num->num->real` (LABEL_TAC "cp")) THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. (Cp:num->num->real) (1 + (k - 1) DIV dimindex(:N))
                                         (1 + (k - 1) MOD dimindex(:N)))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                 (Gc:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field V ((Gc:real->real^N->real^N^N) t)` MP_TAC THENL
     [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[metric_field]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. abs((iterated_partial l
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Gc:real->real^N->real^N^N) t) y)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= 1 + (k - 1) DIV dimindex(:N) /\ 1 + (k - 1) DIV dimindex(:N) <= dimindex(:N) /\
    1 <= 1 + (k - 1) MOD dimindex(:N) /\ 1 + (k - 1) MOD dimindex(:N) <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= 1 + a`] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a < b ==> 1 + a <= b`) THEN
    SIMP_TAC[DIVISION; LE_1; DIMINDEX_GE_1; RDIV_LT_EQ] THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (Gc:real->real^N->real^N^N) t`;
                 `k:num`; `y:real^N`] RFA_ITERATED_PARTIAL_LIFT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(\z. lift((((vectorize:real^N^N->real^(N,N)finite_prod) o
                (Gc:real->real^N->real^N^N) t) z)$k)) =
    (\z. lift(Gc t z$(1 + (k - 1) DIV dimindex(:N))$(1 + (k - 1) MOD dimindex(:N))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTORIZE_COMPONENT THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cp" (MP_TAC o SPECL [`1 + (k - 1) DIV dimindex(:N)`;
                                 `1 + (k - 1) MOD dimindex(:N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Entries of a positive semidefinite symmetric matrix from an upper bound  *)
(* of its quadratic form (polarization).                                     *)

let RFA_QFORM_ENTRY_BOUND = prove
 (`!(A:real^N^N) C p q.
     transp A = A /\ (!v. &0 <= v dot (A ** v)) /\
     (!v. v dot (A ** v) <= C * norm v pow 2) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> abs(A$p$q) <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos")
    (CONJUNCTS_THEN2 (LABEL_TAC "up") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(A:real^N^N)$q$p = A$p$q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real^N^N`; `p:num`; `q:num`] TRANSP_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(basis p + basis q:real^N) dot ((A:real^N^N) ** (basis p + basis q)) =
      A$p$p + &2 * A$p$q + A$q$q /\
    (basis p - basis q:real^N) dot ((A:real^N^N) ** (basis p - basis q)) =
      A$p$p - &2 * A$p$q + A$q$q`
  (LABEL_TAC "eqs") THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                 DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; RFB_BASIS_DOT_MATRIX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis p + basis q:real^N) pow 2 <= &4 /\
                norm(basis p - basis q:real^N) pow 2 <= &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(basis p + basis q:real^N) <= &2 /\
                  norm(basis p - basis q:real^N) <= &2`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(x:real^N) = &1 /\ norm(y:real^N) = &1
                               ==> norm(x + y) <= &2 /\ norm(x - y) <= &2`) THEN
      ASM_SIMP_TAC[NORM_BASIS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&4 = &2 pow 2`] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [USE_THEN "up" (MP_TAC o SPEC `basis p:real^N`) THEN
    USE_THEN "pos" (MP_TAC o SPEC `basis p:real^N`) THEN
    SIMP_TAC[NORM_BASIS; REAL_POW_ONE; ASSUME `1 <= p`; ASSUME `p <= dimindex(:N)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C * norm(basis p + basis q:real^N) pow 2 <= C * &4 /\
                C * norm(basis p - basis q:real^N) pow 2 <= C * &4`
  MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "up" (MP_TAC o SPEC `basis p + basis q:real^N`) THEN
  USE_THEN "up" (MP_TAC o SPEC `basis p - basis q:real^N`) THEN
  USE_THEN "pos" (MP_TAC o SPEC `basis p + basis q:real^N`) THEN
  USE_THEN "pos" (MP_TAC o SPEC `basis p - basis q:real^N`) THEN
  USE_THEN "eqs" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(* Two-sided exponential comparison over a shorter interval.                *)

let RFA_EXP_EQUIV_STEP = prove
 (`!x X Qa Qt. &0 <= x /\ x <= X /\ &0 <= Qa /\ &0 <= Qt /\
               exp(--x) * Qa <= Qt /\ Qt <= exp x * Qa
               ==> Qa <= exp X * Qt /\ Qt <= exp X * Qa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp x <= exp X` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_MONO_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp x * Qt` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `Qa = exp x * (exp(--x) * Qa)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                    REAL_MUL_LID];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp x * Qa` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* Entry bounds and the lower bound of Gt from the bounds of Ga and the    *)
(* two-sided comparison of the quadratic forms.                             *)

let RFA_EQUIV_BOUNDS = prove
 (`!(Ga:real^N^N) (Gt:real^N^N) c0 C0 E.
     &0 < c0 /\ transp Gt = Gt /\ (!w. &0 <= w dot (Gt ** w)) /\
     (!w. c0 * norm w pow 2 <= w dot (Ga ** w)) /\
     (!w. w dot (Ga ** w) <= C0 * norm w pow 2) /\
     (!w. w dot (Ga ** w) <= E * (w dot (Gt ** w))) /\
     (!w. w dot (Gt ** w) <= E * (w dot (Ga ** w))) /\ &0 <= E
     ==> (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> abs(Gt$p$q) <= E * C0) /\
         (!w. norm w pow 2 <= (E / c0) * (w dot (Gt ** w)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "lo")
    (CONJUNCTS_THEN2 (LABEL_TAC "hi") (CONJUNCTS_THEN2 (LABEL_TAC "e1")
    (CONJUNCTS_THEN2 (LABEL_TAC "e2") ASSUME_TAC))))))) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_ENTRY_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `E * (w dot ((Ga:real^N^N) ** w))` THEN
    USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN
  USE_THEN "lo" (MP_TAC o SPEC `w:real^N`) THEN
  USE_THEN "e1" (MP_TAC o SPEC `w:real^N`) THEN
  SUBGOAL_THEN `E / c0 * (w dot ((Gt:real^N^N) ** w)) = (E * (w dot (Gt ** w))) / c0`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < c0`] THEN REAL_ARITH_TAC);;

(* The quadratic form of a chart representative is the quadratic form of   *)
(* the metric at the point applied to the transported vector.               *)

let RFA_METRIC_LOCAL_QFORM = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y w.
     w dot (metric_local atlas c g y ** w) =
     (matrix(chart_jac c (chart_at atlas (chart_inv c y)) (chart_inv c y)) ** w) dot
     (g(chart_inv c y) **
      (matrix(chart_jac c (chart_at atlas (chart_inv c y)) (chart_inv c y)) ** w))`,
  REWRITE_TAC[metric_local; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let RFA_CHART_INV_TOPSPACE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) c y.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> chart_inv c y IN FST c /\ SND c (chart_inv c y) = y /\
         chart_inv c y IN topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
         CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
         SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The squared norm of Rm is bounded by a dimensional multiple of the       *)
(* square of a bound of the sectional curvatures.                           *)

let RFA_R1_RMD0 = prove
 (`?C0. &0 <= C0 /\
        !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x B.
          smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
          x IN topspace top /\ mfd_rm_norm atlas g x <= B
          ==> rfa_rmd2 0 atlas g x <= C0 * B pow 2`,
  MP_TAC(INST_TYPE [`:N`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "sec" MATCH_MP_TAC THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                    (FST(chart_at atlas x))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[riemannian_metric];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas (g:A->real^N^N) x` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `v:real^N`]
           RFA_MFD_SECTIONAL_LE_NORM) THEN
    ASM_REWRITE_TAC[mfd_sectional]]);;

(* The Ricci curvature is bounded by the norm of Rm.                         *)

let RFA_R1_RIC_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x D v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 <= D /\ rfa_rmd2 0 atlas g x <= D
     ==> abs(mfd_ricci atlas g x v v) <=
         (&(dimindex(:N)) * sqrt D) * (v dot (g x ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N)) /\
    SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas (chart_at atlas x) (g:A->real^N^N) (SND(chart_at atlas x) x) = g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))
              (SND(chart_at atlas x) x) u) <=
        sqrt D * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num->real^N` THEN
    MP_TAC(ISPECL [`4`; `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                               (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                   `lrm4(metric_local atlas (chart_at atlas x) (g:A->real^N^N))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`;
                   `M:real^N^N`; `u:num->real^N`; `D:real`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_SIMP_TAC[PRODUCT_4; LRM4_TENSOR_FIELD] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `rfa_rmd2 0 atlas (g:A->real^N^N) x <= D` THEN
    REWRITE_TAC[rfa_rmd2; lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`;
                 `M:real^N^N`; `sqrt D`] LRG_RICCI0_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `v:real^N`]) THEN
  REWRITE_TAC[mfd_ricci] THEN
  SUBGOAL_THEN `(v:real^N) dot ((g:A->real^N^N) x ** v) = norm((M:real^N^N) ** v) * norm(M ** v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2; GSYM DOT_SQUARE_NORM] THEN
    SUBGOAL_THEN `(g:A->real^N^N) x = transp(M:real^N^N) ** M` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    REAL_ARITH_TAC]);;

(* The metric equivalence in a fixed chart.                                  *)

let RFA_R1_CHART_EQUIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) K c.
     ricci_flow_from (top,atlas) a b g /\
     (!t x v. a <= t /\ t < b /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v))) /\
     c IN atlas
     ==> !t y w. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                 ==> exp(--(&2 * K * (t - a))) *
                     (w dot (metric_local atlas c (g a) y ** w))
                     <= w dot (metric_local atlas c (g t) y ** w) /\
                     w dot (metric_local atlas c (g t) y ** w)
                     <= exp(&2 * K * (t - a)) *
                        (w dot (metric_local atlas c (g a) y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `w:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[RFA_METRIC_LOCAL_QFORM] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] RFA_CHART_INV_TOPSPACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `K:real`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* In a fixed chart and on a compact subset: uniform entry bounds and a     *)
(* uniform lower bound of the metrics g(t), a <= t < b, from the metric      *)
(* equivalence (bounded Ricci curvature).                                    *)

let RFA_R1_CHART_BDS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    Kr c K.
     ricci_flow_from (top,atlas) a b g /\ &0 <= Kr /\
     (!t x v. a <= t /\ t < b /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= Kr * (v dot (g t x ** v))) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c)
     ==> ?L. &0 <= L /\
             !t y. a <= t /\ t < b /\ y IN K
                   ==> (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                              ==> abs(metric_local atlas c (g t) y$p$q) <= L) /\
                       (!w. norm w pow 2 <=
                            L * (w dot (metric_local atlas c (g t) y ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) /\
    riemannian_metric atlas ((g:real->A->real^N^N) a)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `(g:real->A->real^N^N) a`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `K:real^N->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gab"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `Kr:real`; `c:(A->bool)#(A->real^N)`]
         RFA_R1_CHART_EQUIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "eqv")] THEN
  EXISTS_TAC `max (exp(&2 * Kr * (b - a)) * C1) (exp(&2 * Kr * (b - a)) / c0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < y ==> &0 <= max x y`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    UNDISCH_TAC `(y:real^N) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c ((g:real->A->real^N^N) t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[riemannian_metric] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp(metric_local atlas c ((g:real->A->real^N^N) t) y) =
    metric_local atlas c (g t) y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                              (metric_local atlas c ((g:real->A->real^N^N) t))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. &0 <= w dot (metric_local atlas c ((g:real->A->real^N^N) t) y ** w)`
  (LABEL_TAC "nn") THENL
   [X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "gab" (LABEL_TAC "gay" o GEN `v:real^N` o
    C MP (ASSUME `(y:real^N) IN K`) o SPECL [`y:real^N`; `v:real^N`]) THEN
  SUBGOAL_THEN
   `!w. w dot (metric_local atlas c ((g:real->A->real^N^N) a) y ** w) <=
        exp(&2 * Kr * (b - a)) * (w dot (metric_local atlas c (g t) y ** w)) /\
        w dot (metric_local atlas c (g t) y ** w) <=
        exp(&2 * Kr * (b - a)) * (w dot (metric_local atlas c (g a) y ** w))`
  (LABEL_TAC "ee") THENL
   [X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC RFA_EXP_EQUIV_STEP THEN
    EXISTS_TAC `&2 * Kr * (t - a)` THEN
    USE_THEN "eqv" (MP_TAC o SPECL [`t:real`; `y:real^N`; `w:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * norm(w:real^N) pow 2` THEN
      USE_THEN "gay" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`metric_local atlas c ((g:real->A->real^N^N) a) y`;
                 `metric_local atlas c ((g:real->A->real^N^N) t) y`;
                 `c0:real`; `C1:real`; `exp(&2 * Kr * (b - a))`] RFA_EQUIV_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "en") (LABEL_TAC "lw")) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * Kr * (b - a)) * C1` THEN CONJ_TAC THENL
     [USE_THEN "en" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * Kr * (b - a)) / c0 *
                (w dot (metric_local atlas c ((g:real->A->real^N^N) t) y ** w))` THEN
    CONJ_TAC THENL [USE_THEN "lw" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN USE_THEN "nn" (fun th -> REWRITE_TAC[th]) THEN
    REAL_ARITH_TAC]);;

(* The global derivative bounds in a fixed chart.                            *)

let RFA_R1_CHART_RMD = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) c K.
     ricci_flow_from (top,atlas) a b g /\ c IN atlas /\ K SUBSET IMAGE (SND c) (FST c) /\
     (!j. ?C. !t x. a <= t /\ t < b /\ x IN topspace top
                    ==> rfa_rmd2 j atlas (g t) x <= C)
     ==> !j. ?C. !t y. a <= t /\ t < b /\ y IN K
                       ==> lrm_deriv_norm2 j (metric_local atlas c (g t)) y <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b10")))) THEN
  X_GEN_TAC `j:num` THEN
  USE_THEN "b10" (X_CHOOSE_THEN `C:real` (LABEL_TAC "bj") o SPEC `j:num`) THEN
  EXISTS_TAC `C:real` THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    UNDISCH_TAC `(y:real^N) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] RFA_CHART_INV_TOPSPACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`j:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] RFA_RMD2_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "bj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The chart C^m bounds on one piece of the cover, and R1                    *)
(* (PDE_REQ_DERIV_BOUNDS_STATEMENT) by taking the maximum over the pieces.   *)
(* ========================================================================= *)

let RFA_R1_CHART_FROM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    Kr c K.
     ricci_flow_from (top,atlas) a b g /\ &0 <= Kr /\
     (!t x v. a <= t /\ t < b /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= Kr * (v dot (g t x ** v))) /\
     (!j. ?C. !t x. a <= t /\ t < b /\ x IN topspace top
                    ==> rfa_rmd2 j atlas (g t) x <= C) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c)
     ==> !m. ?Bc. !B'. Bc <= B'
                       ==> !t. a <= t /\ t < b
                               ==> (!l y. l IN pde_index_lists m (:N) /\ y IN K
                                          ==> norm(iterated_partial l
                                                ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                                 metric_local atlas c (g t)) y) <= B') /\
                                   (!y v. y IN K
                                          ==> norm v pow 2 <=
                                              B' * (v dot (metric_local atlas c (g t) y ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) /\
    ricci_flow_on (top,atlas) a b (g:real->A->real^N^N) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                         (metric_local atlas c ((g:real->A->real^N^N) t))`
  (LABEL_TAC "mf") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[riemannian_metric] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `Kr:real`; `c:(A->bool)#(A->real^N)`;
                 `K:real^N->bool`] RFA_R1_CHART_BDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bds"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `K:real^N->bool`] RFA_R1_CHART_RMD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rmb")] THEN
  SUBGOAL_THEN
   `?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
      &0 < e /\
      smooth_map_on (interval(lift(a - e),lift b) PCROSS
                     IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) FF /\
      !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
            ==> FF(pastecart (lift t) y) =
                vectorize(metric_local atlas c ((g:real->A->real^N^N) t) y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                 (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `K SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `K:real^N->bool`;
                 `a:real`; `b:real`; `e:real`;
                 `\t. metric_local atlas c ((g:real->A->real^N^N) t)`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`; `L:real`]
         RFA_R1_LOCAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "bds" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "bds" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_THEN(LABEL_TAC "jb")] THEN
  MP_TAC(ISPECL [`{t | a <= t /\ t < b}`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `K:real^N->bool`; `m:num`;
                 `\t. metric_local atlas c ((g:real->A->real^N^N) t)`] RFA_JB_VEC_NORM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "jb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Cv:real` (LABEL_TAC "cv"))] THEN
  EXISTS_TAC `max Cv L` THEN X_GEN_TAC `B':real` THEN DISCH_TAC THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cv:real` THEN CONJ_TAC THENL
     [USE_THEN "cv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    UNDISCH_TAC `(y:real^N) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L * (v dot (metric_local atlas c ((g:real->A->real^N^N) t) y ** v))` THEN
  CONJ_TAC THENL
   [USE_THEN "bds" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LRG_METRIC_NONNEG THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_SIMP_TAC[]);;

(* R1: bounded curvature on a finite interval gives chart C^m bounds of     *)
(* every order, uniformly in time.                                           *)

let RFA_R1 = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_DERIV_BOUNDS_STATEMENT u n`,
  REWRITE_TAC[PDE_REQ_DERIV_BOUNDS_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) /\
    (!t. a <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0p")) RFA_R1_RMD0 THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> rfa_rmd2 0 atlas ((g:real->A->real^N^N) t) x <= C0 * B pow 2`
  (LABEL_TAC "r0") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "c0p" MATCH_MP_TAC THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * B pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `C0 * B pow 2`] RFA_SHI_GLOBAL_INITIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "b10")] THEN
  SUBGOAL_THEN
   `!t x v. a <= t /\ t < b /\ x IN topspace top
            ==> abs(mfd_ricci atlas ((g:real->A->real^N^N) t) x v v) <=
                (&(dimindex(:N)) * sqrt(C0 * B pow 2)) * (v dot (g t x ** v))`
  (LABEL_TAC "ric") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_R1_RIC_BOUND THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) * sqrt(C0 * B pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?Bc. i < n0
             ==> !B'. Bc <= B'
                      ==> !t. a <= t /\ t < b
                              ==> (!l y. l IN pde_index_lists m (:N) /\ y IN ks i
                                         ==> norm(iterated_partial l
                                               ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                                metric_local atlas
                                                  ((cs:num->(A->bool)#(A->real^N)) i)
                                                  ((g:real->A->real^N^N) t)) y) <= B') /\
                                  (!y v. y IN ks i
                                         ==> norm v pow 2 <=
                                             B' * (v dot (metric_local atlas (cs i) (g t) y ** v)))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0
                   (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool)` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`;
                   `&(dimindex(:N)) * sqrt(C0 * B pow 2)`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `(ks:num->real^N->bool) i`]
           RFA_R1_CHART_FROM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o SPEC `m:num`)];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `bi:num->real` (LABEL_TAC "bi")) THEN
  MP_TAC(ISPECL [`bi:num->real`; `{i:num | i < n0}`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "B1")) THEN
  EXISTS_TAC `B1:real` THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[pde_cbound] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "bi" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `B1:real`) THEN
  ANTS_TAC THENL [USE_THEN "B1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

