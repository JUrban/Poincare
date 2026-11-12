(* ========================================================================= *)
(* Unit pc_rfa_hcalc: the heat-defect calculus along a chart Ricci flow.     *)
(* For a time family T of (0,k)-tensor fields, rfa_heat says                 *)
(* d/dt T = Lap T - Rc.T + H, where Rc.T is the action of the Ricci          *)
(* endomorphism on the slots (CLN's D_t, the Uhlenbeck trick in              *)
(* coordinates), so H is the heat defect (D_t - Lap) T.  Rules: sums, slot   *)
(* permutations, tensor products, contractions, covariant derivatives (the   *)
(* commutator 2 Rm.nabla T), time factors; base cases the metric, Ric and    *)
(* Rm.                                                                       *)
(* ========================================================================= *)

needs "src/pc_rfa_rmderiv.ml";;
needs "src/pc_rfa_raylap.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Definitions and the elementary rules.                                     *)
(* ========================================================================= *)

(* The action of the Ricci endomorphism on the slots of a (0,k)-tensor,     *)
(* sum over i of T(u_1,..,Rc(u_i),..,u_k), written out with the metric      *)
(* inverse: Rc(v) has components sum_q g^pq Ric(v,e_q).                      *)

let rfa_rcact = new_definition
 `rfa_rcact k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u =
    sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
      matrix_inv(G y)$p$q * lricci G y (u i) (basis q) *
      tf y (\m. if m = i then basis p else u m))))`;;

(* The heat equation with defect H: d/dt T = Lap T - Rc.T + H on (a,b) x U,  *)
(* for jointly smooth tensor families T and spatially smooth H.             *)

let rfa_heat = new_definition
 `rfa_heat k (U:real^N->bool) a b (G:real->real^N->real^N^N)
           (Tf:real->real^N->(num->real^N)->real)
           (Hf:real->real^N->(num->real^N)->real) <=>
    (!t. a < t /\ t < b
         ==> ltensor_field k U (Tf t) /\ ltensor_field k U (Hf t) /\
             (!u. smooth_map_on U (\y. lift(Hf t y u)))) /\
    (!u. smooth_map_on (interval(lift a,lift b) PCROSS U)
           (\z. lift(Tf (drop(fstcart z)) (sndcart z) u))) /\
    (!t y u. a < t /\ t < b /\ y IN U
             ==> ((\s. Tf s y u) has_real_derivative
                  ltlap k (G t) (Tf t) y u - rfa_rcact k (G t) (Tf t) y u + Hf t y u)
                 (atreal t))`;;

(* The cross term of the Laplacian of a tensor product: the metric trace of *)
(* the two derivative slots of nabla A (x) nabla B.                          *)

let rfa_xgrad = new_definition
 `rfa_xgrad p q (G:real^N->real^N^N) (A:real^N->(num->real^N)->real)
            (B:real^N->(num->real^N)->real) y u =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv(G y)$a$b *
      lnabla p G A y (\m. if m = p + 1 then basis a else u m) *
      lnabla q G B y (\m. if m = q + 1 then basis b else u(m + p))))`;;

(* The commutator term of the heat operator with nabla, in the order in     *)
(* which it arises: with c = u(k+1),                                          *)
(*   sum_ab g^ab sum_i sum_pq g^pq ( R(e_b,c,e_p,u_i) nabla T(..e_q..; e_a)  *)
(*                                  + R(e_a,c,e_p,u_i) nabla T(..e_q..; e_b)) *)
(* (R = lrm4; the two halves agree, total 2 R_{p a b_i q} nabla_p T_{..q..}  *)
(* in CLN indices).                                                           *)

let rfa_rmcomm = new_definition
 `rfa_rmcomm k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G y)$a$b *
      sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
        matrix_inv(G y)$p$q *
        (lrm4 G y (\m. if m = 1 then basis b else if m = 2 then u(k + 1)
                       else if m = 3 then basis p else u i) *
         lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis a
                              else u m) +
         lrm4 G y (\m. if m = 1 then basis a else if m = 2 then u(k + 1)
                       else if m = 3 then basis p else u i) *
         lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis b
                              else u m)))))))`;;


(* ========================================================================= *)
(* The Ricci action: linearity, tensor fields, smoothness.                   *)
(* ========================================================================= *)

(* Linear arithmetic over num using only the arithmetic assumptions (ASM_ARITH_TAC *)
(* can fail when boolean atoms such as ltensor_field p U A mention the same     *)
(* num variables).                                                              *)

let rec rfa_is_numrel tm =
  if is_neg tm then rfa_is_numrel (dest_neg tm)
  else if is_conj tm || is_disj tm || is_imp tm then
    rfa_is_numrel (lhand tm) && rfa_is_numrel (rand tm)
  else if is_eq tm then type_of (lhand tm) = `:num`
  else (is_binary "<=" tm || is_binary "<" tm) && type_of (lhand tm) = `:num`;;

let RFA_ARITH_TAC =
  POP_ASSUM_LIST(fun ths ->
    MAP_EVERY (fun th -> if rfa_is_numrel (concl th) then MP_TAC th else ALL_TAC) ths) THEN
  ARITH_TAC;;

let RFA_SMOOTH_LIFT_LINCOMB = prove
 (`!s (f:real^M->real) g a b.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(a * f x + b * g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]);;

let RFA_SMOOTH_LIFT_MUL3 = prove
 (`!s (f:real^M->real) g h.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x)) /\
     smooth_map_on s (\x. lift(h x))
     ==> smooth_map_on s (\x. lift(f x * g x * h x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[]);;

let RFA_RCACT_LINCOMB = prove
 (`!k (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 a b y u.
     rfa_rcact k G (\y u. a * tf1 y u + b * tf2 y u) y u =
     a * rfa_rcact k G tf1 y u + b * rfa_rcact k G tf2 y u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_rcact; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let RFA_RCACT_LOCAL = prove
 (`!k (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 y u.
     (!w. tf1 y w = tf2 y w) ==> rfa_rcact k G tf1 y u = rfa_rcact k G tf2 y u`,
  SIMP_TAC[rfa_rcact]);;

let RFA_RCACT_FIELD = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field k U (rfa_rcact k G tf) /\
         (!u. smooth_map_on U (\y. lift(rfa_rcact k G tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfa_rcact] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_SMOOTH_LIFT_MUL3 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
    ASM_REWRITE_TAC[lric2] THEN
    DISCH_THEN(MP_TAC o SPEC `\m. if m = 1 then (u:num->real^N) i else basis q` o
               CONJUNCT2) THEN
    REWRITE_TAC[ARITH]] THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m)
            ==> (tf:real^N->(num->real^N)->real) y u = tf y u') /\
    (!i u. 1 <= i /\ i <= k
           ==> linear (\v. lift(tf y (\j. if j = i then v else u j))))`
  MP_TAC THENL [ASM_MESON_TAC[ltensor_field]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (LABEL_TAC "li")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN
    DISCH_THEN(LABEL_TAC "uu") THEN REWRITE_TAC[rfa_rcact] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(u:num->real^N) i = u' i` SUBST1_TAC THENL
     [USE_THEN "uu" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN USE_THEN "ag" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "uu" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rcact; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [SUBGOAL_THEN
     `!v:real^N. (tf:real^N->(num->real^N)->real) y
        (\m. if m = i then basis p else if m = j then v else u m) =
      tf y (\m. if m = i then basis p else u m)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m:num = i` THEN REWRITE_TAC[ASSUME `i:num = j`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(m:num = j)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~(m:num = i)` THEN REWRITE_TAC[ASSUME `i:num = j`];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `i:num = j`] THEN
    REWRITE_TAC[REAL_ARITH `a * b * c = (a * c) * b:real`] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_LRICCI_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(i:num = j)` THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `~(i:num = j)`] THEN REWRITE_TAC[LIFT_CMUL] THEN
  REPEAT(MATCH_MP_TAC LINEAR_COMPOSE_CMUL) THEN
  USE_THEN "li" (MP_TAC o SPECL [`j:num`; `\m. if m = i then basis p else (u:num->real^N) m`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ASM_CASES_TAC `m:num = j` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `m:num = i` THEN UNDISCH_TAC `m:num = j` THEN
  UNDISCH_TAC `~(i:num = j)` THEN MESON_TAC[]);;


(* ========================================================================= *)
(* Elementary rules of the heat-defect calculus: congruence,                 *)
(* linear combinations, slot permutations, time factors, the metric.        *)
(* ========================================================================= *)

let RFA_TENSOR_FIELD_EQ = prove
 (`!k U (f:real^N->(num->real^N)->real) g.
     (!y u. y IN U ==> g y u = f y u) /\ ltensor_field k U f
     ==> ltensor_field k U g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltensor_field] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let RFA_LTLAP_LOCAL = prove
 (`!k (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 s y u.
     open s /\ y IN s /\ (!z w. z IN s ==> tf1 z w = tf2 z w)
     ==> ltlap k G tf1 y u = ltlap k G tf2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltlap] THEN
  MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
                 `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ASM_SIMP_TAC[]);;

let RFA_PCROSS_INTERVAL_TIME = prove
 (`!a b (U:real^N->bool) z.
     z IN interval(lift a,lift b) PCROSS U
     ==> a < drop(fstcart z) /\ drop(fstcart z) < b /\ sndcart z IN U`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `z = pastecart (fstcart z) (sndcart(z:real^(1,N)finite_sum))`
    SUBST1_TAC THENL [REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              IN_INTERVAL_1; LIFT_DROP] THEN
  SIMP_TAC[]);;

let RFA_HEAT_SLICE = prove
 (`!k U a b (G:real->real^N->real^N^N) Tf Hf t.
     rfa_heat k U a b G Tf Hf /\ open U /\ a < t /\ t < b
     ==> !u. smooth_map_on U (\y. lift(Tf t y u))`,
  REWRITE_TAC[rfa_heat] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:num->real^N`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z. lift((Tf:real->real^N->(num->real^N)->real)
                           (drop(fstcart z)) (sndcart z) u)`;
                 `a:real`; `b:real`; `U:real^N->bool`; `t:real`]
         RFA_SMOOTH_MAP_ON_SLICE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let RFA_HEAT_CONG = prove
 (`!k U a b (G:real->real^N->real^N^N) Tf Hf Tf' Hf'.
     rfa_heat k U a b G Tf Hf /\ open U /\
     (!t y u. a < t /\ t < b /\ y IN U ==> Tf' t y u = Tf t y u /\ Hf' t y u = Hf t y u)
     ==> rfa_heat k U a b G Tf' Hf'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "fd")
    (CONJUNCTS_THEN2 (LABEL_TAC "js") (LABEL_TAC "dt")))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_EQ THEN
      EXISTS_TAC `(Tf:real->real^N->(num->real^N)->real) t` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_TENSOR_FIELD_EQ THEN
      EXISTS_TAC `(Hf:real->real^N->(num->real^N)->real) t` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y. lift((Hf:real->real^N->(num->real^N)->real) t y u)` THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z. lift((Tf:real->real^N->(num->real^N)->real)
                          (drop(fstcart z)) (sndcart z) u)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_PCROSS_INTERVAL_TIME) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. (Tf:real->real^N->(num->real^N)->real) s y u` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "eq" (fun th -> MP_TAC(SPECL [`s:real`; `y:real^N`;
      `u:num->real^N`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltlap k ((G:real->real^N->real^N^N) t) (Tf' t) y u = ltlap k (G t) (Tf t) y u /\
    rfa_rcact k (G t) (Tf' t) y u = rfa_rcact k (G t) (Tf t) y u /\
    (Hf':real->real^N->(num->real^N)->real) t y u = Hf t y u`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTLAP_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_RCACT_LOCAL THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "dt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Linear combinations and slot permutations.                                *)
(* ========================================================================= *)

let RFA_PERMUTES_OUTSIDE = prove
 (`!k s m. s permutes 1..k /\ k < m ==> s m = m`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT1 o
    REWRITE_RULE[permutes]) THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let RFA_PERMUTES_EQ_ABOVE = prove
 (`!k s m n. s permutes 1..k /\ k < n ==> (s m = n <=> m = n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RFA_PERMUTES_OUTSIDE THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `1 <= m /\ m <= k` THENL
   [SUBGOAL_THEN `(s:num->num) m IN 1..k` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_IN_IMAGE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `(s:num->num) m = m` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[permutes]) THEN
    ASM_REWRITE_TAC[IN_NUMSEG]]);;

let RFA_LNABLA_ITER_LTPERM = prove
 (`!k s (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     s permutes 1..k
     ==> !l y u. lnabla_iter k l G (ltperm s tf) y u =
                 lnabla_iter k l G tf y (\m. u(s m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ltperm]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lnabla_iter] THEN
  SUBGOAL_THEN
   `lnabla_iter k l (G:real^N->real^N^N) (ltperm s tf) =
    (\x u. lnabla_iter k l G tf x (\m. u(s m)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_LNABLA_PERMUTE THEN
  MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC `1..k` THEN
  ASM_REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC);;

let RFA_LTLAP_LTPERM = prove
 (`!k s (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     s permutes 1..k
     ==> ltlap k G (ltperm s tf) y u = ltlap k G tf y (\m. u(s m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltlap] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFA_LNABLA_ITER_LTPERM th]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  MP_TAC(ISPECL [`k:num`; `s:num->num`; `m:num`; `k + 1`] RFA_PERMUTES_EQ_ABOVE) THEN
  MP_TAC(ISPECL [`k:num`; `s:num->num`; `m:num`; `k + 2`] RFA_PERMUTES_EQ_ABOVE) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k < k + 1 /\ k < k + 2`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

let RFA_RCACT_LTPERM = prove
 (`!k s (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     s permutes 1..k
     ==> rfa_rcact k G (ltperm s tf) y u = rfa_rcact k G tf y (\m. u(s m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rcact; ltperm] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP SUM_PERMUTE th]) THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `((s:num->num) m = s j <=> m = j)` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INJECTIVE) THEN SIMP_TAC[]);;

let RFA_LTLAP_CMUL = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) c y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\
     y IN U
     ==> ltlap k G (\x u. c * tf x u) y u = c * ltlap k G tf y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `tf:real^N->(num->real^N)->real`;
                 `c:real`; `&0`; `y:real^N`; `u:num->real^N`] RFA_LTLAP_LINCOMB) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]);;

let RFA_HEAT_LINCOMB = prove
 (`!k U a b (G:real->real^N->real^N^N) T1 H1 T2 H2 c1 c2.
     lricci_flow U a b G /\ rfa_heat k U a b G T1 H1 /\ rfa_heat k U a b G T2 H2
     ==> rfa_heat k U a b G (\t y u. c1 * T1 t y u + c2 * T2 t y u)
                            (\t y u. c1 * H1 t y u + c2 * H2 t y u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                !t. a < t /\ t < b ==> metric_field U ((G:real->real^N->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `T1:real->real^N->(num->real^N)->real`;
                 `H1:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `T2:real->real^N->(num->real^N)->real`;
                 `H2:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "s2") THEN DISCH_THEN(LABEL_TAC "s1") THEN
  UNDISCH_TAC `rfa_heat k U a b (G:real->real^N->real^N^N) T2 H2` THEN
  UNDISCH_TAC `rfa_heat k U a b (G:real->real^N->real^N^N) T1 H1` THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "j1")
    (LABEL_TAC "d1"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f2") (CONJUNCTS_THEN2 (LABEL_TAC "j2")
    (LABEL_TAC "d2"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "f1" (MP_TAC o SPEC `t:real`) THEN USE_THEN "f2" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC RFA_SMOOTH_LIFT_LINCOMB THEN ASM_REWRITE_TAC[]];
    GEN_TAC THEN MATCH_MP_TAC RFA_SMOOTH_LIFT_LINCOMB THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "f1" (MP_TAC o SPEC `t:real`) THEN USE_THEN "f2" (MP_TAC o SPEC `t:real`) THEN
  REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltlap k ((G:real->real^N->real^N^N) t) (\y u. c1 * T1 t y u + c2 * T2 t y u) y u =
    c1 * ltlap k (G t) (T1 t) y u + c2 * ltlap k (G t) (T2 t) y u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_LTLAP_LINCOMB THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_RCACT_LINCOMB; ETA_AX] THEN
  MATCH_MP_TAC(MESON[]
   `!f x y net. (f has_real_derivative x) net /\ (x:real) = y
                ==> (f has_real_derivative y) net`) THEN
  EXISTS_TAC `c1 * (ltlap k ((G:real->real^N->real^N^N) t) (T1 t) y u -
                    rfa_rcact k (G t) (T1 t) y u + H1 t y u) +
              c2 * (ltlap k (G t) (T2 t) y u - rfa_rcact k (G t) (T2 t) y u + H2 t y u)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[]);;

let RFA_HC_HRD_EQ = prove
 (`!f x y net. (f has_real_derivative x) net /\ (x:real) = y
               ==> (f has_real_derivative y) net`,
  MESON_TAC[]);;

let RFA_HEAT_PERM = prove
 (`!k s U a b (G:real->real^N->real^N^N) Tf Hf.
     lricci_flow U a b G /\ rfa_heat k U a b G Tf Hf /\ s permutes 1..k
     ==> rfa_heat k U a b G (\t. ltperm s (Tf t)) (\t. ltperm s (Hf t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "fd") (CONJUNCTS_THEN2 (LABEL_TAC "js") (LABEL_TAC "dt")))
    ASSUME_TAC)) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPERM_SMOOTH THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[ltperm] THEN
    USE_THEN "js" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_LTLAP_LTPERM; RFA_RCACT_LTPERM] THEN
  REWRITE_TAC[ltperm] THEN USE_THEN "dt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Time factors and the metric (heat defect 0).                              *)
(* ========================================================================= *)

let RFA_TENSOR_FIELD_ZERO = prove
 (`!k (U:real^N->bool). ltensor_field k U (\y u. &0)`,
  REWRITE_TAC[ltensor_field; LIFT_NUM; LINEAR_ZERO]);;

let RFA_RCACT_ZERO = prove
 (`!k (G:real^N->real^N^N) y u. rfa_rcact k G (\y u. &0) y u = &0`,
  REWRITE_TAC[rfa_rcact; REAL_MUL_RZERO; SUM_0]);;

let RFA_JOINT_TIME_SMOOTH = prove
 (`!a b (U:real^N->bool) (c:real->real).
     open U /\ smooth_map_on (interval(lift a,lift b)) (\x. lift(c(drop x)))
     ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
           (\z. lift(c(drop(fstcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift(c(drop(fstcart z)))) =
                (\x. lift(c(drop x))) o (fstcart o (\z:real^(1,N)finite_sum. z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_FSTCART_OPEN; SMOOTH_MAP_ON_ID] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART] THEN SIMP_TAC[]);;

let RFA_HEAT_TMUL = prove
 (`!k U a b (G:real->real^N->real^N^N) Tf Hf (c:real->real) c'.
     lricci_flow U a b G /\ rfa_heat k U a b G Tf Hf /\
     (!t. a < t /\ t < b ==> (c has_real_derivative c' t) (atreal t)) /\
     smooth_map_on (interval(lift a,lift b)) (\x. lift(c(drop x)))
     ==> rfa_heat k U a b G (\t y u. c t * Tf t y u)
                            (\t y u. c' t * Tf t y u + c t * Hf t y u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                !t. a < t /\ t < b ==> metric_field U ((G:real->real^N->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `Tf:real->real^N->(num->real^N)->real`;
                 `Hf:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sl") THEN
  UNDISCH_TAC `rfa_heat k U a b (G:real->real^N->real^N^N) Tf Hf` THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fd") (CONJUNCTS_THEN2 (LABEL_TAC "js")
    (LABEL_TAC "dt"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC RFA_SMOOTH_LIFT_LINCOMB THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; RFA_JOINT_TIME_SMOOTH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN
  REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_HC_HRD_EQ THEN
  EXISTS_TAC `c t * (ltlap k ((G:real->real^N->real^N^N) t)
                       ((Tf:real->real^N->(num->real^N)->real) t) y u -
                     rfa_rcact k (G t) (Tf t) y u + Hf t y u) +
              c' t * Tf t y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; USE_THEN "dt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`; `(c:real->real) t`;
                 `y:real^N`; `u:num->real^N`] RFA_LTLAP_CMUL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`; `(c:real->real) t`; `&0`;
                 `y:real^N`; `u:num->real^N`] RFA_RCACT_LINCOMB) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

(* The metric: d/dt g(u1,u2) = -2 Ric(u1,u2) = Lap g - Rc.g with Lap g = 0. *)

let RFA_BFORM_EXPAND = prove
 (`!(A:real^N^N) v w.
     v dot (A ** w) =
     sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. v$i * A$i$j * w$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_LMETRIC2_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y u.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. lmetric2 (G s) y u) has_real_derivative
          --(&2) * lric2 (G t) y u) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  REWRITE_TAC[lmetric2; lric2] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`] LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_BFORM_EXPAND] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN
   `((\s. (G:real->real^N->real^N^N) s y$i$j) has_real_derivative
     --(&2) * lricci (G t) y (basis i) (basis j)) (atreal t)`
  MP_TAC THENL
   [UNDISCH_TAC `lricci_flow U a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `((u:num->real^N) 2)$j` o
             MATCH_MP HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPEC `((u:num->real^N) 1)$i` o
             MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

let RFA_RCACT_LMETRIC2 = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U
     ==> rfa_rcact 2 G (lmetric2 G) y u = &2 * lric2 G y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2(G:real^N->real^N^N)`;
                 `y:real^N`; `2`; `\m. if m = 1 then (u:num->real^N) 1 else u 2`;
                 `(u:num->real^N) 2`] RFA_METRIC_EXPAND) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2(G:real^N->real^N^N)`;
                 `y:real^N`; `2`; `\m. if m = 1 then (u:num->real^N) 2 else u 1`;
                 `(u:num->real^N) 1`] RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[ARITH; lric2] THEN
  DISCH_THEN(LABEL_TAC "e21" o SYM) THEN DISCH_THEN(LABEL_TAC "e12" o SYM) THEN
  REWRITE_TAC[rfa_rcact; SUM_2; lmetric2; ARITH] THEN
  SUBGOAL_THEN `lricci (G:real^N->real^N^N) y (u 2) (u 1) = lricci G y (u 1) (u 2)`
  (LABEL_TAC "sy") THENL [ASM_MESON_TAC[LRICCI_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = r /\ y = r ==> x + y = &2 * r`) THEN CONJ_TAC THENL
   [USE_THEN "e12" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    USE_THEN "sy" (SUBST1_TAC o SYM) THEN
    USE_THEN "e21" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(u:num->real^N) 1 dot ((G:real^N->real^N^N) y ** basis p) =
                  basis p dot (G y ** u 1)`
    SUBST1_TAC THENL [ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let RFA_LMETRIC2_JOINT = prove
 (`!U a b (G:real->real^N->real^N^N) u.
     lricci_flow U a b G
     ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
           (\z. lift(lmetric2 (G (drop(fstcart z))) (sndcart z) u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (G (drop(fstcart z)) (sndcart z)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(lmetric2 ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z) u)) =
    (\m:real^(N,N)finite_prod. lift((u:num->real^N) 1 dot (matrify m ** u 2))) o
    (\z. vectorize(G (drop(fstcart z)) (sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; lmetric2; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

let RFA_HEAT_METRIC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. lmetric2 (G t)) (\t y u. &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_heat; RFA_TENSOR_FIELD_ZERO; LIFT_NUM] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`]
             LRG_LMETRIC2_FIELD) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[lricci_flow]; SIMP_TAC[]];
      REWRITE_TAC[SMOOTH_MAP_ON_CONST]];
    GEN_TAC THEN MATCH_MP_TAC RFA_LMETRIC2_JOINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `u:num->real^N`] RFA_LTLAP2_METRIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `u:num->real^N`] RFA_RCACT_LMETRIC2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC RFA_HC_HRD_EQ THEN EXISTS_TAC `--(&2) * lric2 ((G:real->real^N->real^N^N) t) y u` THEN
  CONJ_TAC THENL [MATCH_MP_TAC RFA_LMETRIC2_DT THEN ASM_MESON_TAC[]; REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Tensor products: the rough Laplacian of A (x) B, the Ricci                *)
(* action, and the product rule of the heat-defect calculus.                 *)
(* ========================================================================= *)

(* Normal form of the index arithmetic: every maximal num sum is put in    *)
(* NUM_NORMALIZE_CONV form (used to align slot indices of instantiated      *)
(* Leibniz rules with the goal).                                             *)

let RFA_NUM_NORM_CONV =
  ONCE_DEPTH_CONV
   (fun tm -> if is_binary "+" tm && type_of tm = `:num`
              then NUM_NORMALIZE_CONV tm else failwith "RFA_NUM_NORM_CONV");;

let RFA_TF_AGREE = prove
 (`!k U (tf:real^N->(num->real^N)->real) y w w'.
     ltensor_field k U tf /\ y IN U /\ (!m. 1 <= m /\ m <= k ==> w m = w' m)
     ==> tf y w = tf y w'`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

let RFA_LNABLA2_LTPROD_EVAL = prove
 (`!p q U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B y u x1 x2.
     metric_field U G /\ ltensor_field p U A /\ ltensor_field q U B /\
     (!u. smooth_map_on U (\x. lift(A x u))) /\ (!u. smooth_map_on U (\x. lift(B x u))) /\
     y IN U
     ==> lnabla_iter (p + q) 2 G (ltprod p A B) y
           (\m. if m = (p + q) + 1 then x1 else if m = (p + q) + 2 then x2 else u m) =
         lnabla_iter p 2 G A y
           (\m. if m = p + 1 then x1 else if m = p + 2 then x2 else u m) *
         B y (\m. u(m + p)) +
         lnabla p G A y (\m. if m = p + 1 then x1 else u m) *
         lnabla q G B y (\m. if m = q + 1 then x2 else u(m + p)) +
         lnabla p G A y (\m. if m = p + 1 then x2 else u m) *
         lnabla q G B y (\m. if m = q + 1 then x1 else u(m + p)) +
         A y u *
         lnabla_iter q 2 G B y
           (\m. if m = q + 1 then x1 else if m = q + 2 then x2 else u(m + p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `B:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla p (G:real^N->real^N^N) A`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`q + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla q (G:real^N->real^N^N) B`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `cy = \m. if m <= p then m else if m = p + 1 then p + q + 1
                       else if m <= p + q + 1 then m - 1 else m` THEN
  SUBGOAL_THEN `cy permutes 1..(p + q) + 1` ASSUME_TAC THENL
   [EXPAND_TAC "cy" THEN REWRITE_TAC[RFA_CYC_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z w. z IN U
          ==> lnabla (p + q) (G:real^N->real^N^N) (ltprod p A B) z w =
              ltperm cy (ltprod (p + 1) (lnabla p G A) B) z w +
              ltprod p A (lnabla q G B) z w`
  (LABEL_TAC "d1") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "cy" THEN MATCH_MP_TAC RFA_LNABLA_LTPROD_PERM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field ((p + q) + 1) U
      (ltperm cy (ltprod (p + 1) (lnabla p (G:real^N->real^N^N) A) B)) /\
    (!w. smooth_map_on U
           (\x. lift(ltperm cy (ltprod (p + 1) (lnabla p (G:real^N->real^N^N) A) B) x w))) /\
    ltensor_field ((p + q) + 1) U (ltprod p A (lnabla q (G:real^N->real^N^N) B)) /\
    (!w. smooth_map_on U (\x. lift(ltprod p A (lnabla q (G:real^N->real^N^N) B) x w)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(p + q) + 1 = (p + 1) + q`] THEN
      MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPERM_SMOOTH THEN MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `(p + q) + 1 = p + q + 1`] THEN
      MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the second covariant derivative of the product, evaluated *)
  SUBGOAL_THEN
   `!W. lnabla_iter (p + q) 2 (G:real^N->real^N^N) (ltprod p A B) y W =
        lnabla ((p + q) + 1) G
          (ltprod (p + 1) (lnabla p G A) B) y (\m. W(cy m)) +
        lnabla ((p + q) + 1) G (ltprod p A (lnabla q G B)) y W`
  (LABEL_TAC "d2") THENL
   [GEN_TAC THEN REWRITE_TAC[RFA_LNABLA_ITER_2] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla ((p + q) + 1) (G:real^N->real^N^N)
        (\z w. ltperm cy (ltprod (p + 1) (lnabla p G A) B) z w +
               ltprod p A (lnabla q G B) z w) y W` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(p + q) + 1`; `G:real^N->real^N^N`;
       `ltperm cy (ltprod (p + 1) (lnabla p (G:real^N->real^N^N) A) B)`;
       `ltprod p A (lnabla q (G:real^N->real^N^N) B)`; `y:real^N`; `W:num->real^N`]
       LRG_LNABLA_ADD) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFA_LNABLA_LTPERM th]) THEN
    REWRITE_TAC[ltperm];
    ALL_TAC] THEN
  USE_THEN "d2" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p + 1`; `q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla p (G:real^N->real^N^N) A`; `B:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LNABLA_LTPROD) THEN
  MP_TAC(ISPECL [`p:num`; `q + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`; `lnabla q (G:real^N->real^N^N) B`;
                 `y:real^N`] RFA_LNABLA_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC RFA_NUM_NORM_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `!m. cy m = (if m <= p then m else if m = p + 1 then p + q + 1
                else if m <= p + q + 1 then m - 1 else m)`
  (LABEL_TAC "cyd") THENL [EXPAND_TAC "cy" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = a' /\ b = b' /\ c = c' /\ d = d' ==> (a + b) + (c + d) = a' + b' + c' + d':real`) THEN
  REPEAT CONJ_TAC THEN BINOP_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THENL
   [EXISTS_TAC `(p + 1) + 1`; EXISTS_TAC `q:num`; EXISTS_TAC `p + 1`; EXISTS_TAC `q + 1`;
    EXISTS_TAC `p + 1`; EXISTS_TAC `q + 1`; EXISTS_TAC `p:num`; EXISTS_TAC `(q + 1) + 1`] THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  USE_THEN "cyd" (fun th -> REWRITE_TAC[th]) THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN TRY ASM_ARITH_TAC);;

let RFA_LTLAP_LTPROD = prove
 (`!p q U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B y u.
     metric_field U G /\ ltensor_field p U A /\ ltensor_field q U B /\
     (!u. smooth_map_on U (\x. lift(A x u))) /\ (!u. smooth_map_on U (\x. lift(B x u))) /\
     y IN U
     ==> ltlap (p + q) G (ltprod p A B) y u =
         ltprod p (ltlap p G A) B y u + ltprod p A (ltlap q G B) y u +
         &2 * rfa_xgrad p q G A B y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`; `B:real^N->(num->real^N)->real`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA2_LTPROD_EVAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ltlap] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ltprod; rfa_xgrad; ltlap] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) y)$a$b *
       lnabla p G A y (\m. if m = p + 1 then basis b else u m) *
       lnabla q G B y (\m. if m = q + 1 then basis a else u(m + p)))) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) y)$a$b *
       lnabla p G A y (\m. if m = p + 1 then basis a else u m) *
       lnabla q G B y (\m. if m = q + 1 then basis b else u(m + p))))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y)$b$a = matrix_inv(G y)$a$b`
    SUBST1_TAC THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. matrix_inv((G:real^N->real^N^N) y)$a$b *
          lnabla_iter p 2 G A y
             (\m. if m = p + 1 then basis a else if m = p + 2 then basis b else u m) *
          B y (\m. u(m + p)) =
          (matrix_inv(G y)$a$b *
           lnabla_iter p 2 G A y
             (\m. if m = p + 1 then basis a else if m = p + 2 then basis b else u m)) *
          B y (\m. u(m + p))`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. matrix_inv((G:real^N->real^N^N) y)$a$b *
          A y u *
          lnabla_iter q 2 G B y
             (\m. if m = q + 1 then basis a else if m = q + 2 then basis b else u(m + p)) =
          A y u *
          (matrix_inv(G y)$a$b *
           lnabla_iter q 2 G B y
             (\m. if m = q + 1 then basis a else if m = q + 2 then basis b else u(m + p)))`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL; SUM_LMUL] THEN REAL_ARITH_TAC);;

let RFA_RCACT_LTPROD = prove
 (`!p q U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B y u.
     ltensor_field p U A /\ ltensor_field q U B /\ y IN U
     ==> rfa_rcact (p + q) G (ltprod p A B) y u =
         ltprod p (rfa_rcact p G A) B y u + ltprod p A (rfa_rcact q G B) y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rcact; ltprod] THEN
  MP_TAC(ISPECL [`\i. sum(1..dimindex(:N)) (\p'. sum(1..dimindex(:N)) (\q'.
      matrix_inv((G:real^N->real^N^N) y)$p'$q' * lricci G y (u i) (basis q') *
      (A:real^N->(num->real^N)->real) y (\m. if m = i then basis p' else u m) *
      (B:real^N->(num->real^N)->real) y
        (\m. if m + p = i then basis p' else u(m + p))))`;
      `1`; `p:num`; `q:num`] SUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= p + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p + 1 = 1 + p /\ p + q = q + p` (fun th ->
    REWRITE_TAC[CONJUNCT1 th] THEN SUBST1_TAC(CONJUNCT2 th)) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN
  REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN BINOP_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THENL
   [SUBGOAL_THEN
     `(B:real^N->(num->real^N)->real) y (\m. if m + p = i then basis a else u(m + p)) =
      B y (\m. u(m + p))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`q:num`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((m:num) + p = i)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN
     `(A:real^N->(num->real^N)->real) y (\m. if m = i + p then basis a else u m) = A y u`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`p:num`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((m:num) = i + p)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\m. if m + p = i + p then basis a else (u:num->real^N)(m + p)) =
      (\m. if m = i then basis a else u(m + p))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; EQ_ADD_RCANCEL]; REAL_ARITH_TAC]]);;

let RFA_XGRAD_FIELD = prove
 (`!p q U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B.
     metric_field U G /\ ltensor_field p U A /\ ltensor_field q U B /\
     (!u. smooth_map_on U (\x. lift(A x u))) /\ (!u. smooth_map_on U (\x. lift(B x u)))
     ==> ltensor_field (p + q) U (rfa_xgrad p q G A B) /\
         (!u. smooth_map_on U (\y. lift(rfa_xgrad p q G A B y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `B:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fb") (LABEL_TAC "sb")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fa") (LABEL_TAC "sa")) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfa_xgrad] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_SMOOTH_LIFT_MUL3 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!w w'. (!m. 1 <= m /\ m <= p + 1 ==> w m = w' m)
            ==> lnabla p (G:real^N->real^N^N) A y w = lnabla p G A y w') /\
    (!i w. 1 <= i /\ i <= p + 1
           ==> linear (\v. lift(lnabla p (G:real^N->real^N^N) A y
                                  (\j. if j = i then v else w j)))) /\
    (!w w'. (!m. 1 <= m /\ m <= q + 1 ==> w m = w' m)
            ==> lnabla q (G:real^N->real^N^N) B y w = lnabla q G B y w') /\
    (!i w. 1 <= i /\ i <= q + 1
           ==> linear (\v. lift(lnabla q (G:real^N->real^N^N) B y
                                  (\j. if j = i then v else w j))))`
  MP_TAC THENL
   [REMOVE_THEN "fa" MP_TAC THEN REMOVE_THEN "fb" MP_TAC THEN
    REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (CONJUNCTS_THEN2 (LABEL_TAC "la")
    (CONJUNCTS_THEN2 (LABEL_TAC "bg") (LABEL_TAC "lb")))) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN
    DISCH_THEN(LABEL_TAC "uu") THEN REWRITE_TAC[rfa_xgrad] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [USE_THEN "ag" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN USE_THEN "uu" MATCH_MP_TAC THEN RFA_ARITH_TAC;
      USE_THEN "bg" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN USE_THEN "uu" MATCH_MP_TAC THEN RFA_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_xgrad; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `(j:num) <= p` THENL
   [SUBGOAL_THEN
     `!v:real^N. lnabla q (G:real^N->real^N^N) B y
        (\m. if m = q + 1 then basis b else if m + p = j then v else u(m + p)) =
      lnabla q G B y (\m. if m = q + 1 then basis b else u(m + p))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN USE_THEN "bg" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((m:num) + p = j)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `g * x * c = (g * c) * x:real`] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    USE_THEN "la" (MP_TAC o SPECL [`j:num`;
      `\m. if m = p + 1 then basis a else (u:num->real^N) m`]) THEN
    ANTS_TAC THENL [RFA_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
    ASM_CASES_TAC `m:num = j` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((j:num) = p + 1)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. lnabla p (G:real^N->real^N^N) A y
      (\m. if m = p + 1 then basis a else if m = j then v else u m) =
    lnabla p G A y (\m. if m = p + 1 then basis a else u m)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "ag" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m:num = j)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  USE_THEN "lb" (MP_TAC o SPECL [`(j:num) - p`;
    `\m. if m = q + 1 then basis b else (u:num->real^N)(m + p)`]) THEN
  ANTS_TAC THENL [RFA_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ASM_CASES_TAC `(m:num) = j - p` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~((j:num) - p = q + 1) /\ (j - p) + p = j` (fun th -> REWRITE_TAC[th]) THEN
    RFA_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((m:num) + p = j)` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC]);;

let RFA_TENSOR_FIELD_SUB = prove
 (`!k U (f:real^N->(num->real^N)->real) g.
        ltensor_field k U f /\ ltensor_field k U g
        ==> ltensor_field k U (\y u. f y u - g y u)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THENL
   [BINOP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    ASM_MESON_TAC[]]);;

let RFA_TENSOR_FIELD_LIN3 = prove
 (`!k U (f1:real^N->(num->real^N)->real) f2 f3 c.
        ltensor_field k U f1 /\ ltensor_field k U f2 /\ ltensor_field k U f3
        ==> ltensor_field k U (\y u. f1 y u + f2 y u - c * f3 y u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `f1:real^N->(num->real^N)->real`;
                 `\y u. (f2:real^N->(num->real^N)->real) y u -
                        c * (f3:real^N->(num->real^N)->real) y u`]
         RFA_TENSOR_FIELD_ADD) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `f2:real^N->(num->real^N)->real`;
                 `\y u. c * (f3:real^N->(num->real^N)->real) y u`]
         RFA_TENSOR_FIELD_SUB) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `f3:real^N->(num->real^N)->real`;
                 `c:real`] RFA_TENSOR_FIELD_CMUL) THEN
  ASM_REWRITE_TAC[]);;

let RFA_HEAT_LTPROD = prove
 (`!p q U a b (G:real->real^N->real^N^N) A HA B HB.
     lricci_flow U a b G /\ rfa_heat p U a b G A HA /\ rfa_heat q U a b G B HB
     ==> rfa_heat (p + q) U a b G (\t. ltprod p (A t) (B t))
           (\t y u. ltprod p (HA t) (B t) y u + ltprod p (A t) (HB t) y u -
                    &2 * rfa_xgrad p q (G t) (A t) (B t) y u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                !t. a < t /\ t < b ==> metric_field U ((G:real->real^N->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `A:real->real^N->(num->real^N)->real`;
                 `HA:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `B:real->real^N->(num->real^N)->real`;
                 `HB:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sb") THEN DISCH_THEN(LABEL_TAC "sa") THEN
  UNDISCH_TAC `rfa_heat q U a b (G:real->real^N->real^N^N) B HB` THEN
  UNDISCH_TAC `rfa_heat p U a b (G:real->real^N->real^N^N) A HA` THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fa") (CONJUNCTS_THEN2 (LABEL_TAC "ja")
    (LABEL_TAC "da"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fb") (CONJUNCTS_THEN2 (LABEL_TAC "jb")
    (LABEL_TAC "db"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fa" (MP_TAC o SPEC `t:real`) THEN USE_THEN "fb" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(A:real->real^N->(num->real^N)->real) t`;
                   `(B:real->real^N->(num->real^N)->real) t`] RFA_XGRAD_FIELD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    USE_THEN "sa" (MP_TAC o SPEC `t:real`) THEN USE_THEN "sb" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN
    DISCH_THEN(LABEL_TAC "sbt") THEN DISCH_THEN(LABEL_TAC "sat") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_TENSOR_FIELD_LIN3 THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[LIFT_SUB; LIFT_ADD; LIFT_CMUL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`p:num`; `U:real^N->bool`;
                       `(HA:real->real^N->(num->real^N)->real) t`;
                       `(B:real->real^N->(num->real^N)->real) t`] RFA_LTPROD_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`p:num`; `U:real^N->bool`;
                       `(A:real->real^N->(num->real^N)->real) t`;
                       `(HB:real->real^N->(num->real^N)->real) t`] RFA_LTPROD_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[ltprod] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "fa" (MP_TAC o SPEC `t:real`) THEN USE_THEN "fb" (MP_TAC o SPEC `t:real`) THEN
  REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(A:real->real^N->(num->real^N)->real) t`;
                 `(B:real->real^N->(num->real^N)->real) t`; `y:real^N`; `u:num->real^N`]
         RFA_LTLAP_LTPROD) THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(A:real->real^N->(num->real^N)->real) t`;
                 `(B:real->real^N->(num->real^N)->real) t`; `y:real^N`; `u:num->real^N`]
         RFA_RCACT_LTPROD) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ltprod] THEN MATCH_MP_TAC RFA_HC_HRD_EQ THEN
  EXISTS_TAC
   `(A:real->real^N->(num->real^N)->real) t y u *
    (ltlap q ((G:real->real^N->real^N^N) t) (B t) y (\m. u(m + p)) -
     rfa_rcact q (G t) (B t) y (\m. u(m + p)) +
     (HB:real->real^N->(num->real^N)->real) t y (\m. u(m + p))) +
    (ltlap p (G t) (A t) y u - rfa_rcact p (G t) (A t) y u +
     (HA:real->real^N->(num->real^N)->real) t y u) *
    (B:real->real^N->(num->real^N)->real) t y (\m. u(m + p))` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
   [USE_THEN "da" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "db" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Contractions: the Laplacian and the Ricci action commute                  *)
(* with ltcontr up to the time derivative of the metric inverse, and the    *)
(* contraction rule of the heat-defect calculus.                             *)
(* ========================================================================= *)

let RFA_LNABLA_ITER2_LTCONTR = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field (k + 2) U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
     ==> lnabla_iter k 2 G (ltcontr G tf) y u =
         ltcontr G (lnabla_iter (k + 2) 2 G tf) y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla (k + 1) (G:real^N->real^N^N)
                (ltcontr G (lnabla (k + 2) G tf)) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LNABLA_LTCONTR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla (k + 2) (G:real^N->real^N^N) tf`; `y:real^N`; `u:num->real^N`]
         RFA_LNABLA_LTCONTR) THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 2 = (k + 2) + 1`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_LTLAP_LTCONTR = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field (k + 2) U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
     ==> ltlap k G (ltcontr G tf) y u = ltcontr G (ltlap (k + 2) G tf) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`]
         RFA_LNABLA_ITER2_LTCONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ltlap] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ltcontr; ltlap] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [RFA_SUM4_PAIRSWAP] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`(k + 2) + 2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN RFA_ARITH_TAC) THEN TRY RFA_ARITH_TAC);;

let RFA_GINV_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> ((\s. matrix_inv(G s y)$p$q) has_real_derivative
          &2 * sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
                 matrix_inv(G t y)$p$c * lricci (G t) y (basis c) (basis d) *
                 matrix_inv(G t y)$d$q))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] LRG_FLOW_DGINV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `q:num`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] (ISPECL
      [`\s. matrix_inv((G:real->real^N->real^N^N) s y)`] LRG_VDERIV_MATRIX_ENTRY_REAL))) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  ASM_SIMP_TAC[MATRIX_NEG_COMPONENT; matrix_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* Reordering four-fold sums over 1..n.                                     *)

let RFA_SUM4_ROT = prove
 (`!n (f:num->num->num->num->real).
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\p. sum(1..n) (\q. f a b p q)))) =
     sum(1..n) (\p. sum(1..n) (\b. sum(1..n) (\q. sum(1..n) (\a. f a b p q))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
  BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

let RFA_SUM4_MID = prove
 (`!n (f:num->num->num->num->real).
     sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\p. sum(1..n) (\q. f a b p q)))) =
     sum(1..n) (\a. sum(1..n) (\p. sum(1..n) (\b. sum(1..n) (\q. f a b p q))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  REFL_TAC);;

let RFA_SUM5_SHIFT = prove
 (`!n k (f:num->num->num->num->num->real).
     sum(1..n) (\a. sum(1..n) (\b. sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q.
       f a b i p q))))) =
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. sum(1..n) (\a. sum(1..n) (\b.
       f a b i p q)))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
  BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV o BINDER_CONV)
    [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN
  BETA_TAC THEN REFL_TAC);;

let RFA_LTCONTR_RCACT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field (k + 2) U tf /\ y IN U
     ==> ltcontr G (rfa_rcact (k + 2) G tf) y u =
         rfa_rcact k G (ltcontr G tf) y u +
         &2 * sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
                  matrix_inv(G y)$a$c * lricci G y (basis c) (basis d) *
                  matrix_inv(G y)$d$b *
                  tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                            else u(m - 2))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. matrix_inv((G:real^N->real^N^N) y)$a$b = matrix_inv(G y)$b$a`
  (LABEL_TAC "gs") THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!c d. lricci (G:real^N->real^N^N) y (basis c) (basis d) =
                      lricci G y (basis d) (basis c)`
  (LABEL_TAC "rs") THENL [ASM_MESON_TAC[LRICCI_SYM]; ALL_TAC] THEN
  REWRITE_TAC[ltcontr; rfa_rcact] THEN
  REWRITE_TAC[ARITH_RULE `k + 2 = 2 + k`] THEN
  MP_TAC(GEN `f:num->real` (ISPECL [`f:num->real`; `1`; `2`; `k:num`] SUM_ADD_SPLIT)) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 2 + 1`] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `2 + 1 = 1 + 2`; SUM_OFFSET; SUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `3 = 1 + 2 /\ 2 + k = k + 2` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN
  REWRITE_TAC[ARITH_RULE `!i. ~(i + 2 = 1) /\ (i + 2 = 2 <=> i = 0) /\ (i + 2) - 2 = i`] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a1 = q /\ a2 = q /\ a3 = r ==> (a1 + a2) + a3 = r + &2 * q:real`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN GEN_REWRITE_TAC LAND_CONV [RFA_SUM4_ROT] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i1:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i2:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i3:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i4:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `(\m. if m = 1 then basis i1 else if m = 1 then basis i4
           else if m = 2 then basis i2 else (u:num->real^N)(m - 2)) =
      (\m. if m = 1 then basis i1 else if m = 2 then basis i2 else u(m - 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "rs" (fun th -> REWRITE_TAC[SPECL [`i4:num`; `i3:num`] th]) THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM SUM_LMUL] THEN GEN_REWRITE_TAC LAND_CONV [RFA_SUM4_MID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i1:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i2:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i3:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i4:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `(\m. if m = 2 then basis i2 else if m = 1 then basis i1
           else if m = 2 then basis i3 else (u:num->real^N)(m - 2)) =
      (\m. if m = 1 then basis i1 else if m = 2 then basis i2 else u(m - 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    USE_THEN "gs" (fun th -> REWRITE_TAC[SPECL [`i2:num`; `i4:num`] th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN GEN_REWRITE_TAC LAND_CONV [RFA_SUM5_SHIFT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~(i = 0)` (fun th -> REWRITE_TAC[th]) THENL [RFA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\m. if m = i + 2 then basis p else if m = 1 then basis a
         else if m = 2 then basis b else (u:num->real^N)(m - 2)) =
    (\m. if m = 1 then basis a else if m = 2 then basis b
         else if m - 2 = i then basis p else u(m - 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN RFA_ARITH_TAC;
    REAL_ARITH_TAC]);;

let RFA_HEAT_LTCONTR = prove
 (`!k U a b (G:real->real^N->real^N^N) Tf Hf.
     lricci_flow U a b G /\ rfa_heat (k + 2) U a b G Tf Hf
     ==> rfa_heat k U a b G (\t. ltcontr (G t) (Tf t)) (\t. ltcontr (G t) (Hf t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                !t. a < t /\ t < b ==> metric_field U ((G:real->real^N->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `Tf:real->real^N->(num->real^N)->real`;
                 `Hf:real->real^N->(num->real^N)->real`] RFA_HEAT_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sl") THEN
  UNDISCH_TAC `rfa_heat (k + 2) U a b (G:real->real^N->real^N^N) Tf Hf` THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fd") (CONJUNCTS_THEN2 (LABEL_TAC "js")
    (LABEL_TAC "dt"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTCONTR_SMOOTH THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[ltcontr] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC LRG_LSMOOTH_GINV_ENTRY THEN MATCH_MP_TAC RFA_LRICCI_FLOW_LSMOOTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "fd" (MP_TAC o SPEC `t:real`) THEN
  REWRITE_TAC[ASSUME `a < t`; ASSUME `t < b`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`; `y:real^N`; `u:num->real^N`]
         RFA_LTLAP_LTCONTR) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`; `y:real^N`; `u:num->real^N`]
         RFA_LTCONTR_RCACT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x = y + c ==> y = x - c:real`)) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr] THEN MATCH_MP_TAC RFA_HC_HRD_EQ THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      matrix_inv((G:real->real^N->real^N^N) t y)$i$j *
      (ltlap (k + 2) (G t) (Tf t) y
         (\m. if m = 1 then basis i else if m = 2 then basis j else u(m - 2)) -
       rfa_rcact (k + 2) (G t) (Tf t) y
         (\m. if m = 1 then basis i else if m = 2 then basis j else u(m - 2)) +
       (Hf:real->real^N->(num->real^N)->real) t y
         (\m. if m = 1 then basis i else if m = 2 then basis j else u(m - 2))) +
      (&2 * sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
         matrix_inv(G t y)$i$c * lricci (G t) y (basis c) (basis d) *
         matrix_inv(G t y)$d$j))) *
      Tf t y (\m. if m = 1 then basis i else if m = 2 then basis j else u(m - 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GINV_DT THEN ASM_MESON_TAC[];
      USE_THEN "dt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(g:real) l r h s tt. g * (l - r + h) + (&2 * s) * tt =
                          ((g * l - g * r) + g * h) + &2 * (s * tt)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL; SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `c = c' ==> ((l - r) + h) + &2 * c = l - (r - &2 * c') + h:real`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The Ricci tensor: d/dt Ric = Lap Ric - Rc.Ric + 2 Rm.Ric.                 *)
(* ========================================================================= *)

(* The heat defect of Ric, 2 R_{d a b e} R_{de} in CLN indices:              *)
(* 2 sum g^kl g^pq Rm(e_k,u1,e_p,u2) Ric(e_l,e_q).                            *)

let rfa_hric = new_definition
 `rfa_hric (G:real^N->real^N^N) y (u:num->real^N) =
    &2 * sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis k else if m = 2 then u 1
                           else if m = 3 then basis p else u 2) *
             lricci G y (basis l) (basis q)))))`;;

let RFA_HRIC_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (rfa_hric G) /\
         (!u. smooth_map_on U (\y. lift(rfa_hric G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (LABEL_TAC "rs")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mf") (LABEL_TAC "ms")) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfa_hric; LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_SMOOTH_LIFT_MUL3 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "rs" (MP_TAC o SPEC `\m. if m = 1 then basis l else (basis q:real^N)`) THEN
      REWRITE_TAC[lric2; ARITH]]] THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!w w'. (!m. 1 <= m /\ m <= 4 ==> w m = w' m)
            ==> lrm4 (G:real^N->real^N^N) y w = lrm4 G y w') /\
    (!i w. 1 <= i /\ i <= 4
           ==> linear (\v. lift(lrm4 (G:real^N->real^N^N) y
                                  (\j. if j = i then v else w j))))`
  MP_TAC THENL [REMOVE_THEN "mf" MP_TAC THEN REWRITE_TAC[ltensor_field] THEN
                ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (LABEL_TAC "li")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN
    DISCH_THEN(LABEL_TAC "uu") THEN
    SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "uu" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[rfa_hric];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_hric] THEN ONCE_REWRITE_TAC[LIFT_CMUL] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ARITH `a * b * c * d = (a * b * d) * c:real`] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  ASM_CASES_TAC `j = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH] THEN
    USE_THEN "li" (MP_TAC o SPECL [`2`;
      `\m. if m = 1 then basis k else if m = 3 then basis p
           else (u:num->real^N) 2`]) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN USE_THEN "ag" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [RFA_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]];
    SUBGOAL_THEN `j = 2` SUBST_ALL_TAC THENL [RFA_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH] THEN
    USE_THEN "li" (MP_TAC o SPECL [`4`;
      `\m. if m = 1 then basis k else if m = 2 then (u:num->real^N) 1
           else basis p`]) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN USE_THEN "ag" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [RFA_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]]]);;

let RFA_RCACT_LRIC2 = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U
     ==> rfa_rcact 2 G (lric2 G) y u =
         &2 * sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                matrix_inv(G y)$p$q * lricci G y (u 1) (basis p) *
                lricci G y (basis q) (u 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. matrix_inv((G:real^N->real^N^N) y)$a$b = matrix_inv(G y)$b$a`
  (LABEL_TAC "gs") THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!v w. lricci (G:real^N->real^N^N) y v w = lricci G y w v`
  (LABEL_TAC "rs") THENL [ASM_MESON_TAC[LRICCI_SYM]; ALL_TAC] THEN
  REWRITE_TAC[rfa_rcact; SUM_2; lric2; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `x = s /\ y = s ==> x + y = &2 * s`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "gs" (fun th -> REWRITE_TAC[SPECL [`q:num`; `p:num`] th]) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "rs" (fun th -> REWRITE_TAC[SPECL [`(u:num->real^N) 2`; `basis q:real^N`] th]) THEN
    REAL_ARITH_TAC]);;

let RFA_HEAT_RIC = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 2 U a b G (\t. lric2 (G t)) (\t. rfa_hric (G t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                !t. a < t /\ t < b ==> metric_field U ((G:real->real^N->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  REWRITE_TAC[rfa_heat] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] LRG_LRIC2_FIELD) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] RFA_HRIC_FIELD) THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN REWRITE_TAC[lric2] THEN MATCH_MP_TAC LRG_LSMOOTH_LRICCI THEN
    MATCH_MP_TAC RFA_LRICCI_FLOW_LSMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`]
         RFA_LRICCI_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `u:num->real^N`] RFA_RCACT_LRIC2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ltlap 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
      (\m. if m = 1 then (u:num->real^N) 1 else u 2) =
    ltlap 2 (G t) (lric2 (G t)) y u`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] LRG_LRIC2_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lric2((G:real->real^N->real^N^N) t)`] RFA_LTLAP_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lric2; rfa_hric] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The Leibniz rule for a contracted product.  For a p-tensor                *)
(* sf and a q-tensor tf, contracting slot i0 of sf with slot j0 of tf and    *)
(* distributing the remaining slots by the maps al, be onto 1..K (encoded by *)
(* the permutation hypothesis), nabla acts by the product rule.             *)
(* ========================================================================= *)

let RFA_LNABLA_CPROD = prove
 (`!p q K i0 j0 (al:num->num) (be:num->num) U (G:real^N->real^N^N)
    (sf:real^N->(num->real^N)->real) tf y w.
     metric_field U G /\ ltensor_field p U sf /\ ltensor_field q U tf /\
     (!u. smooth_map_on U (\x. lift(sf x u))) /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U /\ p + q = K + 2 /\ 1 <= i0 /\ i0 <= p /\ 1 <= j0 /\ j0 <= q /\
     (\m. if 1 <= m /\ m <= p then (if m = i0 then 1 else al m + 2)
          else if p < m /\ m <= p + q then (if m - p = j0 then 2 else be(m - p) + 2)
          else m) permutes 1..p + q
     ==> lnabla K G (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
            matrix_inv(G z)$a$b *
            sf z (\m. if m = i0 then basis a else w(al m)) *
            tf z (\m. if m = j0 then basis b else w(be m))))) y w =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
            matrix_inv(G y)$a$b *
            (lnabla p G sf y (\m. if m = i0 then basis a else if m = p + 1 then w(K + 1)
                                  else w(al m)) *
             tf y (\m. if m = j0 then basis b else w(be m)) +
             sf y (\m. if m = i0 then basis a else w(al m)) *
             lnabla q G tf y (\m. if m = j0 then basis b else if m = q + 1 then w(K + 1)
                                  else w(be m)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `(p:num) + q = K + 2`)) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC
   `sg = \m. if 1 <= m /\ m <= p then (if m = i0 then 1 else (al:num->num) m + 2)
             else if p < m /\ m <= p + q then (if m - p = j0 then 2 else (be:num->num)(m - p) + 2)
             else m` THEN
  SUBGOAL_THEN
   `!m. sg m = (if 1 <= m /\ m <= p then (if m = i0 then 1 else (al:num->num) m + 2)
                else if p < m /\ m <= p + q then (if m - p = j0 then 2 else (be:num->num)(m - p) + 2)
                else m)`
  (LABEL_TAC "sgd") THENL [EXPAND_TAC "sg" THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "inj" o MATCH_MP PERMUTES_INJECTIVE) THEN
  SUBGOAL_THEN `!m. 1 <= m /\ m <= p /\ ~(m = i0) ==> 1 <= (al:num->num) m`
  (LABEL_TAC "a1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inj" (MP_TAC o SPECL [`m:num`; `p + j0:num`]) THEN
    USE_THEN "sgd" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `((p:num) + j0) - p = j0`] THEN
    SUBGOAL_THEN `~(1 <= (p:num) + j0 /\ p + j0 <= p) /\ (p < p + j0 /\ p + j0 <= p + q)`
    (fun th -> REWRITE_TAC[th]) THENL [RFA_ARITH_TAC; ALL_TAC] THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. 1 <= m /\ m <= q /\ ~(m = j0) ==> 1 <= (be:num->num) m`
  (LABEL_TAC "b1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inj" (MP_TAC o SPECL [`m + p:num`; `p + j0:num`]) THEN
    USE_THEN "sgd" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `((p:num) + j0) - p = j0 /\ ((m:num) + p) - p = m`] THEN
    SUBGOAL_THEN `~(1 <= (p:num) + j0 /\ p + j0 <= p) /\ (p < p + j0 /\ p + j0 <= p + q) /\
                  ~(1 <= (m:num) + p /\ m + p <= p) /\ (p < m + p /\ m + p <= p + q)`
    (fun th -> REWRITE_TAC[th]) THENL [RFA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. 1 <= m /\ m <= p ==> sg m = (if m = i0 then 1 else (al:num->num) m + 2)`
  (LABEL_TAC "sg1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sgd" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. 1 <= m /\ m <= q ==> sg(m + p) = (if m = j0 then 2 else (be:num->num) m + 2)`
  (LABEL_TAC "sg2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sgd" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `~(1 <= (m:num) + p /\ m + p <= p) /\ (p < m + p /\ m + p <= p + q) /\
                  (m + p) - p = m` (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. (p:num) + q < m ==> sg m = m` (LABEL_TAC "sg3") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sgd" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `~(1 <= (m:num) /\ m <= p) /\ ~(p < m /\ m <= p + q)`
    (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "sgd" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!(a:num) (b:num) (w':num->real^N) m.
      1 <= m /\ m <= p
      ==> (if sg m = 1 then basis a else if sg m = 2 then basis b else w'(sg m - 2)) =
          (if m = i0 then basis a else w'((al:num->num) m))`
  (LABEL_TAC "ev1") THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "sg1" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `1 <= m`) (ASSUME `(m:num) <= p`))]) THEN
    ASM_CASES_TAC `m:num = i0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "a1" (MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `~((al:num->num) m + 2 = 1) /\ ~(al m + 2 = 2) /\ (al m + 2) - 2 = al m`
    (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(a:num) (b:num) (w':num->real^N) m.
      1 <= m /\ m <= q
      ==> (if sg(m + p) = 1 then basis a else if sg(m + p) = 2 then basis b
           else w'(sg(m + p) - 2)) =
          (if m = j0 then basis b else w'((be:num->num) m))`
  (LABEL_TAC "ev2") THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "sg2" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `1 <= m`) (ASSUME `(m:num) <= q`))]) THEN
    ASM_CASES_TAC `m:num = j0` THEN ASM_REWRITE_TAC[ARITH] THEN
    USE_THEN "b1" (MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `~((be:num->num) m + 2 = 1) /\ ~(be m + 2 = 2) /\ (be m + 2) - 2 = be m`
    (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z (w':num->real^N). z IN U
      ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
            matrix_inv((G:real^N->real^N^N) z)$a$b *
            (sf:real^N->(num->real^N)->real) z (\m. if m = i0 then basis a else w'((al:num->num) m)) *
            (tf:real^N->(num->real^N)->real) z (\m. if m = j0 then basis b else w'((be:num->num) m)))) =
          ltcontr G (ltperm sg (ltprod p sf tf)) z w'`
  (LABEL_TAC "c1") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ltcontr; ltperm; ltprod] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN BINOP_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THENL
     [MAP_EVERY EXISTS_TAC [`p:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC EQ_SYM THEN
      USE_THEN "ev1" (MATCH_MP_TAC o SPECL [`a:num`; `b:num`; `w':num->real^N`; `m:num`]) THEN
      RFA_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`q:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC EQ_SYM THEN
      USE_THEN "ev2" (MATCH_MP_TAC o SPECL [`a:num`; `b:num`; `w':num->real^N`; `m:num`]) THEN
      RFA_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(a:num) (b:num) (w':num->real^N).
      (if sg(p + q + 1) = 1 then basis a else if sg(p + q + 1) = 2 then basis b
       else w'(sg(p + q + 1) - 2)) =
      w'(K + 1)`
  (LABEL_TAC "ev3") THENL
   [REPEAT GEN_TAC THEN BETA_TAC THEN
    USE_THEN "sg3" (fun th -> REWRITE_TAC[MATCH_MP th (ARITH_RULE `(p:num) + q < p + q + 1`)]) THEN
    SUBGOAL_THEN `~((p:num) + q + 1 = 1) /\ ~(p + q + 1 = 2) /\ (p + q + 1) - 2 = K + 1`
    (fun th -> REWRITE_TAC[th]) THEN RFA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field (K + 2) U (ltperm sg (ltprod p (sf:real^N->(num->real^N)->real) tf)) /\
    (!u. smooth_map_on U (\x. lift(ltperm sg (ltprod p sf tf) x u)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_LTPROD_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTPERM_SMOOTH THEN MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla K (G:real^N->real^N^N) (ltcontr G (ltperm sg (ltprod p sf tf))) y w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm sg (ltprod p (sf:real^N->(num->real^N)->real) tf)`;
                 `y:real^N`; `w:num->real^N`] RFA_LNABLA_LTCONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP RFA_LNABLA_LTPERM (ASSUME `sg permutes 1..p + q`)] THEN
  REWRITE_TAC[ltperm] THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `sf:real^N->(num->real^N)->real`; `tf:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LNABLA_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `sf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THEN BINOP_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THENL
   [MAP_EVERY EXISTS_TAC [`p + 1`; `U:real^N->bool`];
    MAP_EVERY EXISTS_TAC [`q:num`; `U:real^N->bool`];
    MAP_EVERY EXISTS_TAC [`p:num`; `U:real^N->bool`];
    MAP_EVERY EXISTS_TAC [`q + 1`; `U:real^N->bool`]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  FIRST
   [ASM_CASES_TAC `m = p + 1` THENL
     [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~(p + 1 = i0)` (fun th -> REWRITE_TAC[th]) THEN
      RFA_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ev1" (MATCH_MP_TAC o SPECL [`a:num`; `b:num`; `w:num->real^N`; `m:num`]) THEN
      RFA_ARITH_TAC] THEN NO_TAC;
    ASM_CASES_TAC `m = q + 1` THENL
     [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~(q + 1 = j0)` (fun th -> REWRITE_TAC[th]) THENL
       [RFA_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(q + 1) + (p:num) = p + q + 1`] THEN
      USE_THEN "ev3" (fun th -> REWRITE_TAC[th]);
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ev2" (MATCH_MP_TAC o SPECL [`a:num`; `b:num`; `w:num->real^N`; `m:num`]) THEN
      RFA_ARITH_TAC] THEN NO_TAC]);;


(* ========================================================================= *)
(* nabla of the Ricci action (Leibniz).                                      *)
(* ========================================================================= *)

let RFA_LNABLA_SUM1 = prove
 (`!k (G:real^N->real^N^N) (tf:num->real^N->(num->real^N)->real) y u n.
     (!i. 1 <= i /\ i <= n ==> (\x. lift(tf i x u)) differentiable at y)
     ==> lnabla k G (\x u. sum(1..n) (\i. tf i x u)) y u =
         sum(1..n) (\i. lnabla k G (tf i) y u)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN DISCH_TAC THEN
    REWRITE_TAC[RFA_LNABLA_ZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`;
                 `\x:real^N u:num->real^N. sum(1..n) (\i. (tf:num->real^N->(num->real^N)->real) i x u)`;
                 `(tf:num->real^N->(num->real^N)->real) (SUC n)`;
                 `y:real^N`; `u:num->real^N`] LRG_LNABLA_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC DIFFERENTIABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN RFA_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RFA_ARITH_TAC);;

let SPDR10_ICOND_TAC : tactic = fun (asl,w as g) ->
  let ok t = is_cond t &&
    (let c = rand(rator(rator t)) in
     not(is_const c) && not(can (find_term is_cond) c) && subset (frees c) (frees w)) in
  let c = rand(rator(rator(find_term ok w))) in
  ASM_CASES_TAC c g;;

let SPDR10_IS_DISEQ t = is_neg t && is_eq (dest_neg t);;

let SPDR10_PRUNE_TAC : tactic = fun (asl,w as g) ->
  let ths = filter (fun th -> rfa_is_numrel (concl th) && not(SPDR10_IS_DISEQ (concl th)))
                   (map snd asl) in
  if ths = [] then failwith "SPDR10_PRUNE_TAC" else
  let th = ARITH_RULE (mk_neg (list_mk_conj (map concl ths))) in
  ACCEPT_TAC (CONTR w (MP (NOT_ELIM th) (end_itlist CONJ ths))) g;;

let SPDR10_LEAF_TAC : tactic = fun (asl,w as g) ->
  let ths = filter (fun th -> rfa_is_numrel (concl th)) (map snd asl) in
  let ths1 = filter (fun th -> not(SPDR10_IS_DISEQ (concl th))) ths in
  (POP_ASSUM_LIST(K ALL_TAC) THEN
   ((MAP_EVERY MP_TAC ths1 THEN ARITH_TAC) ORELSE (MAP_EVERY MP_TAC ths THEN ARITH_TAC))) g;;

(* The 3-cycle 1 -> i+2 -> 2 -> 1 of 1..k+2 (slot map of the Ricci action). *)

let RFA_RCACT_PERMUTES = prove
 (`!k i. 1 <= i /\ i <= k
         ==> (\m. if 1 <= m /\ m <= 2 then (if m = 2 then 1 else (\m:num. i) m + 2)
                  else if 2 < m /\ m <= 2 + k
                  then (if m - 2 = i then 2 else (\m:num. m)(m - 2) + 2)
                  else m) permutes 1..2 + k`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THENL
   [ALL_TAC; ALL_TAC;
    EXISTS_TAC `if x = 1 then 2 else if x = 2 then i + 2 else if x = i + 2 then 1 else x`] THEN
  REPEAT(SPDR10_ICOND_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
         TRY SPDR10_PRUNE_TAC) THEN
  SPDR10_LEAF_TAC);;

let RFA_GSUM_SWAP = prove
 (`!U (G:real^N->real^N^N) y (X:num->real) (Y:num->real).
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * X q * Y p)) =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b * X a * Y b))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y)$b$a = matrix_inv(G y)$a$b`
  SUBST1_TAC THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; REFL_TAC]);;

let RFA_LNABLA_RCACT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> lnabla k G (rfa_rcact k G tf) y u =
         rfa_rcact (k + 1) G (lnabla k G tf) y u -
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y (u(k + 1)) (basis q) *
           lnabla k G tf y (\m. if m = k + 1 then basis p else u m))) +
         sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q *
           lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then basis q
                                       else u(k + 1)) *
           tf y (\m. if m = i then basis p else u m))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfa_rcact k (G:real^N->real^N^N) tf =
    (\z w. sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
       matrix_inv(G z)$p$q * lricci G z (w i) (basis q) *
       (tf:real^N->(num->real^N)->real) z (\m. if m = i then basis p else w m)))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_rcact]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`;
    `\i z w. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
       matrix_inv((G:real^N->real^N^N) z)$p$q * lricci G z (w i) (basis q) *
       (tf:real^N->(num->real^N)->real) z (\m. if m = i then basis p else w m)))`;
    `y:real^N`; `u:num->real^N`; `k:num`] RFA_LNABLA_SUM1) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_SMOOTH_LIFT_MUL3 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `\m. if m = 1 then (u:num->real^N) i else basis q` o
      check (fun th -> is_forall(concl th))) THEN
    REWRITE_TAC[lric2; ARITH];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= k
        ==> lnabla k (G:real^N->real^N^N)
              (\z w. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                 matrix_inv(G z)$p$q * lricci G z (w i) (basis q) *
                 (tf:real^N->(num->real^N)->real) z (\m. if m = i then basis p else w m)))) y u =
            sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv(G y)$p$q * lricci G y (u i) (basis q) *
              lnabla k G tf y (\m. if m = i then basis p else u m))) +
            sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv(G y)$p$q *
              lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then basis q
                                          else u(k + 1)) *
              tf y (\m. if m = i then basis p else u m)))`
  (LABEL_TAC "term") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla k (G:real^N->real^N^N)
        (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G z)$a$b *
           lric2 G z (\m. if m = 2 then basis a else w((\m:num. i) m)) *
           (tf:real^N->(num->real^N)->real) z
             (\m. if m = i then basis b else w((\m:num. m) m))))) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
      DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[lric2; ARITH] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
        `\q. lricci (G:real^N->real^N^N) z ((w:num->real^N) i) (basis q)`;
        `\p. (tf:real^N->(num->real^N)->real) z
               (\m. if m = i then basis p else (w:num->real^N) m)`] RFA_GSUM_SWAP) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `k:num`; `k:num`; `2`; `i:num`; `\m:num. (i:num)`; `\m:num. m`;
                   `U:real^N->bool`; `G:real^N->real^N^N`; `lric2(G:real^N->real^N^N)`;
                   `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
           RFA_LNABLA_CPROD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `2 + k = k + 2`; ARITH] THEN
      MP_TAC(SPECL [`k:num`; `i:num`] RFA_RCACT_PERMUTES) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `2 + k = k + 2`];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `a = d /\ b = c ==> a + b = c + d:real`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
        `\q. lnabla 2 (G:real^N->real^N^N) (lric2 G) y
               (\m. if m = 1 then (u:num->real^N) i else if m = 2 then basis q else u(k + 1))`;
        `\p. (tf:real^N->(num->real^N)->real) y
               (\m. if m = i then basis p else (u:num->real^N) m)`] RFA_GSUM_SWAP) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2(G:real^N->real^N^N)`]
             LNABLA_TENSOR_FIELD) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`2 + 1`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
       [RFA_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
        `\q. lricci (G:real^N->real^N^N) y ((u:num->real^N) i) (basis q)`;
        `\p. lnabla k (G:real^N->real^N^N) tf y
               (\m. if m = i then basis p else (u:num->real^N) m)`] RFA_GSUM_SWAP) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[lric2; ARITH] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..k) (\i. lnabla k (G:real^N->real^N^N)
              (\z w. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                 matrix_inv(G z)$p$q * lricci G z (w i) (basis q) *
                 (tf:real^N->(num->real^N)->real) z (\m. if m = i then basis p else w m)))) y u) =
    sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv(G y)$p$q * lricci G y (u i) (basis q) *
              lnabla k G tf y (\m. if m = i then basis p else u m)))) +
    sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv(G y)$p$q *
              lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then basis q
                                          else u(k + 1)) *
              tf y (\m. if m = i then basis p else u m))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv((G:real^N->real^N^N) y)$p$q * lricci G y (u i) (basis q) *
              lnabla k G (tf:real^N->(num->real^N)->real) y
                (\m. if m = i then basis p else u m))) +
            sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
              matrix_inv(G y)$p$q *
              lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then basis q
                                          else u(k + 1)) *
              tf y (\m. if m = i then basis p else u m))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "term" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_ADD_NUMSEG]];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rcact; GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* nabla of the curvature action rfa_ract (the right side of the Ricci       *)
(* identity), by the contracted-product rule for each slot i.               *)
(* ========================================================================= *)

let RFA_RACT_CPROD_PERMUTES = prove
 (`!k i. 1 <= i /\ i <= k
         ==> (\m. if 1 <= m /\ m <= 4
                  then (if m = 3 then 1
                        else (\m. if m = 1 then k + 1 else if m = 2 then k + 2 else i) m + 2)
                  else if 4 < m /\ m <= 4 + k
                  then (if m - 4 = i then 2 else (\m:num. m)(m - 4) + 2)
                  else m) permutes 1..4 + k`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THENL
   [ALL_TAC; ALL_TAC;
    EXISTS_TAC `if x = 1 then 3 else if x = 2 then 4 + i else if x = k + 3 then 1
                else if x = k + 4 then 2 else if x = i + 2 then 4
                else if 3 <= x /\ x <= k + 2 then x + 2 else x`] THEN
  REPEAT(SPDR10_ICOND_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
         TRY SPDR10_PRUNE_TAC) THEN
  SPDR10_LEAF_TAC);;

let RFA_LNABLA_RACT = prove
 (`!k U (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) tf y w.
     metric_field U G /\ ltensor_field 4 U sf /\ ltensor_field k U tf /\
     (!u. smooth_map_on U (\x. lift(sf x u))) /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> lnabla (k + 2) G (rfa_ract k G sf tf) y w =
         sum(1..k) (\i. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           (lnabla 4 G sf y (\m. if m = 1 then w(k + 1) else if m = 2 then w(k + 2)
                                 else if m = 3 then basis a else if m = 4 then w i
                                 else w(k + 3)) *
            tf y (\m. if m = i then basis b else w m) +
            sf y (\m. if m = 1 then w(k + 1) else if m = 2 then w(k + 2)
                      else if m = 3 then basis a else w i) *
            lnabla k G tf y (\m. if m = i then basis b else if m = k + 1 then w(k + 3)
                                 else w m)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_ract k (G:real^N->real^N^N) sf tf =
    (\z w. sum(1..k) (\i. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G z)$a$b *
       (sf:real^N->(num->real^N)->real) z
         (\m. if m = 3 then basis a
              else w((\m. if m = 1 then k + 1 else if m = 2 then k + 2 else i) m)) *
       (tf:real^N->(num->real^N)->real) z
         (\m. if m = i then basis b else w((\m:num. m) m))))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_ract] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `v:num->real^N`] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `G:real^N->real^N^N`;
    `\i z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) z)$a$b *
       (sf:real^N->(num->real^N)->real) z
         (\m. if m = 3 then basis a
              else w((\m. if m = 1 then k + 1 else if m = 2 then k + 2 else i) m)) *
       (tf:real^N->(num->real^N)->real) z
         (\m. if m = i then basis b else w((\m:num. m) m))))`;
    `y:real^N`; `w:num->real^N`; `k:num`] RFA_LNABLA_SUM1) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_SMOOTH_LIFT_MUL3 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`4`; `k:num`; `k + 2`; `3`; `i:num`;
                 `\m. if m = 1 then k + 1 else if m = 2 then k + 2 else (i:num)`; `\m:num. m`;
                 `U:real^N->bool`; `G:real^N->real^N^N`; `sf:real^N->(num->real^N)->real`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `w:num->real^N`]
         RFA_LNABLA_CPROD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `i:num`] RFA_RACT_CPROD_PERMUTES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `sf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`4 + 1`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5` MP_TAC THENL
     [RFA_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `(k + 2) + 1 = k + 3`]];
    BINOP_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[ARITH];
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; ARITH_RULE `(k + 2) + 1 = k + 3`]]]);;


(* ========================================================================= *)
(* The exact commutator of nabla with the rough Laplacian.                   *)
(* ========================================================================= *)

(* Swapping the last two derivative slots of nabla^3 T: the Ricci identity   *)
(* for nabla T.                                                              *)

let RFA_D3_SWAP23 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u x1 x2 x3.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> lnabla_iter k 3 G tf y
           (\m. if m = k + 1 then x1 else if m = k + 2 then x2 else if m = k + 3 then x3
                else u m) -
         lnabla_iter k 3 G tf y
           (\m. if m = k + 1 then x1 else if m = k + 2 then x3 else if m = k + 3 then x2
                else u m) =
         rfa_ract (k + 1) G (lrm4 G) (lnabla k G tf) y
           (\m. if m = k + 1 then x1 else if m = k + 2 then x2 else if m = k + 3 then x3
                else u m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`;
                 `\m. if m = k + 1 then x1 else if m = k + 2 then x2
                      else if m = k + 3 then (x3:real^N) else u m`] RFA_RICCI_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`;
                 `\m. if m = k + 1 then x1 else if m = k + 2 then x2
                      else if m = k + 3 then (x3:real^N) else u m`] RFA_RACT_LRM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RFA_LNABLA_ITER_SHIFT; ARITH_RULE `2 + 1 = 3`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2 /\ (k + 1) + 2 = k + 3`] THEN
  REWRITE_TAC[ARITH_RULE `~(k + 3 = k + 1) /\ ~(k + 3 = k + 2) /\
                          ~(k + 2 = k + 1) /\ ~(k + 2 = k + 3)`] THEN
  ASM_CASES_TAC `m = k + 2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m = k + 3` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(k + 3 = k + 1) /\ ~(k + 3 = k + 2) /\
                              ~(k + 2 = k + 1) /\ ~(k + 2 = k + 3)`]);;

let RFA_LNABLA_ITER_3 = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     lnabla_iter k 3 G tf = lnabla (k + 2) G (lnabla_iter k 2 G tf)`,
  REWRITE_TAC[num_CONV `3`; lnabla_iter]);;

(* Swapping the first two derivative slots of nabla^3 T: nabla of the Ricci *)
(* identity for T.                                                           *)

let RFA_D3_SWAP12 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u x1 x2 x3.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> lnabla_iter k 3 G tf y
           (\m. if m = k + 1 then x1 else if m = k + 2 then x2 else if m = k + 3 then x3
                else u m) -
         lnabla_iter k 3 G tf y
           (\m. if m = k + 1 then x2 else if m = k + 2 then x1 else if m = k + 3 then x3
                else u m) =
         lnabla (k + 2) G (rfa_ract k G (lrm4 G) tf) y
           (\m. if m = k + 1 then x1 else if m = k + 2 then x2 else if m = k + 3 then x3
                else u m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `swap(k + 1,k + 2) permutes 1..k + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `V = \m. if m = k + 1 then x1 else if m = k + 2 then x2
                      else if m = k + 3 then (x3:real^N) else u m` THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y
      (\m. if m = k + 1 then x2 else if m = k + 2 then x1 else if m = k + 3 then x3
           else u m) =
    ltperm (swap(k + 1,k + 2)) (lnabla (k + 2) G (lnabla_iter k 2 G tf)) y V`
  SUBST1_TAC THENL
   [REWRITE_TAC[ltperm; RFA_LNABLA_ITER_3] THEN AP_TERM_TAC THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[FUN_EQ_THM; swap] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m = k + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1) /\ ~(k + 1 = k + 2)`] THEN
    ASM_CASES_TAC `m = k + 2` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1) /\ ~(k + 1 = k + 2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y V =
    lnabla (k + 2) G (lnabla_iter k 2 G tf) y V`
  SUBST1_TAC THENL [REWRITE_TAC[RFA_LNABLA_ITER_3]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP RFA_LNABLA_LTPERM th)]) THEN
  MP_TAC(ISPECL [`k + 2`; `G:real^N->real^N^N`;
                 `lnabla_iter k 2 (G:real^N->real^N^N) tf`;
                 `ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 (G:real^N->real^N^N) tf)`;
                 `y:real^N`; `V:num->real^N`] LRG_LNABLA_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[ltperm];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `z:real^N`; `w:num->real^N`]
         RFA_RICCI_IDENTITY) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `z:real^N`; `w:num->real^N`]
         RFA_RACT_LRM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ltperm] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; swap] THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `m = k + 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m = k + 2` THEN ASM_REWRITE_TAC[]);;

let RFA_LTLAP_COMMUTE_EXACT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> lnabla k G (ltlap k G tf) y u =
         ltlap (k + 1) G (lnabla k G tf) y u +
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           (rfa_ract (k + 1) G (lrm4 G) (lnabla k G tf) y
              (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                   else if m = k + 3 then u(k + 1) else u m) +
            lnabla (k + 2) G (rfa_ract k G (lrm4 G) tf) y
              (\m. if m = k + 1 then basis a else if m = k + 2 then u(k + 1)
                   else if m = k + 3 then basis b else u m))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_LNABLA_LTLAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_LTLAP_LNABLA] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`;
                 `basis a:real^N`; `basis b:real^N`; `(u:num->real^N)(k + 1)`]
         RFA_D3_SWAP23) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`;
                 `basis a:real^N`; `(u:num->real^N)(k + 1)`; `basis b:real^N`]
         RFA_D3_SWAP12) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 2) (basis a) (basis b) u) =
    lnabla_iter k 3 G tf y
      (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
           else if m = k + 3 then u(k + 1) else u m) /\
    lnabla_iter k 3 G tf y
      (\m. if m = k + 2 then basis a else if m = k + 3 then basis b else u m) =
    lnabla_iter k 3 G tf y
      (\m. if m = k + 1 then u(k + 1) else if m = k + 2 then basis a
           else if m = k + 3 then basis b else u m)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`k + 3`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
    TRY(AP_TERM_TAC THEN RFA_ARITH_TAC) THEN TRY RFA_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The heat defect of nabla T (rule R5).                                     *)
(* ========================================================================= *)

(* Small tactics: pointwise comparison of finite sums, and tuple agreement  *)
(* by case analysis on the slot index.                                      *)

let RFA_SUM_EQ_TAC v =
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC v THEN STRIP_TAC THEN BETA_TAC;;

let RFA_HC_TUPLE_TAC =
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN RFA_ARITH_TAC;;

(* Sum manipulations used below.                                            *)

let RFA_SUM2_FACTOR = prove
 (`!n (g:num->num->real) (f:num->num->real) c d.
     sum(1..n) (\a. sum(1..n) (\b. g a b * (c * f a b * d))) =
     c * sum(1..n) (\a. sum(1..n) (\b. g a b * f a b)) * d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN REAL_ARITH_TAC);;

let RFA_SUM22_SWAP_FACTOR = prove
 (`!n (g:num->num->real) (h:num->num->real) (Fn:num->num->num->real) (X:num->real).
     sum(1..n) (\a. sum(1..n) (\b. g a b *
       sum(1..n) (\p. sum(1..n) (\q. h p q * Fn a b p * X q)))) =
     sum(1..n) (\p. sum(1..n) (\q. h p q *
       sum(1..n) (\a. sum(1..n) (\b. g a b * Fn a b p)) * X q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [RFA_SUM4_PAIRSWAP] THEN
  RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN
  RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN REAL_ARITH_TAC);;

let RFA_SUM3_ADD = prove
 (`!k n (f:num->num->num->real) g.
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. f i p q))) +
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. g i p q))) =
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. f i p q + g i p q)))`,
  REWRITE_TAC[SUM_ADD_NUMSEG]);;

let RFA_SUM3_LIN = prove
 (`!k n (f:num->num->num->real) g h.
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. f i p q))) +
     (sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. g i p q))) -
      sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. h i p q)))) =
     sum(1..k) (\i. sum(1..n) (\p. sum(1..n) (\q. f i p q + (g i p q - h i p q))))`,
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG]);;

(* The trace of Rm over its slots 1 and 4 is minus the Ricci tensor.        *)

let RFA_RM_TRACE14 = prove
 (`!U (G:real^N->real^N^N) y c p.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           lrm4 G y (\m. if m = 1 then basis b else if m = 2 then c
                         else if m = 3 then p else basis a))) =
         --(lricci G y c p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. lrm4 (G:real^N->real^N^N) y
            (\m. if m = 1 then basis b else if m = 2 then c
                 else if m = 3 then p else basis a) =
          --(lrm4 G y (\m. if m = 1 then basis b else if m = 2 then c
                           else if m = 3 then basis a else p))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lrm4] THEN BETA_TAC THEN REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC LRG_RM_ANTISYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_EQ_NEG2] THEN
  MP_TAC(ISPECL [`\a b. matrix_inv((G:real^N->real^N^N) y)$a$b`;
                 `\a b. lrm4 (G:real^N->real^N^N) y
                          (\m. if m = 1 then basis a else if m = 2 then c
                               else if m = 3 then basis b else p)`;
                 `dimindex(:N)`] RFA_SUM_SWAP_SYM) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC LRG_LRM4_CONTRACT13 THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The divergence of nabla Rm over slot 1 (Bianchi II, contracted).         *)

let RFA_DIVRM_FIRST = prove
 (`!U (G:real^N->real^N^N) y c p x.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           lnabla 4 G (lrm4 G) y (\m. if m = 1 then basis a else if m = 2 then c
                                    else if m = 3 then p else if m = 4 then x
                                    else basis b))) =
         lnabla 2 G (lric2 G) y (\m. if m = 1 then x else if m = 2 then c else p) -
         lnabla 2 G (lric2 G) y (\m. if m = 1 then p else if m = 2 then c else x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. lnabla 4 (G:real^N->real^N^N) (lrm4 G) y
            (\m. if m = 1 then basis a else if m = 2 then c else if m = 3 then p
                 else if m = 4 then x else basis b) =
          --(lnabla 4 G (lrm4 G) y
               (\m. if m = 1 then p else if m = 2 then x else if m = 3 then c
                    else if m = 4 then basis a else basis b))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis a:real^N`; `c:real^N`; `p:real^N`; `x:real^N`;
                   `basis b:real^N`] LRG_LNABLA_LRM4_PAIR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RFA_N5_ANTI34_T THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `p:real^N`; `x:real^N`; `c:real^N`] RFA_LRM4_DIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Values of the two slot permutations of nabla Ric appearing in the time  *)
(* derivative of the Christoffel symbols.                                  *)

let RFA_N2_PERM13_VAL = prove
 (`!U (G:real^N->real^N^N) y x v w.
     metric_field U G /\ y IN U
     ==> ltperm (swap(1,3)) (lnabla 2 G (lric2 G)) y
           (\m. if m = 1 then x else if m = 2 then v else w) =
         lnabla 2 G (lric2 G) y (\m. if m = 1 then v else if m = 2 then w else x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\m. if m = 1 then v else if m = 2 then w else x:real^N`]
         LRG_N2_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ltperm] THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[swap; ARITH]);;

let RFA_N2_PERM312_VAL = prove
 (`!U (G:real^N->real^N^N) y x v w.
     metric_field U G /\ y IN U
     ==> ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m)
           (lnabla 2 G (lric2 G)) y
           (\m. if m = 1 then x else if m = 2 then v else w) =
         lnabla 2 G (lric2 G) y (\m. if m = 1 then x else if m = 2 then w else v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\m. if m = 1 then x else if m = 2 then w else v:real^N`]
         LRG_N2_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ltperm] THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[swap; ARITH]);;

(* The nabla Ric term of nabla(Rc.T) is the first Christoffel-derivative   *)
(* action term.                                                             *)

let RFA_NRIC_GACT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ y IN U
     ==> sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q *
           lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then basis q
                                       else u(k + 1)) *
           tf y (\m. if m = i then basis p else u m)))) =
         rfa_gact k G (lnabla 2 G (lric2 G)) tf y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_gact] THEN
  RFA_SUM_EQ_TAC `i:num` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\q. lnabla 2 (G:real^N->real^N^N) (lric2 G) y
                        (\m. if m = 1 then (u:num->real^N) i else if m = 2 then basis q
                             else u(k + 1))`;
                 `\p. (tf:real^N->(num->real^N)->real) y
                        (\m. if m = i then basis p else (u:num->real^N) m)`]
         RFA_GSUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* The first commutator part: the curvature action on nabla T, traced; its *)
(* term on the derivative slot is minus the Ricci slot term.               *)

let RFA_COMM_PART1 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           rfa_ract (k + 1) G (lrm4 G) (lnabla k G tf) y
             (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                  else if m = k + 3 then u(k + 1) else u m))) =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis b else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else u i) *
             lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis a
                                  else u m)))))) -
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y (u(k + 1)) (basis q) *
           lnabla k G tf y (\m. if m = k + 1 then basis p else u m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field (k + 1) U (lnabla k (G:real^N->real^N^N) tf)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LNABLA_TENSOR_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. rfa_ract (k + 1) (G:real^N->real^N^N) (lrm4 G) (lnabla k G tf) y
            (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                 else if m = k + 3 then u(k + 1) else u m) =
          sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis b else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else u i) *
             lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis a
                                  else u m)))) +
          sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis b else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else basis a) *
             lnabla k G tf y (\m. if m = k + 1 then basis q else u m)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[rfa_ract] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2 /\ (k + 1) + 2 = k + 3`] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
    REWRITE_TAC[ADD1] THEN BETA_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1) /\ ~(k + 3 = k + 1) /\ ~(k + 3 = k + 2)`] THEN
    BINOP_TAC THENL
     [RFA_SUM_EQ_TAC `i:num` THEN
      SUBGOAL_THEN `~(i = k + 1) /\ ~(i = k + 2) /\ ~(i = k + 3)` STRIP_ASSUME_TAC THENL
       [RFA_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN RFA_HC_TUPLE_TAC;
      RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN RFA_HC_TUPLE_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `y = --s ==> x + y = x - s:real`) THEN
  MP_TAC(ISPECL [`dimindex(:N)`;
                 `\a b. matrix_inv((G:real^N->real^N^N) y)$a$b`;
                 `\p q. matrix_inv((G:real^N->real^N^N) y)$p$q`;
                 `\a b p. lrm4 (G:real^N->real^N^N) y
                    (\m. if m = 1 then basis b else if m = 2 then (u:num->real^N)(k + 1)
                         else if m = 3 then basis p else basis a)`;
                 `\q. lnabla k (G:real^N->real^N^N) tf y
                        (\m. if m = k + 1 then basis q else (u:num->real^N) m)`]
         RFA_SUM22_SWAP_FACTOR) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_RM_TRACE14) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\q. lricci (G:real^N->real^N^N) y ((u:num->real^N)(k + 1)) (basis q)`;
                 `\p. lnabla k (G:real^N->real^N^N) tf y
                        (\m. if m = k + 1 then basis p else (u:num->real^N) m)`]
         RFA_GSUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; SUM_NEG]);;

(* The second commutator part: nabla of the curvature action on T, traced: *)
(* the Rm.nabla T half and the divergence of Rm acting on T.             *)

let RFA_COMM_PART2 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           lnabla (k + 2) G (rfa_ract k G (lrm4 G) tf) y
             (\m. if m = k + 1 then basis a else if m = k + 2 then u(k + 1)
                  else if m = k + 3 then basis b else u m))) =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis a else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else u i) *
             lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis b
                                  else u m)))))) +
         sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q *
           (lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then u(k + 1)
                                       else basis p) -
            lnabla 2 G (lric2 G) y (\m. if m = 1 then basis p else if m = 2 then u(k + 1)
                                       else u i)) *
           tf y (\m. if m = i then basis q else u m))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field (k + 1) U (lnabla k (G:real^N->real^N^N) tf)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LNABLA_TENSOR_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. lnabla (k + 2) (G:real^N->real^N^N) (rfa_ract k G (lrm4 G) tf) y
            (\m. if m = k + 1 then basis a else if m = k + 2 then u(k + 1)
                 else if m = k + 3 then basis b else u m) =
          sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis a else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else u i) *
             lnabla k G tf y (\m. if m = i then basis q else if m = k + 1 then basis b
                                  else u m)))) +
          sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$p$q *
             lnabla 4 G (lrm4 G) y (\m. if m = 1 then basis a else if m = 2 then u(k + 1)
                           else if m = 3 then basis p else if m = 4 then u i else basis b) *
             tf y (\m. if m = i then basis q else u m))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`; `tf:real^N->(num->real^N)->real`;
                   `y:real^N`;
                   `\m. if m = k + 1 then basis a else if m = k + 2 then (u:num->real^N)(k + 1)
                        else if m = k + 3 then basis b else u m`] RFA_LNABLA_RACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RFA_SUM3_ADD] THEN BETA_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1) /\ ~(k + 3 = k + 1) /\ ~(k + 3 = k + 2)`] THEN
    RFA_SUM_EQ_TAC `i:num` THEN
    SUBGOAL_THEN `~(i = k + 1) /\ ~(i = k + 2) /\ ~(i = k + 3)` STRIP_ASSUME_TAC THENL
     [RFA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
    MATCH_MP_TAC(prove
     (`!g n t1 t1' r t2 t2'.
         t1 = t1' /\ t2 = t2' ==> g * (n * t1 + r * t2) = g * r * t2' + g * n * t1':real`,
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
    CONJ_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THENL
     [MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`]] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN RFA_HC_TUPLE_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [RFA_SUM5_SHIFT] THEN
  RFA_SUM_EQ_TAC `i:num` THEN RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN
  REWRITE_TAC[RFA_SUM2_FACTOR] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N)(k + 1)`; `basis p:real^N`; `(u:num->real^N) i`]
         RFA_DIVRM_FIRST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* The divergence term cancels the remaining Christoffel-derivative terms. *)

let RFA_COMM_DIVTERM = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ y IN U
     ==> sum(1..k) (\i. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q *
           (lnabla 2 G (lric2 G) y (\m. if m = 1 then u i else if m = 2 then u(k + 1)
                                       else basis p) -
            lnabla 2 G (lric2 G) y (\m. if m = 1 then basis p else if m = 2 then u(k + 1)
                                       else u i)) *
           tf y (\m. if m = i then basis q else u m)))) +
         (rfa_gact k G (ltperm (swap(1,3)) (lnabla 2 G (lric2 G))) tf y u -
          rfa_gact k G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                                    else if m = 3 then 2 else m)
                               (lnabla 2 G (lric2 G))) tf y u) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_gact; RFA_SUM3_LIN] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_N2_PERM13_VAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_N2_PERM312_VAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(* Assembly of the commutator identity.                                     *)

let RFA_COMM_IDENT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           (rfa_ract (k + 1) G (lrm4 G) (lnabla k G tf) y
              (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                   else if m = k + 3 then u(k + 1) else u m) +
            lnabla (k + 2) G (rfa_ract k G (lrm4 G) tf) y
              (\m. if m = k + 1 then basis a else if m = k + 2 then u(k + 1)
                   else if m = k + 3 then basis b else u m)))) +
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y (u(k + 1)) (basis q) *
           lnabla k G tf y (\m. if m = k + 1 then basis p else u m))) +
         (rfa_gact k G (ltperm (swap(1,3)) (lnabla 2 G (lric2 G))) tf y u -
          rfa_gact k G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                                    else if m = 3 then 2 else m)
                               (lnabla 2 G (lric2 G))) tf y u) =
         rfa_rmcomm k G tf y u`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_COMM_PART1) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_COMM_PART2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_COMM_DIVTERM) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `h1 + h2 = r ==> d + g = &0 ==> ((h1 - s) + (h2 + d)) + s + g = r:real`) THEN
  REWRITE_TAC[rfa_rmcomm; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG]);;

(* Linearity helpers for the tensor-field property of rfa_rmcomm.           *)

let RFA_TF_LINEAR_SLOT = prove
 (`!k U (tf:real^N->(num->real^N)->real) y j (W:real^N->num->real^N).
     ltensor_field k U tf /\ y IN U /\ 1 <= j /\ j <= k /\
     (!v m. 1 <= m /\ m <= k /\ ~(m = j) ==> W v m = W (vec 0) m) /\
     (!v. W v j = v)
     ==> linear (\v. lift(tf y (\m. W v m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!u u'. (!m. 1 <= m /\ m <= k ==> u m = u' m)
            ==> (tf:real^N->(num->real^N)->real) y u = tf y u') /\
    (!i u. 1 <= i /\ i <= k
           ==> linear (\v. lift(tf y (\j. if j = i then v else u j))))`
  MP_TAC THENL
   [UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (LABEL_TAC "li")) THEN
  SUBGOAL_THEN
   `(\v. lift((tf:real^N->(num->real^N)->real) y (\m. W v m))) =
    (\v. lift(tf y (\m. if m = j then v else W (vec 0) m)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN AP_TERM_TAC THEN
    USE_THEN "ag" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "li" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFA_LINEAR_LIFT_MUL_L = prove
 (`!(f:real^N->real) g.
     linear (\v. lift(f v)) /\ (!v. g v = g (vec 0))
     ==> linear (\v. lift(f v * g v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\v. lift((f:real^N->real) v * g v)) = (\v. g (vec 0) % lift(f v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SPEC `v:real^N`) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL];
    MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[]]);;

let RFA_LINEAR_LIFT_MUL_R = prove
 (`!(f:real^N->real) g.
     (!v. f v = f (vec 0)) /\ linear (\v. lift(g v))
     ==> linear (\v. lift(f v * g v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\v. lift((f:real^N->real) v * g v)) = (\v. f (vec 0) % lift(g v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SPEC `v:real^N`) THEN REWRITE_TAC[LIFT_CMUL];
    MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[]]);;

(* One summand of rfa_rmcomm is linear in the slot j: case analysis on     *)
(* whether j is the derivative slot k+1, the slot i acted on, or neither.  *)

let RFA_RMCOMM_LIN_TAC =
  ASM_CASES_TAC `j = k + 1` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(i = k + 1)` ASSUME_TAC THENL [RFA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LINEAR_LIFT_MUL_L THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`4`; `U:real^N->bool`; `lrm4 (G:real^N->real^N^N)`;
                            `y:real^N`] RFA_TF_LINEAR_SLOT) THEN
      EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      RFA_HC_TUPLE_TAC;
      GEN_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
      MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN RFA_HC_TUPLE_TAC];
    SUBGOAL_THEN `~(k + 1 = j) /\ j <= k` STRIP_ASSUME_TAC THENL
     [RFA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = j` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_LINEAR_LIFT_MUL_L THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`4`; `U:real^N->bool`; `lrm4 (G:real^N->real^N^N)`;
                              `y:real^N`] RFA_TF_LINEAR_SLOT) THEN
        EXISTS_TAC `4` THEN
        ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        RFA_HC_TUPLE_TAC;
        GEN_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
        MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN RFA_HC_TUPLE_TAC];
      SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_LINEAR_LIFT_MUL_R THEN CONJ_TAC THENL
       [BETA_TAC THEN REWRITE_TAC[];
        MATCH_MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                             `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`]
                     RFA_TF_LINEAR_SLOT) THEN
        EXISTS_TAC `j:num` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        RFA_HC_TUPLE_TAC]]];;

let RFA_RMCOMM_FIELD = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field (k + 1) U (rfa_rmcomm k G tf) /\
         (!u. smooth_map_on U (\y. lift(rfa_rmcomm k G tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nf") (LABEL_TAC "ns")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (LABEL_TAC "rs")) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfa_rmcomm] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_SIMP_TAC[RFA_GINV_ENTRY_SMOOTH] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_SIMP_TAC[RFA_GINV_ENTRY_SMOOTH] THEN
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u u'. (!m. 1 <= m /\ m <= k + 1 ==> u m = u' m)
           ==> lnabla k (G:real^N->real^N^N) tf y u = lnabla k G tf y u'`
  (LABEL_TAC "nag") THENL
   [UNDISCH_TAC `ltensor_field (k + 1) U (lnabla k (G:real^N->real^N^N) tf)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->real^N`; `u':num->real^N`] THEN
    DISCH_THEN(LABEL_TAC "uu") THEN REWRITE_TAC[rfa_rmcomm] THEN
    SUBGOAL_THEN `(u:num->real^N)(k + 1) = u'(k + 1)` SUBST1_TAC THENL
     [USE_THEN "uu" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    RFA_SUM_EQ_TAC `a:num` THEN RFA_SUM_EQ_TAC `b:num` THEN AP_TERM_TAC THEN
    RFA_SUM_EQ_TAC `i:num` THEN
    SUBGOAL_THEN `(u:num->real^N) i = u' i` SUBST1_TAC THENL
     [USE_THEN "uu" MATCH_MP_TAC THEN RFA_ARITH_TAC; ALL_TAC] THEN
    RFA_SUM_EQ_TAC `p:num` THEN RFA_SUM_EQ_TAC `q:num` THEN AP_TERM_TAC THEN
    BINOP_TAC THEN AP_TERM_TAC THEN USE_THEN "nag" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    USE_THEN "uu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmcomm] THEN BETA_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
  CONJ_TAC THEN RFA_RMCOMM_LIN_TAC);;

(* The pointwise identity behind rule R5 (one metric G): nabla of the heat  *)
(* operator applied to T, plus the Christoffel-derivative terms, is the     *)
(* heat operator applied to nabla T plus nabla H plus the commutator term.  *)

let RFA_HEAT_LNABLA_ALG = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) hf y u.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\
     ltensor_field k U hf /\ (!u. smooth_map_on U (\x. lift(hf x u))) /\ y IN U
     ==> lnabla k G (\z w. ltlap k G tf z w - rfa_rcact k G tf z w + hf z w) y u -
         --(rfa_gact k G (lnabla 2 G (lric2 G)) tf y u +
            (rfa_gact k G (ltperm (swap(1,3)) (lnabla 2 G (lric2 G))) tf y u -
             rfa_gact k G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                                       else if m = 3 then 2 else m)
                                  (lnabla 2 G (lric2 G))) tf y u)) =
         ltlap (k + 1) G (lnabla k G tf) y u - rfa_rcact (k + 1) G (lnabla k G tf) y u +
         (lnabla k G hf y u + rfa_rmcomm k G tf y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] RFA_LTLAP_FIELD) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] RFA_RCACT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lnabla k (G:real^N->real^N^N)
      (\z w. ltlap k G tf z w - rfa_rcact k G tf z w + hf z w) y u =
    lnabla k G (ltlap k G tf) y u - lnabla k G (rfa_rcact k G tf) y u +
    lnabla k G hf y u`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`;
                   `\z w. ltlap k (G:real^N->real^N^N) tf z w - rfa_rcact k G tf z w`;
                   `hf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
          LRG_LNABLA_ADD) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LIFT_SUB] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`; `ltlap k (G:real^N->real^N^N) tf`;
                   `rfa_rcact k (G:real^N->real^N^N) tf`; `y:real^N`; `u:num->real^N`]
          LRG_LNABLA_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_COMM_IDENT) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_NRIC_GACT) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_LNABLA_RCACT) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_LTLAP_COMMUTE_EXACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

(* Rule R5: if T solves the heat equation with defect H, then nabla T     *)
(* solves it with defect nabla H + rfa_rmcomm (the 2 Rm.nabla T term).   *)

let RFA_HEAT_LNABLA = prove
 (`!k U a b (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real) Hf.
     lricci_flow U a b G /\ rfa_heat k U a b G Tf Hf
     ==> rfa_heat (k + 1) U a b G (\t. lnabla k (G t) (Tf t))
           (\t y u. lnabla k (G t) (Hf t) y u + rfa_rmcomm k (G t) (Tf t) y u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ASSUME `rfa_heat k U a b (G:real->real^N->real^N^N)
                   (Tf:real->real^N->(num->real^N)->real) Hf`) THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "js") (LABEL_TAC "dt"))) THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> metric_field U ((G:real->real^N->real^N^N) t) /\
            ltensor_field k U ((Tf:real->real^N->(num->real^N)->real) t) /\
            (!u. smooth_map_on U (\y. lift(Tf t y u))) /\
            ltensor_field k U ((Hf:real->real^N->(num->real^N)->real) t) /\
            (!u. smooth_map_on U (\y. lift(Hf t y u)))`
  (LABEL_TAC "at") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`; `Tf:real->real^N->(num->real^N)->real`;
                   `Hf:real->real^N->(num->real^N)->real`; `t:real`] RFA_HEAT_SLICE) THEN
    USE_THEN "fl" (MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_heat] THEN BETA_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "at" (fun th -> STRIP_ASSUME_TAC
    (MP (SPEC `t:real` th) (CONJ (ASSUME `a < t:real`) (ASSUME `t < b:real`)))) THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(Tf:real->real^N->(num->real^N)->real) t`] LNABLA_TENSOR_FIELD) THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(Hf:real->real^N->(num->real^N)->real) t`] LNABLA_TENSOR_FIELD) THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(Tf:real->real^N->(num->real^N)->real) t`] RFA_RMCOMM_FIELD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LSMOOTH_LNABLA THEN ASM_SIMP_TAC[RFA_LRICCI_FLOW_LSMOOTH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "at" (fun th -> STRIP_ASSUME_TAC
    (MP (SPEC `t:real` th) (CONJ (ASSUME `a < t:real`) (ASSUME `t < b:real`)))) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`] RFA_LTLAP_FIELD) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`] RFA_RCACT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `Tf:real->real^N->(num->real^N)->real`;
                 `\z w. ltlap k ((G:real->real^N->real^N^N) t)
                          ((Tf:real->real^N->(num->real^N)->real) t) z w -
                        rfa_rcact k (G t) (Tf t) z w +
                        (Hf:real->real^N->(num->real^N)->real) t z w`;
                 `t:real`; `y:real^N`; `u:num->real^N`] RFA_LNABLA_DT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "at" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN DISCH_TAC THEN
      USE_THEN "dt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `(Tf:real->real^N->(num->real^N)->real) t`;
                 `t:real`; `y:real^N`; `u:num->real^N`] RFA_LDGAMMA_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `(Tf:real->real^N->(num->real^N)->real) t`;
                 `(Hf:real->real^N->(num->real^N)->real) t`; `y:real^N`; `u:num->real^N`]
         RFA_HEAT_LNABLA_ALG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC);;

