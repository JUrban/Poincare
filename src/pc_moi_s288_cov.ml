(* ========================================================================= *)
(* pc_moi_s288_cov: Moise 28.8 in the used form, by the PL covering of the   *)
(* torus model.  Main theorem MOISE_288 : |- MOISE_288_STATEMENT             *)
(* (pc_moi_core_stmt.ml).  Route: members of the family that are essential   *)
(* in frontier s carry H_1(s) (pc_moi_s34_torus: loops missing an essential  *)
(* circle are homotopic to loops in it); members inessential in frontier s   *)
(* bound PL 2-cells: transport to the PL torus model (PL_SOLID_TORUS_BASIC), *)
(* lift through the PL covering moi_s8c_q : real^2 -> pl_torus_model         *)
(* (8-periodic, affine on grid squares, a rescaling of the covering of       *)
(* pc_moi_s34_torus), PL Schoenflies in the plane (PL_SCHOENFLIES_2) and     *)
(* disjointness of lattice translates of the lifted disk.                    *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_s34_torus.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_fnd_plst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The 8-periodic unit-speed map sigma of the real line onto the            *)
(* boundary of the square [-1,1]^2, affine on each [2a-1,2a+1].              *)
(* ------------------------------------------------------------------------- *)

let moi_s8c_sig0 = new_definition
 `moi_s8c_sig0 (u:real) =
    if u <= &1 then vector[&1; u]:real^2
    else if u <= &3 then vector[&2 - u; &1]
    else if u <= &5 then vector[-- &1; &4 - u]
    else vector[u - &6; -- &1]`;;

let moi_s8c_sig = new_definition
 `moi_s8c_sig (t:real) = moi_s8c_sig0 (t - &8 * floor((t + &1) / &8))`;;

let MOI_S8C_FLOOR_ADD = prove
 (`!x n. integer n ==> floor(x + n) = floor x + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let MOI_S8C_SIG_PERIODIC = prove
 (`!t n. integer n ==> moi_s8c_sig (t + &8 * n) = moi_s8c_sig t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s8c_sig] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `((t + &8 * n) + &1) / &8 = (t + &1) / &8 + n` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_SIMP_TAC[MOI_S8C_FLOOR_ADD]] THEN
  REAL_ARITH_TAC);;

let MOI_S8C_SIG_BASE = prove
 (`!t. -- &1 <= t /\ t <= &7 ==> moi_s8c_sig t = moi_s8c_sig0 t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &7` THENL
   [ASM_REWRITE_TAC[moi_s8c_sig] THEN
    SUBGOAL_THEN `floor((&7 + &1) / &8) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s8c_sig0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s8c_sig] THEN
    SUBGOAL_THEN `floor((t + &1) / &8) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[FLOOR_EQ_0] THEN
      MAP_EVERY UNDISCH_TAC [`-- &1 <= t`; `t <= &7`; `~(t = &7)`] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO]]]);;

(* The four affine pieces. *)

let MOI_S8C_SIG_PIECES = prove
 (`!m t. integer m
         ==> (-- &1 <= t - &8 * m /\ t - &8 * m <= &1
              ==> moi_s8c_sig t = vector[&1; t - &8 * m]) /\
             (&1 <= t - &8 * m /\ t - &8 * m <= &3
              ==> moi_s8c_sig t = vector[&2 - (t - &8 * m); &1]) /\
             (&3 <= t - &8 * m /\ t - &8 * m <= &5
              ==> moi_s8c_sig t = vector[-- &1; &4 - (t - &8 * m)]) /\
             (&5 <= t - &8 * m /\ t - &8 * m <= &7
              ==> moi_s8c_sig t = vector[(t - &8 * m) - &6; -- &1])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s8c_sig t = moi_s8c_sig (t - &8 * m)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`t - &8 * m`; `m:real`] MOI_S8C_SIG_PERIODIC) THEN
    ASM_REWRITE_TAC[REAL_ARITH `(t - &8 * m) + &8 * m = t`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = t - &8 * m` THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `moi_s8c_sig u = moi_s8c_sig0 u` SUBST1_TAC THENL
    [MATCH_MP_TAC MOI_S8C_SIG_BASE THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[moi_s8c_sig0] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S8C_SQ = prove
 (`!y:real^2.
     y IN relative_frontier(interval[--vec 1,vec 1]) <=>
     abs(y$1) <= &1 /\ abs(y$2) <= &1 /\ (abs(y$1) = &1 \/ abs(y$2) = &1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `~(interior(interval[--vec 1:real^2,vec 1]) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S8C_SIG_IN = prove
 (`!t. moi_s8c_sig t IN relative_frontier(interval[--vec 1:real^2,vec 1])`,
  GEN_TAC THEN REWRITE_TAC[MOI_S8C_SQ] THEN
  MP_TAC(SPEC `(t + &1) / &8` FLOOR) THEN
  ABBREV_TAC `m = floor((t + &1) / &8)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s8c_sig t = moi_s8c_sig0 (t - &8 * m)` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s8c_sig] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s8c_sig0] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[VECTOR_2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S8C_SIG_ONTO = prove
 (`!y:real^2.
     y IN relative_frontier(interval[--vec 1,vec 1])
     ==> ?t. -- &1 <= t /\ t <= &7 /\ moi_s8c_sig t = y`,
  GEN_TAC THEN REWRITE_TAC[MOI_S8C_SQ] THEN STRIP_TAC THENL
   [ALL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
    `abs x = &1 ==> x = &1 \/ x = -- &1`)) THENL
   [EXISTS_TAC `(y:real^2)$2`;
    EXISTS_TAC `&4 - (y:real^2)$2`;
    EXISTS_TAC `&2 - (y:real^2)$1`;
    EXISTS_TAC `&6 + (y:real^2)$1`] THEN
  (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_S8C_SIG_BASE o lhand o snd) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[moi_s8c_sig0] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let moi_s8c_psi = new_definition
 `moi_s8c_psi (y:real^2) =
    if y$1 = &1 then moi_s4u_ex (y$2 / &8)
    else if y$2 = &1 then moi_s4u_ex ((&2 - y$1) / &8)
    else if y$1 = -- &1 then moi_s4u_ex ((&4 - y$2) / &8)
    else moi_s4u_ex ((&6 + y$1) / &8)`;;

let MOI_S8C_PSI_SIG0 = prove
 (`!u. -- &1 <= u /\ u < &7 ==> moi_s8c_psi (moi_s8c_sig0 u) = moi_s4u_ex (u / &8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s8c_sig0] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[moi_s8c_psi; VECTOR_2] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_REAL_ARITH_TAC) THEN ASM_REAL_ARITH_TAC);;

let MOI_S8C_PSI_SIG = prove
 (`!t. moi_s8c_psi (moi_s8c_sig t) = moi_s4u_ex (t / &8)`,
  GEN_TAC THEN MP_TAC(SPEC `(t + &1) / &8` FLOOR) THEN
  ABBREV_TAC `m = floor((t + &1) / &8)` THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s8c_sig] THEN ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_S8C_PSI_SIG0 o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_S4U_EX_EQ] THEN
  SUBGOAL_THEN `(t - &8 * m) / &8 - t / &8 = --m` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[INTEGER_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of psi, psi a homeomorphism of the square boundary onto the    *)
(* unit circle, the covering Q and its factorization through the covering of *)
(* pc_moi_s34_torus: bpsi o Q = moi_s4u_tor o (1/8) scaling; lifting loops.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S8C_EX_CONTINUOUS = prove
 (`!(f:real^N->real) s. (lift o f) continuous_on s
                        ==> (\x. moi_s4u_ex (f x)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4u_ex] THEN
  SUBGOAL_THEN `(\x:real^N. cexp(ii * Cx(&2 * pi * f x))) =
                cexp o (\x. ii * Cx(&2 * pi) * Cx(f x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; CX_MUL; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
  REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN REWRITE_TAC[GSYM o_DEF] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let MOI_S8C_EX_AFFINE_CONTINUOUS = prove
 (`!a b i s. 1 <= i /\ i <= 2
             ==> (\y:real^2. moi_s4u_ex ((a + b * y$i) / &8)) continuous_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S8C_EX_CONTINUOUS THEN
  SUBGOAL_THEN `lift o (\y:real^2. (a + b * y$i) / &8) =
                (\y. lift(a / &8) + (b / &8) % lift(y$i))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
  ASM_REWRITE_TAC[DIMINDEX_2]);;

let MOI_S8C_PSI_CONTINUOUS = prove
 (`moi_s8c_psi continuous_on relative_frontier(interval[--vec 1:real^2,vec 1])`,
  SUBGOAL_THEN
   `relative_frontier(interval[--vec 1:real^2,vec 1]) =
    (relative_frontier(interval[--vec 1:real^2,vec 1]) INTER {y | y$1 = &1}) UNION
    (relative_frontier(interval[--vec 1:real^2,vec 1]) INTER {y | y$2 = &1}) UNION
    (relative_frontier(interval[--vec 1:real^2,vec 1]) INTER {y | y$1 = -- &1}) UNION
    (relative_frontier(interval[--vec 1:real^2,vec 1]) INTER {y | y$2 = -- &1})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; MOI_S8C_SQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i a. closed(relative_frontier(interval[--vec 1:real^2,vec 1]) INTER
                             {y:real^2 | y$i = a})` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN
    REWRITE_TAC[CLOSED_RELATIVE_FRONTIER; CLOSED_STANDARD_HYPERPLANE];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_UNION THEN ASM_REWRITE_TAC[] THEN
         ASM_SIMP_TAC[CLOSED_UNION] THEN CONJ_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `\y:real^2. moi_s4u_ex ((&0 + &1 * y$2) / &8)`;
    EXISTS_TAC `\y:real^2. moi_s4u_ex ((&2 + -- &1 * y$1) / &8)`;
    EXISTS_TAC `\y:real^2. moi_s4u_ex ((&4 + -- &1 * y$2) / &8)`;
    EXISTS_TAC `\y:real^2. moi_s4u_ex ((&6 + &1 * y$1) / &8)`] THEN
  SIMP_TAC[MOI_S8C_EX_AFFINE_CONTINUOUS; ARITH] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_S8C_SQ; moi_s8c_psi] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[MOI_S4U_EX_EQ] THEN
  FIRST(map (fun c -> MATCH_MP_TAC(MESON[INTEGER_CLOSED; INTEGER_NEG]
                        (mk_imp(mk_eq(`x:real`,c),`integer x`))) THEN ASM_REAL_ARITH_TAC)
            [`&0`; `-- &1`; `&1`]));;

let MOI_S8C_PSI_INJ = prove
 (`!y y':real^2.
     y IN relative_frontier(interval[--vec 1,vec 1]) /\
     y' IN relative_frontier(interval[--vec 1,vec 1]) /\
     moi_s8c_psi y = moi_s8c_psi y'
     ==> y = y'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC o MATCH_MP MOI_S8C_SIG_ONTO)
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC o MATCH_MP MOI_S8C_SIG_ONTO) MP_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq (concl th))) THEN
  REWRITE_TAC[MOI_S8C_PSI_SIG; MOI_S4U_EX_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t = t' + &8 * (t / &8 - t' / &8)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8C_SIG_PERIODIC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_S8C_PSI_IMAGE = prove
 (`IMAGE moi_s8c_psi (relative_frontier(interval[--vec 1:real^2,vec 1])) =
   sphere(vec 0:real^2,&1)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC o MATCH_MP MOI_S8C_SIG_ONTO))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MOI_S8C_PSI_SIG; MOI_S4U_EX_SPHERE];
    REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_EQ_1_CEXP] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` SUBST1_TAC) THEN
    EXISTS_TAC `moi_s8c_sig (&8 * s / (&2 * pi))` THEN
    REWRITE_TAC[MOI_S8C_SIG_IN; MOI_S8C_PSI_SIG; moi_s4u_ex] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC PI_POS THEN CONV_TAC REAL_FIELD]);;

let MOI_S8C_PSI_HOMEO = prove
 (`?psi'. homeomorphism (relative_frontier(interval[--vec 1:real^2,vec 1]),
                         sphere(vec 0:real^2,&1)) (moi_s8c_psi,psi')`,
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  REWRITE_TAC[MOI_S8C_PSI_CONTINUOUS; MOI_S8C_PSI_IMAGE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN REWRITE_TAC[BOUNDED_INTERVAL];
    MESON_TAC[MOI_S8C_PSI_INJ]]);;

(* The PL covering Q of the torus model and its rescaled relation to the  *)
(* covering moi_s4u_tor of S1 x S1.                                         *)

let moi_s8c_q = new_definition
 `moi_s8c_q (x:real^2) =
    pastecart (moi_s8c_sig (x$1)) (moi_s8c_sig (x$2)):real^(2,2)finite_sum`;;

let moi_s8c_bpsi = new_definition
 `moi_s8c_bpsi (z:real^(2,2)finite_sum) =
    pastecart (moi_s8c_psi (fstcart z)) (moi_s8c_psi (sndcart z)):real^(2,2)finite_sum`;;

let MOI_S8C_BPSI_Q = prove
 (`!x. moi_s8c_bpsi (moi_s8c_q x) = moi_s4u_tor ((&1 / &8) % x)`,
  GEN_TAC THEN REWRITE_TAC[moi_s8c_bpsi; moi_s8c_q; FSTCART_PASTECART; SNDCART_PASTECART;
    MOI_S8C_PSI_SIG; moi_s4u_tor; VECTOR_MUL_COMPONENT; PASTECART_INJ] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_S8C_Q_IN = prove
 (`!x. moi_s8c_q x IN pl_torus_model`,
  REWRITE_TAC[moi_s8c_q; pl_torus_model; PASTECART_IN_PCROSS; MOI_S8C_SIG_IN]);;

let MOI_S8C_Q_EQ = prove
 (`!x y. moi_s8c_q x = moi_s8c_q y <=>
         integer((x$1 - y$1) / &8) /\ integer((x$2 - y$2) / &8)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_s8c_bpsi`) THEN
    REWRITE_TAC[MOI_S8C_BPSI_Q; MOI_S4U_TOR_EQ; VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN REWRITE_TAC[moi_s8c_q; PASTECART_INJ] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(x:real^2)$1 = (y:real^2)$1 + &8 * ((x$1 - y$1) / &8)` SUBST1_TAC
      THENL [REAL_ARITH_TAC; MATCH_MP_TAC MOI_S8C_SIG_PERIODIC THEN FIRST_ASSUM ACCEPT_TAC];
      SUBGOAL_THEN `(x:real^2)$2 = (y:real^2)$2 + &8 * ((x$2 - y$2) / &8)` SUBST1_TAC
      THENL [REAL_ARITH_TAC; MATCH_MP_TAC MOI_S8C_SIG_PERIODIC THEN FIRST_ASSUM ACCEPT_TAC]]]);;

let MOI_S8C_BPSI_FACTS = prove
 (`moi_s8c_bpsi continuous_on pl_torus_model /\
   IMAGE moi_s8c_bpsi pl_torus_model =
   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
   (!z z'. z IN pl_torus_model /\ z' IN pl_torus_model /\ moi_s8c_bpsi z = moi_s8c_bpsi z'
           ==> z = z')`,
  REWRITE_TAC[pl_torus_model] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `moi_s8c_bpsi = \z. pastecart (moi_s8c_psi (fstcart z))
                                                (moi_s8c_psi (sndcart z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; moi_s8c_bpsi]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    CONJ_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `relative_frontier(interval[--vec 1:real^2,vec 1])` THEN
    REWRITE_TAC[MOI_S8C_PSI_CONTINUOUS; SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN
    SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; MOI_FH1_IN_PCROSS] THEN X_GEN_TAC `w:real^(2,2)finite_sum` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^(2,2)finite_sum` (CONJUNCTS_THEN2 SUBST1_TAC
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[moi_s8c_bpsi; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[GSYM MOI_S8C_PSI_IMAGE] THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM MOI_S8C_PSI_IMAGE; IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^2` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `y2:real^2` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `pastecart (y1:real^2) (y2:real^2)` THEN
      ASM_REWRITE_TAC[moi_s8c_bpsi; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[PASTECART_INJ; FSTCART_PASTECART; SNDCART_PASTECART]];
    REWRITE_TAC[MOI_FH1_IN_PCROSS; moi_s8c_bpsi; PASTECART_INJ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_INJ] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S8C_PSI_INJ THEN
    ASM_REWRITE_TAC[]]);;

(* Lifts of loops of the torus model through Q. *)

let MOI_S8C_Q_LIFT = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET pl_torus_model
     ==> integer((moi_s4u_disp (moi_s8c_bpsi o g))$1) /\
         integer((moi_s4u_disp (moi_s8c_bpsi o g))$2) /\
         ?G. path G /\ pathfinish G = pathstart G + &8 % moi_s4u_disp (moi_s8c_bpsi o g) /\
             !t. t IN interval[vec 0,vec 1] ==> moi_s8c_q (G t) = g t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S8C_BPSI_FACTS THEN STRIP_TAC THEN
  MP_TAC(SPEC `moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum)` MOI_S4U_LOOP_LIFT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `pl_torus_model` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        can (find_term (fun t -> t = `moi_s8c_bpsi`)) (lhs (concl th)))) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `\t:real^1. &8 % (h:real^1->real^2) t` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `path (h:real^1->real^2)` THEN REWRITE_TAC[path] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `pathfinish h = pathstart h + moi_s4u_disp (moi_s8c_bpsi o g)` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `moi_s8c_bpsi`)) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "z'")) (concl th))) THEN
    REWRITE_TAC[MOI_S8C_Q_IN; MOI_S8C_BPSI_Q] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ARITH `&1 / &8 * &8 = &1`; VECTOR_MUL_LID] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `path_image (g:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `moi_s4u_tor`)) (concl th))) THEN
      ASM_REWRITE_TAC[o_THM]]]);;

(* ------------------------------------------------------------------------- *)
(* sigma is affine on each [2a-1,2a+1], so Q is PL on the plane.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S8C_INT_CASES4 = prove
 (`!r. integer r /\ &0 <= r /\ r < &4 ==> r = &0 \/ r = &1 \/ r = &2 \/ r = &3`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:real` INTEGER_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `&n < &4` THEN REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_EQ] THEN ARITH_TAC);;

let MOI_S8C_INT_SMALL = prove
 (`!d. integer d /\ abs d < &2 ==> d = -- &1 \/ d = &0 \/ d = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `abs d` INTEGER_POS) THEN ASM_SIMP_TAC[REAL_ABS_POS; INTEGER_ABS] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `n = 0 \/ n = 1` MP_TAC THENL
   [UNDISCH_TAC `abs d < &2` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    STRIP_TAC THEN UNDISCH_TAC `abs d = &n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_S8C_SIG_AFFINE = prove
 (`!a. integer a
       ==> ?A B. !t. &2 * a - &1 <= t /\ t <= &2 * a + &1
                     ==> moi_s8c_sig t = t % A + B`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a / &4` FLOOR) THEN ABBREV_TAC `m = floor(a / &4)` THEN STRIP_TAC THEN
  MP_TAC(SPEC `a - &4 * m` MOI_S8C_INT_CASES4) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`vector[&0; &1]:real^2`; `vector[&1; -- &8 * m]:real^2`] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT1(MATCH_MP (SPECL [`m:real`; `t:real`] MOI_S8C_SIG_PIECES)
                              (ASSUME `integer m`)));
    MAP_EVERY EXISTS_TAC [`vector[-- &1; &0]:real^2`; `vector[&2 + &8 * m; &1]:real^2`] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP (SPECL [`m:real`; `t:real`] MOI_S8C_SIG_PIECES)
                                        (ASSUME `integer m`))));
    MAP_EVERY EXISTS_TAC [`vector[&0; -- &1]:real^2`; `vector[-- &1; &4 + &8 * m]:real^2`] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP (SPECL [`m:real`; `t:real`]
      MOI_S8C_SIG_PIECES) (ASSUME `integer m`)))));
    MAP_EVERY EXISTS_TAC [`vector[&1; &0]:real^2`; `vector[-- &8 * m - &6; -- &1]:real^2`] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP (SPECL [`m:real`; `t:real`]
      MOI_S8C_SIG_PIECES) (ASSUME `integer m`)))))] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* Q is PL on the whole plane: affine on each grid square. *)

let MOI_S8C_Q_PL = prove
 (`pl_map_on (:real^2) moi_s8c_q`,
  REWRITE_TAC[pl_map_on; IN_UNIV; INTER_UNIV; SUBSET_UNIV] THEN X_GEN_TAC `x:real^2` THEN
  ABBREV_TAC `a0 = floor(((x:real^2)$1 + &1) / &2)` THEN
  ABBREV_TAC `b0 = floor(((x:real^2)$2 + &1) / &2)` THEN
  SUBGOAL_THEN `integer a0 /\ integer b0 /\
                a0 <= ((x:real^2)$1 + &1) / &2 /\ (x$1 + &1) / &2 < a0 + &1 /\
                b0 <= (x$2 + &1) / &2 /\ (x$2 + &1) / &2 < b0 + &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "b0"] THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  EXISTS_TAC
   `{interval[vector[&2 * a - &1; &2 * b - &1],vector[&2 * a + &1; &2 * b + &1]]:real^2->bool |
     a IN {a0 - &1, a0, a0 + &1} /\ b IN {b0 - &1, b0, b0 + &1}}` THEN
  EXISTS_TAC `ball(x:real^2,&1)` THEN REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\a b. interval[vector[&2 * a - &1; &2 * b - &1],
                      vector[&2 * a + &1; &2 * b + &1]]:real^2->bool`;
      `{a0 - &1, a0, a0 + &1}`; `\a:real. {b0 - &1, b0, b0 + &1}`]
      FINITE_PRODUCT_DEPENDENT) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[SUBSET; IN_BALL; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN
    ABBREV_TAC `a = floor(((z:real^2)$1 + &1) / &2)` THEN
    ABBREV_TAC `b = floor(((z:real^2)$2 + &1) / &2)` THEN
    SUBGOAL_THEN `integer a /\ integer b /\
                  a <= ((z:real^2)$1 + &1) / &2 /\ (z$1 + &1) / &2 < a + &1 /\
                  b <= (z$2 + &1) / &2 /\ (z$2 + &1) / &2 < b + &1` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((z:real^2)$1 - (x:real^2)$1) < &1 /\ abs(z$2 - x$2) < &1`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `dist(x:real^2,z) < &1` THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPECL [`x - z:real^2`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x - z:real^2`; `2`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `interval[vector[&2 * a - &1; &2 * b - &1],
                         vector[&2 * a + &1; &2 * b + &1]]:real^2->bool` THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      MP_TAC(SPEC `a - a0:real` MOI_S8C_INT_SMALL) THEN
      MP_TAC(SPEC `b - b0:real` MOI_S8C_INT_SMALL) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[FORALL_IN_GSPEC; POLYTOPE_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `integer a /\ integer b` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `a IN {a0 - &1, a0, a0 + &1}` THEN UNDISCH_TAC `b IN {b0 - &1, b0, b0 + &1}` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    MP_TAC(SPEC `a:real` MOI_S8C_SIG_AFFINE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A1:real^2` (X_CHOOSE_TAC `B1:real^2`)) THEN
    MP_TAC(SPEC `b:real` MOI_S8C_SIG_AFFINE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A2:real^2` (X_CHOOSE_TAC `B2:real^2`)) THEN
    EXISTS_TAC `\z:real^2. pastecart (z$1 % (A1:real^2)) (z$2 % (A2:real^2))` THEN
    EXISTS_TAC `pastecart (B1:real^2) (B2:real^2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_PASTECART THEN CONJ_TAC THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
      X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      STRIP_TAC THEN REWRITE_TAC[moi_s8c_q; PASTECART_ADD] THEN
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Planar: a Jordan curve J disjoint from its translate J + v (v          *)
(* nonzero) has J + v outside J (the maximum of x dot v on J is exceeded   *)
(* on J + v), and the closed Jordan regions of J and J + v are disjoint.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S8C_TRANSLATE_OUTSIDE = prove
 (`!(c:real^1->real^2) v.
     simple_path c /\ pathfinish c = pathstart c /\ ~(v = vec 0) /\
     DISJOINT (path_image c) (IMAGE (\x. v + x) (path_image c))
     ==> IMAGE (\x. v + x) (path_image c) SUBSET outside(path_image c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `J = path_image (c:real^1->real^2)` THEN
  SUBGOAL_THEN `compact (J:real^2->bool) /\ ~(J = {}) /\ connected J` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
    SUBGOAL_THEN `path (c:real^1->real^2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. v dot x`; `J:real^2->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{x:real^2 | v dot z0 < v dot x} SUBSET outside J` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J:real^2->bool`; `{x:real^2 | v dot x <= v dot z0}`]
      OUTSIDE_SUBSET_CONVEX) THEN
    REWRITE_TAC[CONVEX_HALFSPACE_LE] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_ELIM_THM; REAL_NOT_LE] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4U_CONNECTED_SIDE THEN EXISTS_TAC `inside J:real^2->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    REWRITE_TAC[ASSUME `inside J UNION outside J = (:real^2) DIFF J`] THEN
    UNDISCH_TAC `DISJOINT (J:real^2->bool) (IMAGE (\x. v + x) J)` THEN SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    EXISTS_TAC `v + z0:real^2` THEN CONJ_TAC THENL
     [EXISTS_TAC `z0:real^2` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `outside:(real^2->bool)->real^2->bool`)) (concl th) &&
        can (find_term ((=) `z0:real^2`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM; DOT_RADD] THEN
      UNDISCH_TAC `~(v:real^2 = vec 0)` THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
      MP_TAC(ISPEC `v:real^2` DOT_POS_LE) THEN REAL_ARITH_TAC]]);;

let MOI_S8C_TRANSLATE_DISKS = prove
 (`!(c:real^1->real^2) v.
     simple_path c /\ pathfinish c = pathstart c /\ ~(v = vec 0) /\
     DISJOINT (path_image c) (IMAGE (\x. v + x) (path_image c))
     ==> DISJOINT (path_image c UNION inside(path_image c))
                  (IMAGE (\x. v + x) (path_image c UNION inside(path_image c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^1->real^2`; `v:real^2`] MOI_S8C_TRANSLATE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c' = (\x:real^2. v + x) o (c:real^1->real^2)` THEN
  SUBGOAL_THEN `simple_path (c':real^1->real^2) /\ pathfinish c' = pathstart c' /\
                path_image c' = IMAGE (\x. v + x) (path_image c)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    REWRITE_TAC[ASSUME `pathfinish (c:real^1->real^2) = pathstart c`] THEN
    MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[ASSUME `simple_path (c:real^1->real^2)`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      SIMP_TAC[VECTOR_ARITH `v + x:real^2 = v + y <=> x = y`]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c':real^1->real^2`; `--v:real^2`] MOI_S8C_TRANSLATE_OUTSIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ARITH `--v + v + x:real^2 = x`; IMAGE_ID] THEN
    UNDISCH_TAC `DISJOINT (path_image c) (IMAGE (\x:real^2. v + x) (path_image c))` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--v + v + x:real^2 = x`; IMAGE_ID] THEN
  DISCH_TAC THEN
  ABBREV_TAC `J = path_image (c:real^1->real^2)` THEN
  ABBREV_TAC `J' = IMAGE (\x:real^2. v + x) J` THEN
  SUBGOAL_THEN `~(J:real^2->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[PATH_IMAGE_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `inside(J':real^2->bool) = IMAGE (\x. v + x) (inside J)` ASSUME_TAC THENL
   [EXPAND_TAC "J'" THEN REWRITE_TAC[INSIDE_TRANSLATION]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `path_image (c:real^1->real^2) = J`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c':real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `path_image (c':real^1->real^2) = IMAGE (\x. v + x) J`;
              ASSUME `IMAGE (\x:real^2. v + x) J = J'`] THEN STRIP_TAC THEN
  REWRITE_TAC[IMAGE_UNION; ASSUME `IMAGE (\x:real^2. v + x) J = J'`;
              GSYM(ASSUME `inside(J':real^2->bool) = IMAGE (\x. v + x) (inside J)`)] THEN
  (* inside J lies outside J' *)
  SUBGOAL_THEN `inside J SUBSET outside(J':real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_CONNECTED_SIDE THEN EXISTS_TAC `inside(J':real^2->bool)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASSUME `inside J' UNION outside J' = (:real^2) DIFF J'`] THEN
      MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
      UNDISCH_TAC `J' SUBSET outside(J:real^2->bool)` THEN SET_TAC[];
      ONCE_REWRITE_TAC[TAUT `~p <=> (p ==> F)`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `inside J SUBSET inside(J':real^2->bool)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(y:real^2) IN (:real^2) DIFF J'` MP_TAC THENL
         [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
          MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
          UNDISCH_TAC `J' SUBSET outside(J:real^2->bool)` THEN
          UNDISCH_TAC `(y:real^2) IN inside J` THEN UNDISCH_TAC `(y:real^2) IN J'` THEN
          SET_TAC[];
          REWRITE_TAC[GSYM(ASSUME `inside J' UNION outside J' = (:real^2) DIFF J'`)] THEN
          UNDISCH_TAC `inside J INTER outside(J':real^2->bool) = {}` THEN
          UNDISCH_TAC `(y:real^2) IN inside J` THEN SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `J SUBSET inside(J':real^2->bool) UNION J'` MP_TAC THENL
       [SUBGOAL_THEN `closure(inside J) SUBSET closure(inside(J':real^2->bool))` MP_TAC THENL
         [MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`J SUBSET outside(J':real^2->bool)`;
                             `DISJOINT (J:real^2->bool) J'`; `~(J:real^2->bool = {})`;
                             `inside J' INTER outside J':real^2->bool = {}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`inside J SUBSET outside(J':real^2->bool)`; `J' SUBSET outside(J:real^2->bool)`;
    `J SUBSET outside(J':real^2->bool)`; `DISJOINT (J:real^2->bool) J'`;
    `inside J INTER outside J:real^2->bool = {}`;
    `inside J' INTER outside J':real^2->bool = {}`] THEN
  REWRITE_TAC[DISJOINT] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The PL lift.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Q is injective on boxes of side 6, and a compact set on which Q is      *)
(* injective, mapped onto a polyhedron, is a polyhedron PL homeomorphic to  *)
(* its image (the inverse is locally the inverse of Q on a box).            *)

let MOI_S8C_Q_BOX_INJ = prove
 (`!x y z:real^2.
     y IN interval[x - vec 3,x + vec 3] /\ z IN interval[x - vec 3,x + vec 3] /\
     moi_s8c_q y = moi_s8c_q z
     ==> y = z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT;
              VECTOR_ADD_COMPONENT; VEC_COMPONENT; MOI_S8C_Q_EQ] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `((y:real^2)$1 - (z:real^2)$1) / &8` MOI_S8C_INT_SMALL) THEN
  MP_TAC(SPEC `((y:real^2)$2 - (z:real^2)$2) / &8` MOI_S8C_INT_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S8C_LIFT_PL = prove
 (`!(J:real^2->bool) (j0:real^(2,2)finite_sum->bool).
     compact J /\ IMAGE moi_s8c_q J = j0 /\ pl_polyhedron j0 /\
     (!x y. x IN J /\ y IN J /\ moi_s8c_q x = moi_s8c_q y ==> x = y)
     ==> pl_polyhedron J /\ ?qi. pl_homeomorphism (J,j0) (moi_s8c_q,qi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. moi_s8c_q continuous_on s` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[MOI_S8C_Q_PL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^2->bool`; `moi_s8c_q`; `j0:real^(2,2)finite_sum->bool`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `qi:real^(2,2)finite_sum->real^2`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  SUBGOAL_THEN `pl_map_on j0 (qi:real^(2,2)finite_sum->real^2)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN X_GEN_TAC `y:real^(2,2)finite_sum` THEN
    DISCH_TAC THEN
    ABBREV_TAC `x = (qi:real^(2,2)finite_sum->real^2) y` THEN
    ABBREV_TAC `B = interval[x - vec 3:real^2,x + vec 3]` THEN
    MP_TAC(ISPECL [`B:real^2->bool`; `moi_s8c_q`; `IMAGE moi_s8c_q (B:real^2->bool)`]
      HOMEOMORPHISM_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "B" THEN REWRITE_TAC[COMPACT_INTERVAL];
        EXPAND_TAC "B" THEN MESON_TAC[MOI_S8C_Q_BOX_INJ]];
      DISCH_THEN(X_CHOOSE_TAC `R:real^(2,2)finite_sum->real^2`)] THEN
    SUBGOAL_THEN `pl_map_on (IMAGE moi_s8c_q (B:real^2->bool)) (R:real^(2,2)finite_sum->real^2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
      MAP_EVERY EXISTS_TAC [`B:real^2->bool`; `moi_s8c_q`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[MOI_S8C_Q_PL; SUBSET_UNIV] THEN EXPAND_TAC "B" THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN REWRITE_TAC[POLYTOPE_INTERVAL];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
      can (find_term ((=) `R:real^(2,2)finite_sum->real^2`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_map_on")) (concl th)))) THEN
    (* continuity of qi at y *)
    SUBGOAL_THEN
     `?u. open u /\ y IN u /\
          !y'. y' IN j0 INTER u ==> (qi:real^(2,2)finite_sum->real^2) y' IN ball(x,&1)`
    (X_CHOOSE_THEN `u:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(qi:real^(2,2)finite_sum->real^2) continuous_on j0` THEN
      REWRITE_TAC[continuous_on] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^(2,2)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(y:real^(2,2)finite_sum,d)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; IN_INTER; IN_BALL; DIST_REFL] THEN
      X_GEN_TAC `y':real^(2,2)finite_sum` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball(x:real^2,&1) SUBSET B` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `interval[x - vec 3:real^2,x + vec 3] = B`)] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL; DIMINDEX_2; FORALL_2;
        VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VEC_COMPONENT; dist] THEN
      X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`x - w:real^2`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x - w:real^2`; `2`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `u:real^(2,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `R:real^(2,2)finite_sum->real^2` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y':real^(2,2)finite_sum` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(qi:real^(2,2)finite_sum->real^2) y' IN B /\
                    moi_s8c_q (qi y') = y'` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `ball(x:real^2,&1) SUBSET B` THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `y':real^(2,2)finite_sum` o check (fun th ->
            can (find_term ((=) `ball(x:real^2,&1)`)) (concl th) && is_forall (concl th))) THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC
           `(y':real^(2,2)finite_sum) IN j0 INTER u` THEN SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(R:real^(2,2)finite_sum->real^2) y' =
                    R(moi_s8c_q ((qi:real^(2,2)finite_sum->real^2) y'))` SUBST1_TAC THENL
       [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `R:real^(2,2)finite_sum->real^2`)) (concl th) &&
        can (find_term ((=) `B:real^2->bool`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE moi_s8c_q (B:real^2->bool)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y':real^(2,2)finite_sum` THEN
        STRIP_TAC THEN EXISTS_TAC `(qi:real^(2,2)finite_sum->real^2) y'` THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `ball(x:real^2,&1) SUBSET B` THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `y':real^(2,2)finite_sum` o check (fun th ->
            can (find_term ((=) `ball(x:real^2,&1)`)) (concl th) && is_forall (concl th))) THEN
          ASM_REWRITE_TAC[IN_INTER] THEN SET_TAC[]];
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (J:real^2->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `J:real^2->bool`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `qi:real^(2,2)finite_sum->real^2` THEN
  REWRITE_TAC[pl_homeomorphism] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  ASM_SIMP_TAC[MOI_S8C_Q_PL; SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

(* ------------------------------------------------------------------------- *)
(* Lifting inessential simple closed curves.                                 *)
(* ------------------------------------------------------------------------- *)

(* Lifting an inessential simple closed curve of the torus model: a simple *)
(* closed curve of the plane, mapped injectively by Q, disjoint from its   *)
(* translates by the nonzero lattice vectors of 8 Z^2.                     *)

let MOI_S8C_SIMPLE_LIFT = prove
 (`!g:real^1->real^(2,2)finite_sum.
     simple_path g /\ pathfinish g = pathstart g /\ path_image g SUBSET pl_torus_model /\
     homotopic_loops pl_torus_model g (linepath(pathstart g,pathstart g))
     ==> ?G. simple_path G /\ pathfinish G = pathstart G /\
             IMAGE moi_s8c_q (path_image G) = path_image g /\
             (!x y. x IN path_image G /\ y IN path_image G /\ moi_s8c_q x = moi_s8c_q y
                    ==> x = y) /\
             (!v. integer(v$1 / &8) /\ integer(v$2 / &8) /\ ~(v = vec 0)
                  ==> DISJOINT (path_image G) (IMAGE (\x. v + x) (path_image G)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (g:real^1->real^(2,2)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC MOI_S8C_BPSI_FACTS THEN STRIP_TAC THEN
  (* the displacement of bpsi o g is zero *)
  SUBGOAL_THEN `moi_s4u_disp (moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum)) = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum)`;
                   `linepath(moi_s8c_bpsi(pathstart (g:real^1->real^(2,2)finite_sum)),
                             moi_s8c_bpsi(pathstart g))`] MOI_S4U_DISP_HOMOTOPIC) THEN
    SUBGOAL_THEN `path (moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum)) /\
                  path_image (moi_s8c_bpsi o g) SUBSET
                  sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                  moi_s8c_bpsi (pathstart g) IN
                  sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `pl_torus_model` THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
          can (find_term (fun t -> t = `moi_s8c_bpsi`)) (lhs (concl th)))) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
          can (find_term (fun t -> t = `moi_s8c_bpsi`)) (lhs (concl th)))) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `path_image (g:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
        MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` PATHSTART_IN_PATH_IMAGE) THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_LINEPATH;
                      PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                      SEGMENT_REFL; SING_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ (r ==> s) ==> (p <=> r) ==> s`) THEN CONJ_TAC THENL
     [SUBGOAL_THEN `linepath(moi_s8c_bpsi(pathstart (g:real^1->real^(2,2)finite_sum)),
                             moi_s8c_bpsi(pathstart g)) =
                    moi_s8c_bpsi o linepath(pathstart g,pathstart g)` SUBST1_TAC THENL
       [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `pl_torus_model` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        can (find_term (fun t -> t = `moi_s8c_bpsi`)) (lhs (concl th)))) THEN
      REWRITE_TAC[SUBSET_REFL];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOI_S4U_DISP_CONST THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `g:real^1->real^(2,2)finite_sum` MOI_S8C_Q_LIFT) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^1->real^2` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      moi_s8c_q ((G:real^1->real^2) s) = moi_s8c_q (G t)
                      ==> G s = G t /\
                          (s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0:real^1)`
    MP_TAC THENL
     [UNDISCH_TAC `simple_path (g:real^1->real^(2,2)finite_sum)` THEN
      REWRITE_TAC[simple_path] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `pathfinish (G:real^1->real^2) = pathstart G` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `G:real^1->real^2` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[simple_path] THEN MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `G:real^1->real^2`)) (concl th) &&
      can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[path_image; GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^1. x IN s ==> (f:real^1->real^(2,2)finite_sum) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[path_image; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x':real^1`; `x'':real^1`] o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `G:real^1->real^2`)) (concl th) &&
      can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; path_image] THEN
    X_GEN_TAC `w:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w':real^2` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)))) THEN
    UNDISCH_TAC `~(v:real^2 = vec 0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `G:real^1->real^2`)) (concl th) &&
      can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_s8c_q ((G:real^1->real^2) s) = moi_s8c_q (G t)` (fun th ->
      REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `(G:real^1->real^2) s = v + G t` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_S8C_Q_EQ; VECTOR_ADD_COMPONENT] THEN
      ASM_REWRITE_TAC[REAL_ARITH `(v + x) - x:real = v`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `(G:real^1->real^2) s = v + G t` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The model disk.                                                           *)
(* ------------------------------------------------------------------------- *)

(* An inessential PL circle of the torus model bounds a PL 2-cell in it.   *)

let MOI_S8C_MODEL_DISK = prove
 (`!j0:real^(2,2)finite_sum->bool.
     j0 SUBSET pl_torus_model /\ pl_sphere 1 j0 /\
     (!g. path g /\ pathfinish g = pathstart g /\ path_image g SUBSET j0
          ==> homotopic_loops pl_torus_model g (linepath(pathstart g,pathstart g)))
     ==> ?d. d SUBSET pl_torus_model /\ pl_cell_with_boundary 2 d j0`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?g:real^1->real^(2,2)finite_sum.
                  simple_path g /\ pathfinish g = pathstart g /\ path_image g = j0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4U_PL_SPHERE1_CIRCLE
      (ASSUME `pl_sphere 1 (j0:real^(2,2)finite_sum->bool)`)) THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    DISCH_THEN(X_CHOOSE_THEN `h0:real^2->real^(2,2)finite_sum`
      (X_CHOOSE_THEN `k0:real^(2,2)finite_sum->real^2` ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
    STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
    EXISTS_TAC `(h0:real^2->real^(2,2)finite_sum) o circlepath(vec 0:real^2,&1)` THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `g:real^1->real^(2,2)finite_sum` MOI_S8C_SIMPLE_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^1->real^2` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `J = path_image (G:real^1->real^2)` THEN
  SUBGOAL_THEN `compact (J:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
    MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^2->bool`; `j0:real^(2,2)finite_sum->bool`] MOI_S8C_LIFT_PL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `qi:real^(2,2)finite_sum->real^2`))] THEN
  (* J is a PL circle of the plane *)
  SUBGOAL_THEN `pl_sphere 1 (J:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_sphere 1 (j0:real^(2,2)finite_sum->bool)` THEN
    REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN
      `f0:real^(2,2)finite_sum->real^(2,2)finite_sum` (X_CHOOSE_THEN
      `g0:real^(2,2)finite_sum->real^(2,2)finite_sum` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`convex hull {vec 0:real^2,basis 1,basis 2}`;
                   `k0:real^(2,2)finite_sum->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
    ASM_REWRITE_TAC[MOI_S27_STD_SIMPLEX_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^(2,2)finite_sum` (X_CHOOSE_THEN
      `q:real^(2,2)finite_sum->real^2` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `convex hull {vec 0:real^2,basis 1,basis 2}` THEN
    REWRITE_TAC[MOI_S27_STD_SIMPLEX_2] THEN
    EXISTS_TAC `(qi:real^(2,2)finite_sum->real^2) o
                ((f0:real^(2,2)finite_sum->real^(2,2)finite_sum) o
                 (p:real^2->real^(2,2)finite_sum))` THEN
    EXISTS_TAC `((q:real^(2,2)finite_sum->real^2) o
                 (g0:real^(2,2)finite_sum->real^(2,2)finite_sum)) o moi_s8c_q` THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `j0:real^(2,2)finite_sum->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `relative_frontier k0:real^(2,2)finite_sum->bool` THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the planar disk D and the injectivity of Q on it *)
  MP_TAC(SPEC `J:real^2->bool` (REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT] PL_SCHOENFLIES_2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `D = (J:real^2->bool) UNION inside J` THEN
  SUBGOAL_THEN `!x y. x IN D /\ y IN D /\ moi_s8c_q x = moi_s8c_q y ==> x:real^2 = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    REWRITE_TAC[MOI_S8C_Q_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`G:real^1->real^2`; `x - y:real^2`] MOI_S8C_TRANSLATE_DISKS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_SUB_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `path_image (G:real^1->real^2) = J`;
                ASSUME `(J:real^2->bool) UNION inside J = D`] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `pl_ball 2 (D:real^2->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `kD:real^2->bool` (X_CHOOSE_THEN `fD:real^2->real^2`
    (X_CHOOSE_THEN `gD:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (fD:real^2->real^2) (relative_frontier kD) = J` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kD:real^2->bool`; `D:real^2->bool`; `fD:real^2->real^2`;
                   `gD:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "D" THEN EXPAND_TAC "J" THEN MATCH_MP_TAC MOI_PL2_FRONTIER_JORDAN_REGION THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (D:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (kD,D) (fD:real^2->real^2,gD)`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `D:real^2->bool`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
    EXISTS_TAC `&2:int` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `moi_s8c_q`; `IMAGE moi_s8c_q (D:real^2->bool)`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[MOI_S8C_Q_PL]];
    DISCH_THEN(X_CHOOSE_TAC `qD:real^(2,2)finite_sum->real^2`)] THEN
  SUBGOAL_THEN `pl_homeomorphism (D,IMAGE moi_s8c_q D) (moi_s8c_q,qD:real^(2,2)finite_sum->real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[MOI_S8C_Q_PL; SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE moi_s8c_q (D:real^2->bool)` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S8C_Q_IN] THEN
  UNDISCH_TAC `pl_sphere 1 (j0:real^(2,2)finite_sum->bool)` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN
    `f0:real^(2,2)finite_sum->real^(2,2)finite_sum` (X_CHOOSE_THEN
    `g0:real^(2,2)finite_sum->real^(2,2)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k0:real^(2,2)finite_sum->bool`; `kD:real^2->bool`; `&2:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(2,2)finite_sum->real^2` (X_CHOOSE_THEN
    `q:real^2->real^(2,2)finite_sum` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN EXISTS_TAC `k0:real^(2,2)finite_sum->bool` THEN
  EXISTS_TAC `moi_s8c_q o ((fD:real^2->real^2) o (p:real^(2,2)finite_sum->real^2))` THEN
  EXISTS_TAC `((q:real^2->real^(2,2)finite_sum) o (gD:real^2->real^2)) o
              (qD:real^(2,2)finite_sum->real^2)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `kD:real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `pl_homeomorphism (relative_frontier k0,relative_frontier kD)
                   (p:real^(2,2)finite_sum->real^2,q)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* MOISE_288.  Members essential in frontier s carry H_1(s)                  *)
(* (pc_moi_s34_torus); members inessential in frontier s bound PL 2-cells in *)
(* it (the model disk, transported by PL_SOLID_TORUS_BASIC).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S8C_CONNECTED_IN_MEMBER = prove
 (`!(t:real^N->bool) jj.
     connected t /\ ~(t = {}) /\ t SUBSET UNIONS jj /\ FINITE jj /\
     pairwise DISJOINT jj /\ (!j. j IN jj ==> closed j)
     ==> ?j. j IN jj /\ t SUBSET j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(t:real^N->bool = {})`)) THEN
  SUBGOAL_THEN `?j:real^N->bool. j IN jj /\ x IN j` (X_CHOOSE_THEN `j:real^N->bool`
    STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(t:real^N->bool) SUBSET UNIONS jj` THEN
    UNDISCH_TAC `(x:real^N) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `j:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed (UNIONS (jj DELETE (j:real^N->bool))) /\
                DISJOINT j (UNIONS (jj DELETE j)) /\
                t SUBSET j UNION UNIONS (jj DELETE j)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
      REWRITE_TAC[SET_RULE `!a:real^N->bool s. DISJOINT a (UNIONS s) <=>
                             !x. x IN s ==> DISJOINT a x`; IN_DELETE] THEN
      UNDISCH_TAC `pairwise DISJOINT (jj:(real^N->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `(t:real^N->bool) SUBSET UNIONS jj` THEN
      UNDISCH_TAC `(j:real^N->bool) IN jj` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (t:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  DISCH_THEN(MP_TAC o SPECL [`j:real^N->bool`; `UNIONS (jj DELETE (j:real^N->bool))`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_SIMP_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`DISJOINT (j:real^N->bool) (UNIONS (jj DELETE j))`;
                         `(t:real^N->bool) SUBSET j UNION UNIONS (jj DELETE j)`;
                         `(x:real^N) IN t`; `(x:real^N) IN j`] THEN
  SET_TAC[]);;

let MOI_S8C_ESSENTIAL_CARRIES = prove
 (`!(s:real^3->bool) jj j.
     pl_solid_torus s /\ FINITE jj /\ pairwise DISJOINT jj /\
     (!j. j IN jj ==> pl_sphere 1 j /\ j SUBSET frontier s) /\
     carries_h1 (UNIONS jj) s /\ j IN jj /\
     (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET j /\
          ~homotopic_loops (frontier s) k (linepath(pathstart k,pathstart k)))
     ==> carries_h1 j s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4U_PL_SOLID_TORUS_FACTS) THEN
  ABBREV_TAC `th = frontier (s:real^3->bool)` THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET th /\ j homeomorphic sphere(vec 0:real^2,&1) /\
                UNIONS jj SUBSET (th:real^3->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_image (homology_group(&1,subtopology euclidean (UNIONS jj)),
                 homology_group(&1,subtopology euclidean th))
                (hom_induced (&1) (subtopology euclidean (UNIONS jj),{})
                                  (subtopology euclidean th,{}) (\x:real^3. x)) SUBSET
    group_image (homology_group(&1,subtopology euclidean j),
                 homology_group(&1,subtopology euclidean th))
                (hom_induced (&1) (subtopology euclidean j,{})
                                  (subtopology euclidean th,{}) (\x:real^3. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN ASM_REWRITE_TAC[MOI_S4U_IMAGE_SUBGROUP] THEN
    X_GEN_TAC `g:real^1->real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`path_image (g:real^1->real^3)`; `jj:(real^3->bool)->bool`]
      MOI_S8C_CONNECTED_IN_MEMBER) THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATH_IMAGE_NONEMPTY] THEN ANTS_TAC THENL
     [X_GEN_TAC `j':real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN
      EXISTS_TAC `1` THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j':real^3->bool` STRIP_ASSUME_TAC)] THEN
    ASM_CASES_TAC `j':real^3->bool = j` THENL
     [MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`th:real^3->bool`; `j:real^3->bool`; `g:real^1->real^3`]
      MOI_S4U_CURVE_LOOPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `k:real^1->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (j':real^3->bool) j` MP_TAC THENL
       [UNDISCH_TAC `pairwise DISJOINT (jj:(real^3->bool)->bool)` THEN
        REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`path_image (g:real^1->real^3) SUBSET j'`;
                             `UNIONS jj SUBSET (th:real^3->bool)`;
                             `(j':real^3->bool) IN jj`] THEN
      SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^3` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
    MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `carries_h1 (UNIONS jj) (s:real^3->bool)` THEN REWRITE_TAC[carries_h1] THEN
  MP_TAC(ISPECL [`UNIONS jj:real^3->bool`; `th:real^3->bool`; `s:real^3->bool`]
    MOI_S4U_IMAGE_COMPOSE) THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `th:real^3->bool`; `s:real^3->bool`]
    MOI_S4U_IMAGE_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[homology_group; HOM_INDUCED];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S8C_MODEL_SIMPLEX = prove
 (`&2 simplex (IMAGE (\x:real^2. pastecart x (vec 0:real^2))
                     (convex hull {vec 0:real^2,basis 1,basis 2}))`,
  MP_TAC(ISPECL [`\x:real^2. pastecart x (vec 0:real^2)`; `vec 0:real^(2,2)finite_sum`;
                 `&2:int`; `convex hull {vec 0:real^2,basis 1,basis 2}`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  REWRITE_TAC[MOI_S27_STD_SIMPLEX_2; VECTOR_ADD_RID; PASTECART_INJ] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_ID; LINEAR_ZERO];
    SIMP_TAC[ETA_AX]]);;

let MOI_S8C_INESSENTIAL_DISK = prove
 (`!(s:real^3->bool) j.
     pl_solid_torus s /\ pl_sphere 1 j /\ j SUBSET frontier s /\
     (!k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET j
          ==> homotopic_loops (frontier s) k (linepath(pathstart k,pathstart k)))
     ==> ?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real^3->bool` (CONJUNCT2 PL_SOLID_TORUS_BASIC)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_THEN `ps:real^3->real^(2,2)finite_sum` ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  SUBGOAL_THEN `pl_polyhedron (j:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `j0 = IMAGE (ps:real^3->real^(2,2)finite_sum) j` THEN
  SUBGOAL_THEN `pl_homeomorphism (j,j0) (ps:real^3->real^(2,2)finite_sum,ph)` ASSUME_TAC THENL
   [EXPAND_TAC "j0" THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`frontier s:real^3->bool`; `pl_torus_model`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `j0 SUBSET pl_torus_model` ASSUME_TAC THENL
   [EXPAND_TAC "j0" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `pl_torus_model`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* j0 is a PL circle *)
  SUBGOAL_THEN `pl_sphere 1 (j0:real^(2,2)finite_sum->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_sphere 1 (j:real^3->bool)` THEN REWRITE_TAC[pl_sphere] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`IMAGE (\x:real^2. pastecart x (vec 0:real^2))
                          (convex hull {vec 0:real^2,basis 1,basis 2})`;
                   `k:real^3->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
    ASM_REWRITE_TAC[MOI_S8C_MODEL_SIMPLEX] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^(2,2)finite_sum->real^3` (X_CHOOSE_THEN
      `q:real^3->real^(2,2)finite_sum` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (\x:real^2. pastecart x (vec 0:real^2))
                      (convex hull {vec 0:real^2,basis 1,basis 2})` THEN
    REWRITE_TAC[MOI_S8C_MODEL_SIMPLEX] THEN
    EXISTS_TAC `(ps:real^3->real^(2,2)finite_sum) o
                ((f:real^3->real^3) o (p:real^(2,2)finite_sum->real^3))` THEN
    EXISTS_TAC `((q:real^3->real^(2,2)finite_sum) o (g:real^3->real^3)) o
                (ph:real^(2,2)finite_sum->real^3)` THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* loops in j0 are null-homotopic in the model *)
  SUBGOAL_THEN
   `!g0:real^1->real^(2,2)finite_sum.
      path g0 /\ pathfinish g0 = pathstart g0 /\ path_image g0 SUBSET j0
      ==> homotopic_loops pl_torus_model g0 (linepath(pathstart g0,pathstart g0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `g0:real^1->real^(2,2)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `path_image (g0:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model`
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`path_image (g0:real^1->real^(2,2)finite_sum) SUBSET j0`;
                             `j0 SUBSET pl_torus_model`] THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(ph:real^(2,2)finite_sum->real^3) o
                                 (g0:real^1->real^(2,2)finite_sum)` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `frontier s:real^3->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "homotopic_loops")) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `pl_torus_model` THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC [`path_image (g0:real^1->real^(2,2)finite_sum) SUBSET j0`;
                               `IMAGE (ps:real^3->real^(2,2)finite_sum) j = j0`;
                               `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y`;
                               `(j:real^3->bool) SUBSET frontier s`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPECL [`ps:real^3->real^(2,2)finite_sum`; `pl_torus_model`] o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE)) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    SUBGOAL_THEN `(ps:real^3->real^(2,2)finite_sum) o
                  linepath(pathstart ((ph:real^(2,2)finite_sum->real^3) o g0),pathstart (ph o g0)) =
                  linepath(pathstart g0,pathstart g0)` SUBST1_TAC THENL
     [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM; PATHSTART_COMPOSE] THEN REPEAT GEN_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPEC `g0:real^1->real^(2,2)finite_sum` PATHSTART_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `path_image (g0:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(ps:real^3->real^(2,2)finite_sum) o (ph:real^(2,2)finite_sum->real^3) o
                (g0:real^1->real^(2,2)finite_sum)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (g0:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `j0:real^(2,2)finite_sum->bool` MOI_S8C_MODEL_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (ph:real^(2,2)finite_sum->real^3) d0` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `frontier s:real^3->bool`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d0:real^(2,2)finite_sum->bool) j0` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN
    `f0:real^(2,2)finite_sum->real^(2,2)finite_sum` (X_CHOOSE_THEN
    `g0:real^(2,2)finite_sum->real^(2,2)finite_sum` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_sphere 1 (j:real^3->bool)` THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `fk:real^3->real^3`
    (X_CHOOSE_THEN `gk:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `k0:real^(2,2)finite_sum->bool`; `&2:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^(2,2)finite_sum` (X_CHOOSE_THEN
    `q:real^(2,2)finite_sum->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (d0,IMAGE (ph:real^(2,2)finite_sum->real^3) d0)
                  (ph,ps:real^3->real^(2,2)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`pl_torus_model`; `frontier s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pl_polyhedron (d0:real^(2,2)finite_sum->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `pl_homeomorphism (k0,d0) (f0:real^(2,2)finite_sum->real^(2,2)finite_sum,g0)`)) THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `d0:real^(2,2)finite_sum->bool`)) THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
      EXISTS_TAC `&2:int` THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  EXISTS_TAC `k:real^3->bool` THEN
  EXISTS_TAC `(ph:real^(2,2)finite_sum->real^3) o
              ((f0:real^(2,2)finite_sum->real^(2,2)finite_sum) o
               (p:real^3->real^(2,2)finite_sum))` THEN
  EXISTS_TAC `((q:real^(2,2)finite_sum->real^3) o
               (g0:real^(2,2)finite_sum->real^(2,2)finite_sum)) o
              (ps:real^3->real^(2,2)finite_sum)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `d0:real^(2,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k0:real^(2,2)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `pl_homeomorphism (relative_frontier k,relative_frontier k0)
                   (p:real^3->real^(2,2)finite_sum,q)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `j0:real^(2,2)finite_sum->bool`)) THEN
    EXPAND_TAC "j0" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC(SET_RULE
      `!f:real^3->real^3 s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET frontier s` THEN ASM SET_TAC[]]);;

let MOISE_288 = prove
 (`MOISE_288_STATEMENT`,
  REWRITE_TAC[MOISE_288_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET j /\
        ~homotopic_loops (frontier s) k (linepath(pathstart k,pathstart (k:real^1->real^3)))`
  THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_S8C_ESSENTIAL_CARRIES THEN
    EXISTS_TAC `jj:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC MOI_S8C_INESSENTIAL_DISK THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN MESON_TAC[]]);;

