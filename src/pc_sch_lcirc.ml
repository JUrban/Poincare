(* ========================================================================= *)
(* pc_sch_lcirc: a compact, connected, isolated component K of the regular   *)
(* zero set of a smooth planar function phi is the central circle of a       *)
(* planar neck (SCH4N_PLANAR_NECK). The level field rot(grad phi) has K as a *)
(* periodic orbit; the normal field grad phi / |grad phi|^2 moves across the *)
(* levels at unit speed; the neck is                                         *)
(* F(x) = Psi_{eps(|x| - 1)}(Phi_{T Arg x/2pi} p).                           *)
(* ========================================================================= *)

needs "src/pc_sch_vflow.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic tools.  A linear first integral of a complete flow,               *)
(* a 2x2 invertibility criterion, and the rotation of R^2 by a right angle.  *)
(* ------------------------------------------------------------------------- *)

let SCH4N_FLOW_LINEAR_INTEGRAL = prove
 (`!(v:real^N->real^N) (F0:real^N->real^1) U c x t.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
     open U /\ (!y. y IN U ==> (F0 has_derivative frechet_derivative F0 (at y)) (at y) /\
                               frechet_derivative F0 (at y) (v y) = c) /\
     (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
          ==> ode_vf_flow v (:real^N) u x IN U)
     ==> F0(ode_vf_flow v (:real^N) t x) = F0 x + drop t % c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^N) (v:real^N->real^N)`)) THEN
  SUBGOAL_THEN `!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                    ==> ((\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x) -
                              drop s % c) has_vector_derivative vec 0) (at u)` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `vec 0:real^1 = c - c` SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\s. ode_vf_flow (v:real^N->real^N) (:real^N) s x`;
                     `(v:real^N->real^N) (ode_vf_flow v (:real^N) u x)`; `F0:real^N->real^1`;
                     `frechet_derivative (F0:real^N->real^1) (at (ode_vf_flow v (:real^N) u x))`;
                     `u:real^1`] SCH5_CHAIN_VECTOR) THEN
      REWRITE_TAC[o_DEF] THEN
      SUBGOAL_THEN `ode_vf_flow (v:real^N->real^N) (:real^N) u x IN U` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) t x) - drop t % c =
                F0(ode_vf_flow v (:real^N) (vec 0) x) - drop(vec 0) % c` MP_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `&0 <= drop t \/ drop t <= &0`) THENL
     [MP_TAC(ISPECL [`\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x) -
                          drop s % c`; `vec 0:real^1`; `t:real^1`] SCH5V_ZERO_DERIV_CONST) THEN
      ASM_REWRITE_TAC[DROP_VEC] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
        REWRITE_TAC[DROP_VEC]];
      MP_TAC(ISPECL [`\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x) -
                          drop s % c`; `t:real^1`; `vec 0:real^1`] SCH5V_ZERO_DERIV_CONST) THEN
      ASM_REWRITE_TAC[DROP_VEC] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
        REWRITE_TAC[DROP_VEC] THEN DISCH_THEN(ACCEPT_TAC o SYM)]];
    ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN VECTOR_ARITH_TAC]);;

(* A linear map of R^2 with n . D h = h$1 and D(basis 2) <> 0 is invertible. *)

let SCH4N_DET2 = prove
 (`!(D:real^2->real^2) (n:real^2).
     linear D /\ (!h. n dot D h = h$1) /\ ~(D(basis 2) = vec 0)
     ==> ~(det(matrix D) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2)$1 = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^2 = x$2 % basis 2` ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$2 % (D:real^2->real^2)(basis 2) = vec 0` MP_TAC THENL
   [MP_TAC(ISPECL [`D:real^2->real^2`; `(x:real^2)$2`; `basis 2:real^2`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(x:real^2) = x$2 % basis 2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(x:real^2 = vec 0)` THEN
  UNDISCH_TAC `(x:real^2) = x$2 % basis 2` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO]);;

(* The rotation of R^2 by a right angle. *)

let sch4n_rot = new_definition
 `sch4n_rot (u:real^2) = vector[--(u$2); u$1]:real^2`;;

let SCH4N_ROT_FACTS = prove
 (`(!u:real^2. u dot sch4n_rot u = &0) /\
   (!u:real^2. norm(sch4n_rot u) = norm u) /\
   (!u:real^2. sch4n_rot u = vec 0 <=> u = vec 0) /\
   linear sch4n_rot`,
  REWRITE_TAC[sch4n_rot; DOT_2; VECTOR_2; NORM_EQ; DOT_2] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    GEN_TAC THEN SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[linear; sch4n_rot] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The setting and the two fields.  V = chi rot(G) (tangent to               *)
(* the levels of phi) and N = chi G/|G|^2 (unit speed across the levels),    *)
(* with a cutoff chi = 1 near K and compact support where G <> 0.             *)
(* ------------------------------------------------------------------------- *)

let sch4n_setup = new_definition
 `sch4n_setup (phi:real^2->real) (G:real^2->real^2) W K d0 <=>
    open W /\ smooth_map_on W G /\
    (!z. z IN W ==> ((\z. lift(phi z)) has_derivative (\h. lift(G z dot h))) (at z)) /\
    compact K /\ connected K /\ ~(K = {}) /\ K SUBSET W /\
    (!z. z IN K ==> phi z = &0 /\ ~(G z = vec 0)) /\
    &0 < d0 /\ (!z y. z IN W /\ phi z = &0 /\ y IN K /\ dist(z,y) < d0 ==> z IN K)`;;

let SCH4N_FIELDS = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0.
     sch4n_setup phi G W K d0
     ==> ?d (V:real^2->real^2) (N:real^2->real^2) BV BN.
           &0 < d /\ d <= d0 /\
           smooth_map_on (:real^2) V /\ smooth_map_on (:real^2) N /\
           (!z. norm(V z) <= BV) /\ (!z. norm(N z) <= BN) /\ &0 < BN /\
           (!y. ode_vf_maxint V (:real^2) y = (:real^1)) /\
           (!y. ode_vf_maxint N (:real^2) y = (:real^1)) /\
           (!z y. y IN K /\ dist(y,z) < d
                  ==> z IN W /\ ~(G z = vec 0) /\ V z = sch4n_rot(G z) /\
                      N z = inv(G z dot G z) % G z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch4n_setup] THEN STRIP_TAC THEN
  ABBREV_TAC `W1 = {z:real^2 | z IN W /\ ~((G:real^2->real^2) z = vec 0)}` THEN
  SUBGOAL_THEN `open(W1:real^2->bool) /\ K SUBSET W1 /\ W1 SUBSET W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W1" THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{z:real^2 | z IN W /\ ~((G:real^2->real^2) z = vec 0)} =
                    {z | z IN W /\ G z IN (:real^2) DIFF {vec 0}}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `W1:real^2->bool`; `d0:real`] SCH5V_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `chi:real^2->real`
    (X_CHOOSE_THEN `L:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `smooth_map_on W1 (\z. sch4n_rot((G:real^2->real^2) z)) /\
                smooth_map_on W1 (\z. inv(G z dot G z) % (G:real^2->real^2) z)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on W1 (G:real^2->real^2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`W1:real^2->bool`; `G:real^2->real^2`; `sch4n_rot`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[SCH4N_ROT_FACTS; o_DEF];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`W1:real^2->bool`;
                   `\z. lift(inv(drop(lift((G:real^2->real^2) z dot G z))))`;
                   `G:real^2->real^2`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W1:real^2->bool`; `\z. lift((G:real^2->real^2) z dot G z)`]
      SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`W1:real^2->bool`; `G:real^2->real^2`; `G:real^2->real^2`]
        SMOOTH_MAP_ON_DOT_OPEN) THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W1" THEN REWRITE_TAC[IN_ELIM_THM; DOT_EQ_0] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^2->real^2.
                  smooth_map_on W1 f
                  ==> smooth_map_on (:real^2) (\z. (chi:real^2->real) z % f z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN W1` THENL
     [EXISTS_TAC `W1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`W1:real^2->bool`; `\z. lift((chi:real^2->real) z)`;
                     `f:real^2->real^2`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `(:real^2) DIFF L` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\z:real^2. vec 0:real^2` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\ !z. z IN L ==> norm((G:real^2->real^2) z) <= M`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded(IMAGE (G:real^2->real^2) L)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      ASM SET_TAC[];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M'. &0 < M' /\
                     !z. z IN L ==> norm(inv((G:real^2->real^2) z dot G z) % G z) <= M'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded(IMAGE (\z. inv((G:real^2->real^2) z dot G z) % G z) L)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `W1:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z f:real^2->real^2 B.
                  &0 <= B /\ (!z. z IN L ==> norm(f z) <= B)
                  ==> norm((chi:real^2->real) z % f z) <= B`
  (LABEL_TAC "BD") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `(z:real^2) IN L` THENL
     [REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * norm((f:real^2->real^2) z)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
          can (term_match [] `!x:real^2. &0 <= chi x /\ chi x <= &1`) (concl th))) THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; NORM_0]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "SM" o check (fun th ->
    can (term_match [] `!f:real^2->real^2. smooth_map_on W1 f
                          ==> smooth_map_on (:real^2) (\z. (chi:real^2->real) z % f z)`)
        (concl th))) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. (chi:real^2->real) z % sch4n_rot((G:real^2->real^2) z)) /\
                smooth_map_on (:real^2) (\z. chi z % (inv(G z dot G z) % G z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "SM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!z. norm((chi:real^2->real) z % sch4n_rot((G:real^2->real^2) z)) <= M) /\
                (!z. norm(chi z % (inv(G z dot G z) % G z)) <= M')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real^2` THEN USE_THEN "BD" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SCH4N_ROT_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. ode_vf_maxint (\z. (chi:real^2->real) z % sch4n_rot((G:real^2->real^2) z))
                                     (:real^2) y = (:real^1)) /\
                (!y. ode_vf_maxint (\z. chi z % (inv(G z dot G z) % G z)) (:real^2) y = (:real^1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCH5V_BOUNDED_COMPLETE THENL
     [EXISTS_TAC `M:real`; EXISTS_TAC `M':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `\z. (chi:real^2->real) z % sch4n_rot((G:real^2->real^2) z)`;
                        `\z. (chi:real^2->real) z % (inv((G:real^2->real^2) z dot G z) % G z)`;
                        `M:real`; `M':real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `z:real^2`] o check (fun th ->
    can (term_match [] `!y x:real^2. y IN K /\ dist(y,x) < d ==> chi x = &1 /\ x IN W1`)
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  UNDISCH_TAC `(z:real^2) IN W1` THEN EXPAND_TAC "W1" THEN SIMP_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* The fields bundle, the first integrals near K (phi is                     *)
(* constant along V and grows at unit speed along N), and the invariance of  *)
(* K under the flow of V.                                                    *)
(* ------------------------------------------------------------------------- *)

let sch4n_fields = new_definition
 `sch4n_fields (G:real^2->real^2) W K d (V:real^2->real^2) (N:real^2->real^2) BV BN <=>
    &0 < d /\ smooth_map_on (:real^2) V /\ smooth_map_on (:real^2) N /\
    (!z. norm(V z) <= BV) /\ (!z. norm(N z) <= BN) /\ &0 < BN /\
    (!y. ode_vf_maxint V (:real^2) y = (:real^1)) /\
    (!y. ode_vf_maxint N (:real^2) y = (:real^1)) /\
    (!z y. y IN K /\ dist(y,z) < d
           ==> z IN W /\ ~(G z = vec 0) /\ V z = sch4n_rot(G z) /\
               N z = inv(G z dot G z) % G z)`;;

let SCH4N_FIELDS_EXIST = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0.
     sch4n_setup phi G W K d0
     ==> ?d (V:real^2->real^2) (N:real^2->real^2) BV BN.
           d <= d0 /\ sch4n_fields G W K d V N BV BN`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SCH4N_FIELDS) THEN
  REWRITE_TAC[sch4n_fields] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SCH4N_FLOW_CONT = prove
 (`!(v:real^N->real^N) x.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
     ==> (\t. ode_vf_flow v (:real^N) t x) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^N) (v:real^N->real^N)`)) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `t:real^1` THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h:real^1. drop h % (v:real^N->real^N)(ode_vf_flow v (:real^N) t x)` THEN
  REWRITE_TAC[GSYM has_vector_derivative] THEN ASM_REWRITE_TAC[]);;

(* The region near K where the fields have their exact form. *)

let SCH4N_REGION = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN
     ==> open {z:real^2 | ?y. y IN K /\ dist(y,z) < d} /\
         K SUBSET {z:real^2 | ?y. y IN K /\ dist(y,z) < d} /\
         (!z. z IN {z:real^2 | ?y. y IN K /\ dist(y,z) < d}
              ==> z IN W /\ ~(G z = vec 0) /\ V z = sch4n_rot(G z) /\
                  N z = inv(G z dot G z) % G z /\
                  ((\z. lift(phi z)) has_derivative (\h. lift(G z dot h))) (at z) /\
                  frechet_derivative (\z. lift(phi z)) (at z) = (\h. lift(G z dot h)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch4n_setup; sch4n_fields] THEN STRIP_TAC THEN
  REWRITE_TAC[SCH5V_OPEN_NBHD; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `y:real^2`] o check (fun th ->
    can (term_match [] `!z y:real^2. y IN K /\ dist(y,z) < d ==> P z`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((\z. lift((phi:real^2->real) z)) has_derivative
                 (\h. lift((G:real^2->real^2) z dot h))) (at z)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  FIRST_ASSUM ACCEPT_TAC);;

let SCH4N_PHI_ALONG_V = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN x t.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\
     (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
          ==> ode_vf_flow V (:real^2) u x IN {z:real^2 | ?y. y IN K /\ dist(y,z) < d})
     ==> phi(ode_vf_flow V (:real^2) t x) = phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`] SCH4N_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sch4n_fields (G:real^2->real^2) W K d V N BV BN` THEN
  REWRITE_TAC[sch4n_fields] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN
  MP_TAC(ISPECL [`V:real^2->real^2`; `\z:real^2. lift((phi:real^2->real) z)`;
                 `{z:real^2 | ?y. y IN K /\ dist(y,z) < d}`; `x:real^2`; `t:real^1`]
    SCH5V_FLOW_FIRST_INTEGRAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
    can (term_match [] `!z:real^2. z IN {z | ?y. y IN K /\ dist(y,z) < d} ==> P z`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SCH4N_ROT_FACTS; LIFT_NUM]);;

let SCH4N_PHI_ALONG_N = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN x t.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\
     (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
          ==> ode_vf_flow N (:real^2) u x IN {z:real^2 | ?y. y IN K /\ dist(y,z) < d})
     ==> phi(ode_vf_flow N (:real^2) t x) = phi x + drop t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`] SCH4N_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sch4n_fields (G:real^2->real^2) W K d V N BV BN` THEN
  REWRITE_TAC[sch4n_fields] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_ADD] THEN
  MP_TAC(ISPECL [`N:real^2->real^2`; `\z:real^2. lift((phi:real^2->real) z)`;
                 `{z:real^2 | ?y. y IN K /\ dist(y,z) < d}`; `lift(&1)`; `x:real^2`; `t:real^1`]
    SCH4N_FLOW_LINEAR_INTEGRAL) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
    can (term_match [] `!z:real^2. z IN {z | ?y. y IN K /\ dist(y,z) < d} ==> P z`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RMUL; LIFT_EQ] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REWRITE_TAC[DOT_EQ_0]);;

let SCH4N_SPEED = prove
 (`!B d a. &0 <= B /\ &0 < d /\ abs a < d / (B + &1) ==> B * abs a < d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(B * d) / (B + &1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= B ==> &0 < B + &1`] THEN
    ASM_REAL_ARITH_TAC]);;

let SCH4N_INTERVAL_ABS = prove
 (`!w t:real^1. w IN interval[vec 0,t] UNION interval[t,vec 0] ==> abs(drop w) <= abs(drop t)`,
  REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

(* Points flowing for a short time stay close to K. *)

let SCH4N_NEAR = prove
 (`!(v:real^2->real^2) B q r w.
     smooth_map_on (:real^2) v /\ (!y. ode_vf_maxint v (:real^2) y = (:real^1)) /\
     (!z. norm(v z) <= B) /\ &0 <= B /\ B * abs(drop r) < d /\ abs(drop w) <= abs(drop r)
     ==> dist(q, ode_vf_flow v (:real^2) w q) < d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^2) (v:real^2->real^2)`)) THEN
  MP_TAC(ISPECL [`v:real^2->real^2`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`q:real^2`; `vec 0:real^1`; `w:real^1`]) THEN
  ASM_REWRITE_TAC[DROP_VEC; GSYM dist; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * abs(drop(w:real^1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * abs(drop(r:real^1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let SCH4N_K_INVARIANT = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p t.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ p IN K
     ==> ode_vf_flow V (:real^2) t p IN K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{t:real^1 | ode_vf_flow (V:real^2->real^2) (:real^2) t p IN K} = (:real^1)`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN SIMP_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_setup] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_setup" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^2) (V:real^2->real^2)`)) THEN
  SUBGOAL_THEN `&0 <= BV` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((V:real^2->real^2) p)` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{t:real^1 | ode_vf_flow (V:real^2->real^2) (:real^2) t p IN K}` CLOPEN) THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q \/ r) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN X_GEN_TAC `t0:real^1` THEN
      MP_TAC(ISPECL [`V:real^2->real^2`; `p:real^2`] SCH4N_FLOW_CONT) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN X_GEN_TAC `t0:real^1` THEN DISCH_TAC THEN
    EXISTS_TAC `d / (BV + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    ABBREV_TAC `q = ode_vf_flow (V:real^2->real^2) (:real^2) t0 p` THEN
    SUBGOAL_THEN `ode_vf_flow (V:real^2->real^2) (:real^2) u p =
                  ode_vf_flow V (:real^2) (u - t0) q` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `BV * abs(drop(u - t0:real^1)) < d` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH4N_SPEED THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist(t0:real^1,u) < d / (BV + &1)` THEN
      REWRITE_TAC[dist; NORM_1; DROP_SUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!w. abs(drop w) <= abs(drop(u - t0:real^1))
                      ==> dist(q:real^2, ode_vf_flow (V:real^2->real^2) (:real^2) w q) < d`
    (LABEL_TAC "NEAR") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH4N_NEAR THEN
      MAP_EVERY EXISTS_TAC [`BV:real`; `u - t0:real^1`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `q:real^2`; `u - t0:real^1`] SCH4N_PHI_ALONG_V) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `q:real^2` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "NEAR" MATCH_MP_TAC THEN MATCH_MP_TAC SCH4N_INTERVAL_ABS THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^2->real) q = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `q:real^2` o check (fun th ->
        can (term_match [] `!z:real^2. z IN K ==> phi z = &0 /\ P z`) (concl th))) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN `dist(q:real^2, ode_vf_flow (V:real^2->real^2) (:real^2) (u - t0) q) < d`
    ASSUME_TAC THENL
     [USE_THEN "NEAR" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!z y:real^2. z IN W /\ phi z = &0 /\ y IN K /\ dist(z,y) < d0
                                       ==> z IN K`) (concl th))) THEN
    EXISTS_TAC `q:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`ode_vf_flow (V:real^2->real^2) (:real^2) (u - t0) q`;
                                    `q:real^2`] o check (fun th ->
        can (term_match [] `!z y:real^2. y IN K /\ dist(y,z) < d ==> P z`) (concl th))) THEN
      ASM_SIMP_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
    EXISTS_TAC `vec 0:real^1` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Box maps box(c,z0)(w) = Psi_{w1}(Phi_{c w2} z0).  On points               *)
(* of K, phi(box w) = w1 for small w1, so the derivative has n . D h = h$1,  *)
(* and D(basis 2) <> 0 because Psi_{-w1} o box o line is a reparametrized   *)
(* trajectory of V.  Hence box is a local diffeomorphism, and near each      *)
(* point q of K the set K is the local V-orbit of q.                         *)
(* ------------------------------------------------------------------------- *)

let sch4n_box = new_definition
 `sch4n_box (V:real^2->real^2) (N:real^2->real^2) c (z0:real^2) (w:real^2) =
    ode_vf_flow N (:real^2) (lift(w$1)) (ode_vf_flow V (:real^2) (lift(c * w$2)) z0)`;;

let SCH4N_BOX_SMOOTH = prove
 (`!(V:real^2->real^2) (N:real^2->real^2) c z0.
     smooth_map_on (:real^2) V /\ (!y. ode_vf_maxint V (:real^2) y = (:real^1)) /\
     smooth_map_on (:real^2) N /\ (!y. ode_vf_maxint N (:real^2) y = (:real^1))
     ==> smooth_map_on (:real^2) (sch4n_box V N c z0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^2) (V:real^2->real^2)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^2) (N:real^2->real^2)`)) THEN
  SUBGOAL_THEN `sch4n_box (V:real^2->real^2) N c z0 =
                (\w. ode_vf_flow N (:real^2) (lift(w$1))
                       (ode_vf_flow V (:real^2) (lift(c * w$2)) z0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch4n_box]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_vf_flow (N:real^2->real^2) (:real^2)`; `(:real^2)`; `\w:real^2. w$1`;
                 `\w:real^2. ode_vf_flow (V:real^2->real^2) (:real^2) (lift(c * w$2)) z0`]
    SCH5V_FLOW_COMPOSE_SMOOTH) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `1`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    MP_TAC(ISPECL [`ode_vf_flow (V:real^2->real^2) (:real^2)`; `(:real^2)`;
                   `\w:real^2. c * w$2`; `\w:real^2. z0:real^2`] SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(:real^2)`; `c:real`; `\x:real^2. lift(x$2)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `2`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

let SCH4N_BOX_PHI = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN c z0 w.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\
     z0 IN K /\ BN * abs(w$1) < d
     ==> phi(sch4n_box V N c z0 w) = w$1 /\
         ode_vf_flow V (:real^2) (lift(c * w$2)) z0 IN K /\
         dist(ode_vf_flow V (:real^2) (lift(c * w$2)) z0, sch4n_box V N c z0 w) < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k = ode_vf_flow (V:real^2->real^2) (:real^2) (lift(c * (w:real^2)$2)) z0` THEN
  SUBGOAL_THEN `(k:real^2) IN K` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC SCH4N_K_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `d0:real`; `d:real`; `N:real^2->real^2`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
  SUBGOAL_THEN `!u. abs(drop u) <= abs(drop(lift((w:real^2)$1)))
                    ==> dist(k:real^2, ode_vf_flow (N:real^2->real^2) (:real^2) u k) < d`
  (LABEL_TAC "NEAR") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH4N_NEAR THEN
    MAP_EVERY EXISTS_TAC [`BN:real`; `lift((w:real^2)$1)`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch4n_box] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `k:real^2`; `lift((w:real^2)$1)`] SCH4N_PHI_ALONG_N) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:real^2` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "NEAR" MATCH_MP_TAC THEN MATCH_MP_TAC SCH4N_INTERVAL_ABS THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_setup] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_setup" with Failure _ -> false)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2` o check (fun th ->
      can (term_match [] `!z:real^2. z IN K ==> phi z = &0 /\ P z`) (concl th))) THEN
    ASM_SIMP_TAC[REAL_ADD_LID];
    USE_THEN "NEAR" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]]);;

let rec sch4n_labels ls =
  match ls with
    [l] -> LABEL_TAC l
  | l::t -> CONJUNCTS_THEN2 (LABEL_TAC l) (sch4n_labels t)
  | [] -> failwith "sch4n_labels";;

let sch4n_ctx_tac =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_setup] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_setup" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false));;

(* The gradient identity for box maps at points of K: n . D h = h$1. *)

let SCH4N_BOX_GRAD = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN c z0 w.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\
     z0 IN K /\ BN * abs(w$1) < d
     ==> (sch4n_box V N c z0 has_derivative
          frechet_derivative (sch4n_box V N c z0) (at w)) (at w) /\
         sch4n_box V N c z0 w IN W /\
         !h. G(sch4n_box V N c z0 w) dot frechet_derivative (sch4n_box V N c z0) (at w) h = h$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (sch4n_box (V:real^2->real^2) N c z0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH4N_BOX_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (sch4n_box (V:real^2->real^2) N c z0) (at w)` THEN
  SUBGOAL_THEN `(sch4n_box (V:real^2->real^2) N c z0 has_derivative D) (at w)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `c:real`; `z0:real^2`; `w:real^2`] SCH4N_BOX_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch4n_box (V:real^2->real^2) N c z0 w IN W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`sch4n_box (V:real^2->real^2) N c z0 w`;
       `ode_vf_flow (V:real^2->real^2) (:real^2) (lift(c * (w:real^2)$2)) z0`] o check (fun th ->
      can (term_match [] `!z y:real^2. y IN K /\ dist(y,z) < d ==> P z`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !w'. dist(w',w) < e ==> BN * abs((w':real^2)$1) < d`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(d - BN * abs((w:real^2)$1)) / (BN + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w':real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((w':real^2)$1) <= abs((w:real^2)$1) + dist(w',w)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`w' - w:real^2`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[dist; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`BN:real`; `d - BN * abs((w:real^2)$1)`; `dist(w':real^2,w)`] SCH4N_SPEED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_DIST] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIST] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `BN * (abs((w:real^2)$1) + dist(w',w))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `BN * dist(w':real^2,w) < d - BN * abs((w:real^2)$1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift((phi:real^2->real) x)) o sch4n_box (V:real^2->real^2) N c z0
                 has_derivative
                 (\h. lift((G:real^2->real^2)(sch4n_box V N c z0 w) dot h)) o D) (at w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^2. lift(x$1)) has_derivative
                 (\h. lift((G:real^2->real^2)(sch4n_box V N c z0 w) dot h)) o D) (at w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(\x. lift((phi:real^2->real) x)) o sch4n_box (V:real^2->real^2) N c z0` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w':real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; LIFT_EQ] THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `c:real`; `z0:real^2`; `w':real^2`] SCH4N_BOX_PHI) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^2. lift(x$1)) has_derivative (\x:real^2. lift(x$1))) (at w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. lift(x$1)`;
                 `(\h. lift((G:real^2->real^2)(sch4n_box V N c z0 w) dot h)) o (D:real^2->real^2)`;
                 `\x:real^2. lift(x$1)`; `w:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_EQ]);;

(* D(basis 2) <> 0: Psi_{-w1} o box o (line in direction basis 2) is a       *)
(* reparametrized trajectory of V, whose velocity is c V(k) <> 0.            *)

let SCH4N_BOX_TANGENT = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN c z0 w.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\
     z0 IN K /\ BN * abs(w$1) < d /\ ~(c = &0)
     ==> ~(frechet_derivative (sch4n_box V N c z0) (at w) (basis 2) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `c:real`; `z0:real^2`; `w:real^2`] SCH4N_BOX_GRAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `c:real`; `z0:real^2`; `w:real^2`] SCH4N_BOX_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = ode_vf_flow (V:real^2->real^2) (:real^2) (lift(c * (w:real^2)$2)) z0` THEN
  MP_TAC(ISPEC `V:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  MP_TAC(ISPEC `N:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["N0";"ND";"NG";"NS";"NDIFF"]) THEN
  ABBREV_TAC `D = frechet_derivative (sch4n_box (V:real^2->real^2) N c z0) (at w)` THEN
  DISCH_TAC THEN
  ABBREV_TAC `P = ode_vf_flow (N:real^2->real^2) (:real^2) (lift(--((w:real^2)$1)))` THEN
  SUBGOAL_THEN `(P:real^2->real^2) differentiable (at (sch4n_box V N c z0 w))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN EXPAND_TAC "P" THEN
    USE_THEN "NDIFF" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on]
      (SPEC `lift(--((w:real^2)$1))` th)]);
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (P:real^2->real^2) (at (sch4n_box V N c z0 w))` THEN
  SUBGOAL_THEN `linear(L:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t:real^1. (w:real^2) + drop t % basis 2) has_vector_derivative basis 2)
                (at (vec 0))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((P:real^2->real^2) o sch4n_box V N c z0 o (\t:real^1. (w:real^2) + drop t % basis 2)
                 has_vector_derivative vec 0) (at (vec 0))` ASSUME_TAC THENL
   [SUBGOAL_THEN `vec 0:real^2 = (L:real^2->real^2)((D:real^2->real^2)(basis 2))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH5_CHAIN_VECTOR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM; DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      EXPAND_TAC "L" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^2->real^2) o sch4n_box V N c z0 o (\t:real^1. (w:real^2) + drop t % basis 2) =
                (\s. ode_vf_flow V (:real^2) s z0) o (\t:real^1. lift(c * (w$2 + drop t)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; sch4n_box] THEN X_GEN_TAC `t:real^1` THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN EXPAND_TAC "P" THEN
    USE_THEN "NG" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM] THEN USE_THEN "N0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `((\s. ode_vf_flow (V:real^2->real^2) (:real^2) s z0) o
                 (\t:real^1. lift(c * ((w:real^2)$2 + drop t)))
                 has_vector_derivative drop(lift c) % V(k)) (at (vec 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\t:real^1. lift(c * ((w:real^2)$2 + drop t))) =
                    (\t. lift(c * w$2) + drop t % lift c)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      REWRITE_TAC[DROP_VEC; REAL_ADD_RID] THEN EXPAND_TAC "k" THEN
      USE_THEN "VD" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(lift c) % (V:real^2->real^2) k = vec 0` MP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(\s. ode_vf_flow (V:real^2->real^2) (:real^2) s z0) o
                (\t:real^1. lift(c * ((w:real^2)$2 + drop t)))` THEN
    EXISTS_TAC `vec 0:real^1` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `((P:real^2->real^2) o sch4n_box V N c z0 o
                    (\t:real^1. (w:real^2) + drop t % basis 2)
                    has_vector_derivative vec 0) (at (vec 0))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_EQ_0] THEN
  SUBGOAL_THEN `(V:real^2->real^2) k = sch4n_rot((G:real^2->real^2) k)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^2`; `k:real^2`] o check (fun th ->
      can (term_match [] `!z y:real^2. y IN K /\ dist(y,z) < d ==> P z`) (concl th))) THEN
    ASM_SIMP_TAC[DIST_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SCH4N_ROT_FACTS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2` o check (fun th ->
    can (term_match [] `!z:real^2. z IN K ==> phi z = &0 /\ P z`) (concl th))) THEN
  ASM_SIMP_TAC[]);;

let SCH4N_BOX_DET = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN c z0 w.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\
     z0 IN K /\ BN * abs(w$1) < d /\ ~(c = &0)
     ==> ~(det(matrix(frechet_derivative (sch4n_box V N c z0) (at w))) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `c:real`; `z0:real^2`; `w:real^2`] SCH4N_BOX_GRAD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SCH4N_DET2 THEN
  EXISTS_TAC `(G:real^2->real^2)(sch4n_box V N c z0 w)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SCH4N_BOX_TANGENT THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `K:real^2->bool`; `d0:real`; `d:real`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Near each point q of K, K is the local V-orbit of q, injectively. *)

let SCH4N_LOCAL_ARC = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN q.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ q IN K
     ==> ?U r. open U /\ q IN U /\ &0 < r /\ r <= &1 / &2 /\
               (!z. z IN K /\ z IN U
                    ==> ?u. abs u < r /\ z = ode_vf_flow V (:real^2) (lift u) q) /\
               (!u u'. abs u < r /\ abs u' < r /\
                       ode_vf_flow V (:real^2) (lift u) q = ode_vf_flow V (:real^2) (lift u') q
                       ==> u = u')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  MP_TAC(ISPEC `V:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  MP_TAC(ISPEC `N:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["N0";"ND";"NG";"NS";"NDIFF"]) THEN
  SUBGOAL_THEN `!u. sch4n_box (V:real^2->real^2) N (&1) q (u % basis 2) =
                    ode_vf_flow V (:real^2) (lift u) q` (LABEL_TAC "B2") THENL
   [GEN_TAC THEN REWRITE_TAC[sch4n_box] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_MUL_LID; LIFT_NUM] THEN
    USE_THEN "N0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `sch4n_box (V:real^2->real^2) N (&1) q (vec 0) = q` ASSUME_TAC THENL
   [MP_TAC(SPEC `&0` (ASSUME `!u. sch4n_box (V:real^2->real^2) N (&1) q (u % basis 2) =
                                   ode_vf_flow V (:real^2) (lift u) q`)) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; LIFT_NUM] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "V0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch4n_box (V:real^2->real^2) N (&1) q`; `(:real^2)`; `vec 0:real^2`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH4N_BOX_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH4N_BOX_DET THEN
      MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                            `K:real^2->bool`; `d0:real`; `d:real`; `BV:real`; `BN:real`] THEN
      ASM_REWRITE_TAC[VEC_COMPONENT; REAL_ABS_NUM; REAL_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^2->bool` (X_CHOOSE_THEN `U0:real^2->bool`
    (X_CHOOSE_THEN `binv:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `vec 0:real^2` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(T0:real^2->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min (&1 / &2) (min e (d / (BN + &1)))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 / &2 /\ r <= e /\ r <= d / (BN + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    SUBGOAL_THEN `&0 < d / (BN + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^2,r) SUBSET T0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^2,e)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. w IN ball(vec 0,r) ==> BN * abs(w$1) < d` (LABEL_TAC "WB") THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH4N_SPEED THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(w:real^2)` THEN REWRITE_TAC[COMPONENT_LE_NORM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (sch4n_box (V:real^2->real^2) N (&1) q) (ball(vec 0,r))` THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`T0:real^2->bool`; `U0:real^2->bool`;
                   `sch4n_box (V:real^2->real^2) N (&1) q`; `binv:real^2->real^2`;
                   `ball(vec 0:real^2,r)`] SCH5_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN SIMP_TAC[diffeomorphism_on];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `&1`; `q:real^2`; `w:real^2`] SCH4N_BOX_PHI) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "WB" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `(phi:real^2->real) z = &0` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
        can (term_match [] `!z:real^2. z IN K ==> phi z = &0 /\ P z`) (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH `a = &0 /\ a = b ==> b = &0`)) THEN
    EXISTS_TAC `(w:real^2)$2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(w:real^2)` THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN ASM_MESON_TAC[IN_BALL_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2) = w$2 % basis 2` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      USE_THEN "B2" (fun th -> REWRITE_TAC[th])];
    MAP_EVERY X_GEN_TAC [`u:real`; `u':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `u % basis 2:real^2 = u' % basis 2` MP_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on T0 U0 (sch4n_box (V:real^2->real^2) N (&1) q) binv` THEN
      REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(u % basis 2:real^2) IN T0 /\ (u' % basis 2:real^2) IN T0` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `ball(vec 0:real^2,r) SUBSET T0`)) THEN
        REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ASSUME `ode_vf_flow (V:real^2->real^2) (:real^2) (lift u) q =
                     ode_vf_flow V (:real^2) (lift u') q`) THEN
      MP_TAC(ASSUME `!x:real^2. x IN T0 ==> binv(sch4n_box (V:real^2->real^2) N (&1) q x) = x`) THEN
      MP_TAC(ASSUME `(u % basis 2:real^2) IN T0`) THEN MP_TAC(ASSUME `(u' % basis 2:real^2) IN T0`) THEN
      USE_THEN "B2" (fun th -> MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `u':real` th)) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* K is a single V-orbit, and that orbit is periodic with a                  *)
(* minimal period T:  Phi_t p = Phi_t' p iff t - t' IN T Z.                  *)
(* ------------------------------------------------------------------------- *)

let SCH4N_ORBIT = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ p IN K
     ==> !z. z IN K <=> ?t. z = ode_vf_flow V (:real^2) (lift t) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  MP_TAC(ISPEC `V:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  ABBREV_TAC `O = {z:real^2 | ?t. z = ode_vf_flow (V:real^2->real^2) (:real^2) (lift t) p}` THEN
  SUBGOAL_THEN `(O:real^2->bool) SUBSET K` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH4N_K_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `d0:real`; `d:real`; `N:real^2->real^2`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x u. x IN O ==> ode_vf_flow (V:real^2->real^2) (:real^2) (lift u) x IN O`
  (LABEL_TAC "OI") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `t + u:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "VG" (fun th -> REWRITE_TAC[th; LIFT_ADD]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^2->bool) = K` (fun th -> REWRITE_TAC[GSYM th] THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[IN_ELIM_THM]) THEN
  MP_TAC(ISPEC `K:real^2->bool` CONNECTED_CLOPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `O:real^2->bool`) THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q \/ r) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                     `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                     `BN:real`; `x:real^2`] SCH4N_LOCAL_ARC) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `K INTER (U:real^2->bool)` THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
        can (term_match [] `!z:real^2. z IN K /\ z IN U ==> ?u. abs u < r /\ P u z`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "OI" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `x:real^2`] SCH4N_LOCAL_ARC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `K INTER (U:real^2->bool)` THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      can (term_match [] `!z:real^2. z IN K /\ z IN U ==> ?u. abs u < r /\ P u z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((x:real^2) IN O)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^2 = ode_vf_flow (V:real^2->real^2) (:real^2) (lift(--u)) z`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "VG" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM] THEN
      USE_THEN "V0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "OI" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^2` THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[LIFT_NUM] THEN USE_THEN "V0" (fun th -> REWRITE_TAC[th])]);;

(* The orbit map is not injective: otherwise the times n of a convergent     *)
(* subsequence of Phi_n p would differ by less than 1 near the limit.        *)

let SCH4N_NONINJ = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ p IN K
     ==> ?t t'. ~(t = t') /\
                ode_vf_flow V (:real^2) (lift t) p = ode_vf_flow V (:real^2) (lift t') p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  MP_TAC(ISPEC `V:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  SUBGOAL_THEN `~(!t t'. ode_vf_flow (V:real^2->real^2) (:real^2) (lift t) p =
                         ode_vf_flow V (:real^2) (lift t') p ==> t = t')` MP_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(LABEL_TAC "INJ") THEN
  SUBGOAL_THEN `!n. ode_vf_flow (V:real^2->real^2) (:real^2) (lift(&n)) p IN K` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCH4N_K_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `d0:real`; `d:real`; `N:real^2->real^2`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `compact(K:real^2->bool)` THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. ode_vf_flow (V:real^2->real^2) (:real^2) (lift(&n)) p`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`] SCH4N_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` (LABEL_TAC "TAU" o SYM)) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `l:real^2`] SCH4N_LOCAL_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?M. !n. M <= n
                        ==> ode_vf_flow (V:real^2->real^2) (:real^2) (lift(&((r:num->num) n))) p IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `l:real^2` (REWRITE_RULE[OPEN_CONTAINS_BALL] (ASSUME `open(U:real^2->bool)`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `((\n. ode_vf_flow (V:real^2->real^2) (:real^2) (lift(&n)) p) o r --> l)
                 sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `ball(l:real^2,e) SUBSET U`)) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. M <= n ==> ?u. abs u < rho /\ &((r:num->num) n) = tau + u`
  (LABEL_TAC "TIMES") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ode_vf_flow (V:real^2->real^2) (:real^2) (lift(&((r:num->num) n))) p`
      o check (fun th ->
      can (term_match [] `!z:real^2. z IN K /\ z IN U ==> ?u. abs u < rho /\ P u z`) (concl th))) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TAU" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "VG" (fun th -> REWRITE_TAC[th; GSYM LIFT_ADD]);
    ALL_TAC] THEN
  USE_THEN "TIMES" (MP_TAC o SPEC `M:num`) THEN
  USE_THEN "TIMES" (MP_TAC o SPEC `SUC M`) THEN REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE `M <= SUC M`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:num->num) M < r (SUC M)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  SUBGOAL_THEN `&((r:num->num) M) + &1 <= &(r (SUC M))` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `(r:num->num) M < r (SUC M)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs u0 < rho` THEN UNDISCH_TAC `abs u1 < rho` THEN
  UNDISCH_TAC `rho <= &1 / &2` THEN REAL_ARITH_TAC);;

let SCH4N_INT_PERIOD = prove
 (`!(v:real^N->real^N) p Tp.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
     ode_vf_flow v (:real^N) (lift Tp) p = p
     ==> !k. integer k ==> ode_vf_flow v (:real^N) (lift(k * Tp)) p = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  SUBGOAL_THEN `!n. ode_vf_flow (v:real^N->real^N) (:real^N) (lift(&n * Tp)) p = p`
  (LABEL_TAC "NAT") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO; LIFT_NUM] THEN USE_THEN "V0" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID; LIFT_ADD] THEN
      USE_THEN "VG" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[ASSUME `ode_vf_flow (v:real^N->real^N) (:real^N) (lift(&n * Tp)) p = p`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  TRY(USE_THEN "NAT" MATCH_ACCEPT_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [GSYM(SPEC `n:num` (ASSUME `!n. ode_vf_flow (v:real^N->real^N) (:real^N) (lift(&n * Tp)) p = p`))] THEN
  USE_THEN "VG" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM LIFT_ADD; REAL_MUL_LNEG; REAL_ADD_RINV; LIFT_NUM] THEN
  USE_THEN "V0" (fun th -> REWRITE_TAC[th]));;

let SCH4N_FLOW_SHIFT = prove
 (`!(v:real^N->real^N) p t t'.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
     ==> (ode_vf_flow v (:real^N) (lift t) p = ode_vf_flow v (:real^N) (lift t') p <=>
          ode_vf_flow v (:real^N) (lift(t - t')) p = p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^N->real^N` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `ode_vf_flow (v:real^N->real^N) (:real^N) (lift(t - t')) p =
                  ode_vf_flow v (:real^N) (lift(--t')) (ode_vf_flow v (:real^N) (lift t) p)`
    SUBST1_TAC THENL
     [USE_THEN "VG" (fun th -> REWRITE_TAC[th; GSYM LIFT_ADD]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[ASSUME `ode_vf_flow (v:real^N->real^N) (:real^N) (lift t) p =
                          ode_vf_flow v (:real^N) (lift t') p`] THEN
      USE_THEN "VG" (fun th -> REWRITE_TAC[th; GSYM LIFT_ADD]) THEN
      REWRITE_TAC[REAL_ADD_RINV; LIFT_NUM] THEN USE_THEN "V0" (fun th -> REWRITE_TAC[th])];
    DISCH_TAC THEN
    SUBGOAL_THEN `ode_vf_flow (v:real^N->real^N) (:real^N) (lift t) p =
                  ode_vf_flow v (:real^N) (lift t') (ode_vf_flow v (:real^N) (lift(t - t')) p)`
    SUBST1_TAC THENL
     [USE_THEN "VG" (fun th -> REWRITE_TAC[th; GSYM LIFT_ADD]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[ASSUME `ode_vf_flow (v:real^N->real^N) (:real^N) (lift(t - t')) p = p`]]]);;

let SCH4N_PERIODIC = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p.
     sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ p IN K
     ==> ?Tp. &0 < Tp /\
              !t t'. ode_vf_flow V (:real^2) (lift t) p = ode_vf_flow V (:real^2) (lift t') p <=>
                     ?k. integer k /\ t - t' = k * Tp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN sch4n_ctx_tac THEN
  MP_TAC(ISPEC `V:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["V0";"VD";"VG";"VS";"VDIFF"]) THEN
  MP_TAC(ISPECL [`V:real^2->real^2`; `p:real^2`] SCH4N_FLOW_SHIFT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "SH") THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`] SCH4N_LOCAL_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2->bool` (X_CHOOSE_THEN `rho:real`
    (sch4n_labels ["UO";"PU";"RP";"RH";"ARC";"LINJ"]))) THEN
  SUBGOAL_THEN `!s. ode_vf_flow (V:real^2->real^2) (:real^2) (lift s) p = p /\ &0 < s ==> rho <= s`
  (LABEL_TAC "LB") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "LINJ" (MP_TAC o SPECL [`s:real`; `&0`]) THEN
    REWRITE_TAC[LIFT_NUM; REAL_SUB_RZERO;
                ASSUME `ode_vf_flow (V:real^2->real^2) (:real^2) (lift s) p = p`] THEN
    USE_THEN "V0" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `s < rho` THEN UNDISCH_TAC `&0 < rho` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = {s | rho <= s /\ ode_vf_flow (V:real^2->real^2) (:real^2) (lift s) p = p}` THEN
  SUBGOAL_THEN `~(P:real->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                   `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                   `BN:real`; `p:real^2`] SCH4N_NONINJ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(REAL_ARITH `t' < t \/ t < t' \/ t = t'`) THEN STRIP_TAC THENL
     [EXISTS_TAC `t - t':real`;
      EXISTS_TAC `t' - t:real`;
      ASM_MESON_TAC[]] THEN
    (SUBGOAL_THEN `ode_vf_flow (V:real^2->real^2) (:real^2) (lift(t - t')) p = p /\
                   ode_vf_flow V (:real^2) (lift(t' - t)) p = p` STRIP_ASSUME_TAC THENL
      [CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC;
         USE_THEN "SH" (fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC SYM_CONV THEN
         USE_THEN "SH" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `inf P IN (P:real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CLOSED_CONTAINS_INF THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM]] THEN
    REWRITE_TAC[REAL_CLOSED] THEN
    SUBGOAL_THEN `IMAGE lift P =
                  {x:real^1 | x$1 >= rho} INTER
                  {x | ode_vf_flow (V:real^2->real^2) (:real^2) x p IN {p}}` SUBST1_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_SING] THEN
      X_GEN_TAC `x:real^1` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; real_ge];
        STRIP_TAC THEN EXISTS_TAC `drop x` THEN
        ASM_REWRITE_TAC[LIFT_DROP; drop] THEN ASM_REWRITE_TAC[GSYM real_ge]];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN REWRITE_TAC[CLOSED_SING] THEN
    X_GEN_TAC `t0:real^1` THEN
    MP_TAC(ISPECL [`V:real^2->real^2`; `p:real^2`] SCH4N_FLOW_CONT) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `Tp = inf (P:real->bool)` THEN
  SUBGOAL_THEN `rho <= Tp /\ ode_vf_flow (V:real^2->real^2) (:real^2) (lift Tp) p = p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Tp:real) IN P` THEN EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN P ==> Tp <= s` (LABEL_TAC "TMIN") THENL
   [EXPAND_TAC "Tp" THEN
    MP_TAC(ISPEC `P:real->bool` INF) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `rho:real` THEN EXPAND_TAC "P" THEN
      SIMP_TAC[IN_ELIM_THM];
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `Tp:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `t':real`] THEN
  USE_THEN "SH" (fun th -> REWRITE_TAC[th]) THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `floor((t - t') / Tp)` THEN REWRITE_TAC[FLOOR] THEN
    ABBREV_TAC `k = floor((t - t') / Tp)` THEN
    ABBREV_TAC `q = (t - t') - k * Tp` THEN
    SUBGOAL_THEN `&0 <= q /\ q < Tp` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `(t - t') / Tp` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXPAND_TAC "q" THEN
      SUBGOAL_THEN `&0 < Tp` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `k <= (t - t') / Tp` THEN UNDISCH_TAC `(t - t') / Tp < k + &1` THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; ASSUME `&0 < Tp`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ode_vf_flow (V:real^2->real^2) (:real^2) (lift q) p = p` ASSUME_TAC THENL
     [SUBGOAL_THEN `lift q = lift(t - t') + lift(--k * Tp)` SUBST1_TAC THENL
       [EXPAND_TAC "q" THEN REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "VG" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[ASSUME `ode_vf_flow (V:real^2->real^2) (:real^2) (lift(t - t')) p = p`] THEN
      MP_TAC(ISPECL [`V:real^2->real^2`; `p:real^2`; `Tp:real`] SCH4N_INT_PERIOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(SPEC `(t - t') / Tp` FLOOR) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[INTEGER_NEG];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < q` THENL
     [SUBGOAL_THEN `(q:real) IN P` ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      USE_THEN "TMIN" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(q:real) IN P`))) THEN
      UNDISCH_TAC `q < Tp` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(&0 < q)` THEN UNDISCH_TAC `&0 <= q` THEN EXPAND_TAC "q" THEN
      REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^2->real^2`; `p:real^2`; `Tp:real`] SCH4N_INT_PERIOD) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Complex logarithm charts.  Near each x0 <> 0 the map                      *)
(* L x = clog(x / x0) + clog x0 is a holomorphic local inverse of cexp       *)
(* (a diffeomorphism onto its image), and Re(L x) = log |x|, Im(L x) = Arg x *)
(* + 2 n pi.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SCH4N_LOG_ARG = prove
 (`!z x. cexp z = x
         ==> Re z = log(norm x) /\ ?n. integer n /\ Im z = Arg x + &2 * n * pi`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[NORM_CEXP; LOG_EXP] THEN
  MP_TAC(SPEC `cexp z` ARG) THEN STRIP_TAC THEN
  SUBGOAL_THEN `cexp z = Cx(exp(Re z)) * cexp(ii * Cx(Arg(cexp z)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN REWRITE_TAC[NORM_CEXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx(Im z)) = cexp(ii * Cx(Arg(cexp z)))` MP_TAC THENL
   [MP_TAC(ISPECL [`Cx(exp(Re z))`; `cexp(ii * Cx(Im z))`; `cexp(ii * Cx(Arg(cexp z)))`]
      COMPLEX_EQ_MUL_LCANCEL) THEN
    REWRITE_TAC[CX_INJ; REAL_EXP_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
    REWRITE_TAC[CEXP_ADD; CX_EXP];
    ALL_TAC] THEN
  REWRITE_TAC[CEXP_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_MUL_CX; IM_II] THEN
  REWRITE_TAC[IM_CX; RE_MUL_CX; RE_II] THEN REAL_ARITH_TAC);;

let SCH4N_CLOG_CHART = prove
 (`!x0:complex.
     ~(x0 = Cx(&0))
     ==> ?U L'. open U /\ x0 IN U /\
                (!x. x IN U ==> ~(x = Cx(&0)) /\ cexp(clog(x / x0) + clog x0) = x) /\
                diffeomorphism_on U (IMAGE (\x. clog(x / x0) + clog x0) U)
                                  (\x. clog(x / x0) + clog x0) L'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = {x:complex | x / x0 IN ball(Cx(&1),&1)}` THEN
  SUBGOAL_THEN `!x:complex. x IN U ==> ~(x / x0 = Cx(&0)) /\ ~(x = Cx(&0))` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `dist(Cx(&1),x / x0) < &1` THEN
      ASM_REWRITE_TAC[dist; COMPLEX_SUB_RZERO; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[complex_div; COMPLEX_ENTIRE; COMPLEX_INV_EQ_0] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:complex. x IN U ==> cexp(clog(x / x0) + clog x0) = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CEXP_ADD] THEN
    ASM_SIMP_TAC[CEXP_CLOG] THEN ASM_SIMP_TAC[COMPLEX_DIV_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SUBGOAL_THEN `{x:complex | x / x0 IN ball(Cx(&1),&1)} =
                  {x | x IN (:complex) /\ (\x. x / x0) x IN ball(Cx(&1),&1)}` SUBST1_TAC THENL
     [REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_UNIV; OPEN_BALL] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[complex_div] THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:complex. clog(x / x0) + clog x0`; `U:complex->bool`]
    SCH2_HOLO_INJ_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      SUBGOAL_THEN `(\x:complex. clog(x / x0)) = clog o (\x. x / x0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC THENL
       [REWRITE_TAC[complex_div] THEN
        SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
        MATCH_MP_TAC HOLOMORPHIC_ON_CLOG THEN REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
        EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL; dist] THEN
        X_GEN_TAC `x:complex` THEN DISCH_TAC THEN DISCH_TAC THEN
        MP_TAC(SPEC `Cx(&1) - x / x0` COMPLEX_NORM_GE_RE_IM) THEN
        REWRITE_TAC[RE_SUB; RE_CX] THEN
        UNDISCH_TAC `norm(Cx(&1) - x / x0) < &1` THEN REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `cexp`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `L':complex->complex`) THEN
  MAP_EVERY EXISTS_TAC [`U:complex->bool`; `L':complex->complex`] THEN
  ASM_SIMP_TAC[] THEN EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[COMPLEX_DIV_REFL; CENTRE_IN_BALL; REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* The planar neck F(x) = box(c,p)(eps log|x|, Arg x) with                   *)
(* c = T/(2 pi): smooth and with invertible derivative (locally F = box o M  *)
(* o L with L a complex logarithm chart and M = diag(eps,1)), injective (phi *)
(* recovers |x|, the minimal period recovers Arg x), and F(sphere) = K.      *)
(* ------------------------------------------------------------------------- *)

let SCH4N_LOG_BOUND = prove
 (`!r. &1 / &2 < r /\ r < &2 ==> abs(log r) < &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv r < &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 = inv(&1 / &2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `r - &1` LOG_LE_STRONG) THEN
  MP_TAC(SPEC `inv r - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
  ASM_SIMP_TAC[LOG_INV; REAL_LT_INV_EQ] THEN
  UNDISCH_TAC `inv r < &2` THEN UNDISCH_TAC `r < &2` THEN REAL_ARITH_TAC);;

let SCH4N_JAC_CHAIN = prove
 (`!(f:real^N->real^N) (g:real^N->real^N) x.
     f differentiable at x /\ g differentiable at (f x)
     ==> det(jacobian (g o f) (at x)) = det(jacobian g (at (f x))) * det(jacobian f (at x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `frechet_derivative ((g:real^N->real^N) o (f:real^N->real^N)) (at x) =
                frechet_derivative g (at (f x)) o frechet_derivative f (at x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_FRECHET_DERIVATIVE; DET_MUL]);;

(* The linear map M = diag(eps, 1). *)

let SCH4N_MLIN = prove
 (`!e. linear (\z:real^2. vector[e * z$1; z$2]:real^2) /\
       det(matrix(\z:real^2. vector[e * z$1; z$2]:real^2)) = e /\
       smooth_map_on (:real^2) (\z:real^2. vector[e * z$1; z$2]:real^2)`,
  GEN_TAC THEN
  SUBGOAL_THEN `linear (\z:real^2. vector[e * z$1; z$2]:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[DET_2] THEN SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
    SIMP_TAC[VECTOR_2; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `\z:real^2. vector[e * z$1; z$2]:real^2`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF]]);;

let SCH4N_JAC_LOCAL = prove
 (`!(f:real^N->real^N) g U x.
     open U /\ x IN U /\ (!y. y IN U ==> f y = g y) /\ g differentiable at x
     ==> f differentiable at x /\ jacobian f (at x) = jacobian g (at x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^N` (REWRITE_RULE[OPEN_CONTAINS_BALL] (ASSUME `open(U:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `((f:real^N->real^N) has_derivative frechet_derivative g (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `g:real^N->real^N` THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(x:real^N,r) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN FIRST_ASSUM ACCEPT_TAC);;

(* The neck data and the neck map. *)

let sch4n_neckdata = new_definition
 `sch4n_neckdata (phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p Tp e <=>
    sch4n_setup phi G W K d0 /\ sch4n_fields G W K d V N BV BN /\ d <= d0 /\ p IN K /\
    &0 < Tp /\
    (!t t'. ode_vf_flow V (:real^2) (lift t) p = ode_vf_flow V (:real^2) (lift t') p <=>
            ?k. integer k /\ t - t' = k * Tp) /\
    &0 < e /\ BN * e < d`;;

let sch4n_fmap = new_definition
 `sch4n_fmap (V:real^2->real^2) (N:real^2->real^2) p Tp e (x:real^2) =
    sch4n_box V N (Tp / (&2 * pi)) p (vector[e * log(norm x); Arg x])`;;

let SCH4N_FMAP_PHI = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p Tp e x.
     sch4n_neckdata phi G W K d0 d V N BV BN p Tp e /\ x IN annulus (&1 / &2) (&2)
     ==> phi(sch4n_fmap V N p Tp e x) = e * log(norm x) /\
         BN * abs(e * log(norm x)) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch4n_neckdata; annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `BN * abs(e * log(norm(x:real^2))) < d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `BN * e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_MUL; REAL_ARITH `&0 < e ==> abs e = e`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SCH4N_LOG_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch4n_fmap] THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `Tp / (&2 * pi)`; `p:real^2`;
                 `vector[e * log(norm(x:real^2)); Arg x]:real^2`] SCH4N_BOX_PHI) THEN
  ASM_REWRITE_TAC[VECTOR_2] THEN SIMP_TAC[]);;

let SCH4N_FMAP_INJ = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p Tp e x y.
     sch4n_neckdata phi G W K d0 d V N BV BN p Tp e /\
     x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
     sch4n_fmap V N p Tp e x = sch4n_fmap V N p Tp e y
     ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`; `Tp:real`; `e:real`; `x:real^2`] SCH4N_FMAP_PHI) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`; `Tp:real`; `e:real`; `y:real^2`] SCH4N_FMAP_PHI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_neckdata] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_neckdata" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
  UNDISCH_TAC `(x:real^2) IN annulus (&1 / &2) (&2)` THEN
  UNDISCH_TAC `(y:real^2) IN annulus (&1 / &2) (&2)` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(x:real^2) = norm(y:real^2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(norm(x:real^2)) = log(norm(y:real^2))` MP_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `&0 < e /\ e * a = e * b ==> a = b`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN MATCH_MP_TAC LOG_INJ THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `N:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["N0";"ND";"NG";"NS";"NDIFF"]) THEN
  SUBGOAL_THEN `ode_vf_flow (V:real^2->real^2) (:real^2) (lift(Tp / (&2 * pi) * Arg x)) p =
                ode_vf_flow V (:real^2) (lift(Tp / (&2 * pi) * Arg y)) p` MP_TAC THENL
   [UNDISCH_TAC `sch4n_fmap V N p Tp e x = sch4n_fmap V N p Tp e (y:real^2)` THEN
    ASM_REWRITE_TAC[sch4n_fmap; sch4n_box; VECTOR_2] THEN
    DISCH_THEN(MP_TAC o AP_TERM `ode_vf_flow (N:real^2->real^2) (:real^2)
                                   (lift(--(e * log(norm(y:real^2)))))`) THEN
    USE_THEN "NG" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM] THEN
    USE_THEN "N0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> can (term_match []
    `!t t'. ode_vf_flow (V:real^2->real^2) (:real^2) (lift t) p =
            ode_vf_flow V (:real^2) (lift t') p <=> Q t t'`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `Arg(x:real^2) - Arg(y:real^2) = &2 * k * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN UNDISCH_TAC `&0 < Tp` THEN
    UNDISCH_TAC `Tp / (&2 * pi) * Arg(x:real^2) - Tp / (&2 * pi) * Arg(y:real^2) = k * Tp` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPEC `k:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONJUNCT1(SPEC `x:real^2` ARG)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPEC `x:real^2` ARG))) THEN
    MP_TAC(CONJUNCT1(SPEC `y:real^2` ARG)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPEC `y:real^2` ARG))) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(&2 * k * pi) < &2 * pi` MP_TAC THENL
     [FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
        lhand(concl th) = `Arg(x:real^2) - Arg(y:real^2)`)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
    MATCH_MP_TAC(REAL_ARITH `&2 * pi <= x ==> ~(x < &2 * pi)`) THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&2 * pi = &2 * &1 * pi`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Arg(x:real^2) = Arg(y:real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `Arg(x:real^2) - Arg(y:real^2) = &2 * k * pi` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARG] THEN ASM_REWRITE_TAC[]);;

let SCH4N_FMAP_IMAGE = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p Tp e.
     sch4n_neckdata phi G W K d0 d V N BV BN p Tp e
     ==> IMAGE (sch4n_fmap V N p Tp e) (sphere(vec 0,&1)) = K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_neckdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
  MP_TAC(ISPEC `N:real^2->real^2` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(sch4n_labels ["N0";"ND";"NG";"NS";"NDIFF"]) THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1)
                ==> sch4n_fmap V N p Tp e x =
                    ode_vf_flow (V:real^2->real^2) (:real^2) (lift(Tp / (&2 * pi) * Arg x)) p`
  (LABEL_TAC "S1") THENL
   [REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[sch4n_fmap; sch4n_box; VECTOR_2] THEN
    REWRITE_TAC[ASSUME `norm(x:real^2) = &1`; LOG_1; REAL_MUL_RZERO; LIFT_NUM] THEN
    USE_THEN "N0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_IMAGE] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    USE_THEN "S1" (fun th -> ASM_REWRITE_TAC[MATCH_MP th
      (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)]) THEN
    MATCH_MP_TAC SCH4N_K_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `d0:real`; `d:real`; `N:real^2->real^2`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`] SCH4N_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
  ABBREV_TAC `k = floor(t / Tp)` THEN
  SUBGOAL_THEN `integer k` ASSUME_TAC THENL [EXPAND_TAC "k" THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  ABBREV_TAC `th = (&2 * pi) * (t - k * Tp) / Tp` THEN
  SUBGOAL_THEN `&0 <= th /\ th < &2 * pi /\ Tp / (&2 * pi) * th = t - k * Tp` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t / Tp` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC PI_POS THEN DISCH_TAC THEN EXPAND_TAC "th" THEN
    SUBGOAL_THEN `&0 <= t - k * Tp /\ t - k * Tp < Tp` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `k <= t / Tp` THEN UNDISCH_TAC `t / Tp < k + &1` THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; ASSUME `&0 < Tp`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < pi` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < pi` THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID]];
      UNDISCH_TAC `&0 < pi` THEN UNDISCH_TAC `&0 < Tp` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `cexp(ii * Cx th)` THEN
  SUBGOAL_THEN `cexp(ii * Cx th) IN sphere(vec 0,&1) /\ Arg(cexp(ii * Cx th)) = th`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0] THEN
    MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  USE_THEN "S1" (fun th0 -> REWRITE_TAC[MATCH_MP th0
    (ASSUME `cexp(ii * Cx th) IN sphere(vec 0,&1)`)]) THEN
  REWRITE_TAC[ASSUME `Arg(cexp(ii * Cx th)) = th`;
              ASSUME `Tp / (&2 * pi) * th = t - k * Tp`] THEN
  FIRST_ASSUM((fun th0 -> REWRITE_TAC[th0]) o check (fun th0 -> can (term_match []
    `!t t'. ode_vf_flow (V:real^2->real^2) (:real^2) (lift t) p =
            ode_vf_flow V (:real^2) (lift t') p <=> Q t t'`) (concl th0))) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Locally F = box o M o L with L a logarithm chart: F is smooth with        *)
(* invertible derivative.                                                    *)

let SCH4N_FMAP_LOCAL = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0 d V N BV BN p Tp e x0.
     sch4n_neckdata phi G W K d0 d V N BV BN p Tp e /\ x0 IN annulus (&1 / &2) (&2)
     ==> ?U. open U /\ x0 IN U /\ smooth_map_on U (sch4n_fmap V N p Tp e) /\
             ~(det(jacobian (sch4n_fmap V N p Tp e) (at x0)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`; `Tp:real`; `e:real`; `x0:real^2`] SCH4N_FMAP_PHI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_neckdata] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_neckdata" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sch4n_fields] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "sch4n_fields" with Failure _ -> false)) THEN
  SUBGOAL_THEN `~(x0 = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^2) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_VEC_0] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&1 / &2 < &0)`];
    ALL_TAC] THEN
  MP_TAC(SPEC `x0:complex` SCH4N_CLOG_CHART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:complex->bool` (X_CHOOSE_THEN `L':complex->complex`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `B = sch4n_box (V:real^2->real^2) N (Tp / (&2 * pi)) p` THEN
  SUBGOAL_THEN `!x. x IN U0 INTER annulus (&1 / &2) (&2)
                    ==> sch4n_fmap V N p Tp e x =
                        ((B:real^2->real^2) o (\z:real^2. vector[e * z$1; z$2]:real^2) o
                         (\x:complex. clog(x / (x0:complex)) + clog x0)) x` (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`clog(x / x0) + clog x0`; `x:real^2`] SCH4N_LOG_ARG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[RE_DEF; IM_DEF] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN REWRITE_TAC[sch4n_fmap; sch4n_box; VECTOR_2] THEN
    AP_TERM_TAC THEN
    FIRST_ASSUM((fun th0 -> REWRITE_TAC[th0]) o check (fun th0 -> can (term_match []
      `!t t'. ode_vf_flow (V:real^2->real^2) (:real^2) (lift t) p =
              ode_vf_flow V (:real^2) (lift t') p <=> Q t t'`) (concl th0))) THEN
    EXISTS_TAC `--n:real` THEN ASM_SIMP_TAC[INTEGER_NEG] THEN
    MP_TAC PI_POS THEN UNDISCH_TAC `&0 < Tp` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (B:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC SCH4N_BOX_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U0 (\x:complex. clog(x / (x0:complex)) + clog x0)` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on U0 (IMAGE (\x:complex. clog(x / (x0:complex)) + clog x0) U0)
                   (\x:complex. clog(x / (x0:complex)) + clog x0) L'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MP_TAC(SPEC `e:real` SCH4N_MLIN) THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U0 ((B:real^2->real^2) o (\z:real^2. vector[e * z$1; z$2]:real^2) o
                                 (\x:complex. clog(x / (x0:complex)) + clog x0))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(U0:complex->bool) INTER annulus (&1 / &2) (&2)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_ANNULUS; IN_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(B:real^2->real^2) o (\z:real^2. vector[e * z$1; z$2]:real^2) o
                (\x:complex. clog(x / (x0:complex)) + clog x0)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "EQ" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U0:complex->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((B:real^2->real^2) o (\z:real^2. vector[e * z$1; z$2]:real^2) o
                 (\x:complex. clog(x / (x0:complex)) + clog x0)) differentiable at x0 /\
                (\x:complex. clog(x / (x0:complex)) + clog x0) differentiable at x0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U0:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch4n_fmap (V:real^2->real^2) N p Tp e`;
                 `(B:real^2->real^2) o (\z:real^2. vector[e * z$1; z$2]:real^2) o
                  (\x:complex. clog(x / (x0:complex)) + clog x0)`;
                 `(U0:complex->bool) INTER annulus (&1 / &2) (&2)`; `x0:real^2`]
    SCH4N_JAC_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_ANNULUS; IN_INTER] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER];
    DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`(\z:real^2. vector[e * z$1; z$2]:real^2) o
                  (\x:complex. clog(x / (x0:complex)) + clog x0)`; `B:real^2->real^2`;
                 `x0:real^2`] SCH4N_JAC_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `U0:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\x:complex. clog(x / (x0:complex)) + clog x0`;
                 `\z:real^2. vector[e * z$1; z$2]:real^2`; `x0:real^2`] SCH4N_JAC_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `!z. jacobian (\z:real^2. vector[e * z$1; z$2]:real^2) (at z) =
                    matrix(\z:real^2. vector[e * z$1; z$2]:real^2)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[o_THM; jacobian] THEN EXPAND_TAC "B" THEN
    MATCH_MP_TAC SCH4N_BOX_DET THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                          `K:real^2->bool`; `d0:real`; `d:real`; `BV:real`; `BN:real`] THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`clog(x0 / x0) + clog(x0:complex)`; `x0:real^2`] SCH4N_LOG_ARG) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[RE_DEF] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MP_TAC PI_POS THEN UNDISCH_TAC `&0 < Tp` THEN CONV_TAC REAL_FIELD];
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SCH2_DIFFEO_DET_NZ THEN
    MAP_EVERY EXISTS_TAC [`L':complex->complex`; `U0:complex->bool`;
                          `IMAGE (\x:complex. clog(x / (x0:complex)) + clog x0) U0`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The planar neck theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let SCH4N_PLANAR_NECK = prove
 (`!(phi:real^2->real) (G:real^2->real^2) W K d0.
     sch4n_setup phi G W K d0
     ==> ?F F'. sch_neck F F' /\ IMAGE F (sphere(vec 0,&1)) = K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH4N_FIELDS_EXIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `V:real^2->real^2`
    (X_CHOOSE_THEN `N:real^2->real^2` (X_CHOOSE_THEN `BV:real`
    (X_CHOOSE_THEN `BN:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `?p:real^2. p IN K` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch4n_setup (phi:real^2->real) (G:real^2->real^2) W K d0` THEN
    REWRITE_TAC[sch4n_setup; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`; `K:real^2->bool`;
                 `d0:real`; `d:real`; `V:real^2->real^2`; `N:real^2->real^2`; `BV:real`;
                 `BN:real`; `p:real^2`] SCH4N_PERIODIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Tp:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < d /\ &0 < BN` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch4n_fields (G:real^2->real^2) W K d V N BV BN` THEN
    REWRITE_TAC[sch4n_fields] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = d / (BN + &1) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ BN * e < d` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < d / (BN + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`BN:real`; `d:real`; `e:real`] SCH4N_SPEED) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&0 < e ==> abs e = e`] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch4n_neckdata phi G W K d0 d V N BV BN p Tp e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch4n_neckdata]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sch4n_fmap (V:real^2->real^2) N p Tp e`;
                 `annulus (&1 / &2) (&2):real^2->bool`] SCHI_INJ_DIFFEO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_ANNULUS] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                     `K:real^2->bool`; `d0:real`; `d:real`; `V:real^2->real^2`;
                     `N:real^2->real^2`; `BV:real`; `BN:real`; `p:real^2`; `Tp:real`;
                     `e:real`; `x:real^2`] SCH4N_FMAP_LOCAL) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      MATCH_MP_TAC SCH4N_FMAP_INJ THEN
      MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                            `K:real^2->bool`; `d0:real`; `d:real`; `V:real^2->real^2`;
                            `N:real^2->real^2`; `BV:real`; `BN:real`; `p:real^2`; `Tp:real`;
                            `e:real`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                     `K:real^2->bool`; `d0:real`; `d:real`; `V:real^2->real^2`;
                     `N:real^2->real^2`; `BV:real`; `BN:real`; `p:real^2`; `Tp:real`;
                     `e:real`; `x:real^2`] SCH4N_FMAP_LOCAL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM jacobian]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `F':real^2->real^2`) THEN
  MAP_EVERY EXISTS_TAC [`sch4n_fmap (V:real^2->real^2) N p Tp e`; `F':real^2->real^2`] THEN
  ASM_REWRITE_TAC[sch_neck] THEN
  MATCH_MP_TAC SCH4N_FMAP_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `G:real^2->real^2`; `W:real^2->bool`;
                        `d0:real`; `d:real`; `BV:real`; `BN:real`] THEN
  ASM_REWRITE_TAC[]);;

