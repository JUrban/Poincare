(* ========================================================================= *)
(* Unit pc_p2c_gauge (Part 2C): MT Lemma 5.7, the gauge of Cheeger-Gromov    *)
(* compactness.  In normal coordinates (the pullback cmp_expmetric of g by w *)
(* |-> exp_x(E w) on a tangent ball) the metric is bounded in C^k by the     *)
(* bounds on |nabla^l Rm|, l <= k (P2C_GAUGE_STATEMENT).  Route: coordinate  *)
(* derivatives d = lnabla with the flat metric p2c_flat; Phi = (1/2) D_X G   *)
(* and the radial equations (j + D_X) d^j G = 2 d^j Phi, (1 + j + D_X) d^j   *)
(* Phi = d^j S; the radial lemma; general-order Leibniz bounds; conversion   *)
(* between d^j and nabla^j (P2C_CONN_DIFF with G0 = p2c_flat); a bootstrap   *)
(* at each order.  The C^0 part is CMP_EXP_PULLBACK of pc_cmp_pull.          *)
(*                                                                           *)
(* Main theorem: P2C_GAUGE |- !u. P2C_GAUGE_STATEMENT u (the statement       *)
(* constant is in pc_p2c_iface); local form P2C_GAUGE_LOCAL.                 *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_cmp_pull.ml";;
needs "src/pc_lrg_flowsmooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The flat metric, coordinate derivatives and Euclidean norms.              *)
(* ------------------------------------------------------------------------- *)

let p2c_flat = new_definition
 `p2c_flat = (\z:real^N. mat 1:real^N^N)`;;

let P2C_FLAT_METRIC_FIELD = prove
 (`!U:real^N->bool. open U ==> metric_field U p2c_flat`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field; p2c_flat] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST];
    REWRITE_TAC[TRANSP_MAT; MATRIX_VECTOR_MUL_LID] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DOT_POS_LT]]);;

let P2C_FLAT_CHRISTOFFEL = prove
 (`!y a b:real^N. christoffel (p2c_flat:real^N->real^N^N) y a b = vec 0`,
  REWRITE_TAC[p2c_flat; LRG_CHRISTOFFEL_CONST]);;

let P2C_FLAT_LNABLA = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u.
     ltensor_field k U tf /\ y IN U
     ==> lnabla k p2c_flat tf y u =
         drop(frechet_derivative (\z. lift(tf z u)) (at y) (u(k + 1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; P2C_FLAT_CHRISTOFFEL] THEN
  MATCH_MP_TAC(REAL_ARITH `s = &0 ==> d - s = d`) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]);;

let P2C_FLAT_LTNORM2 = prove
 (`!k U (tf:real^N->(num->real^N)->real) y.
     ltensor_field k U tf /\ y IN U
     ==> ltnorm2 k p2c_flat tf y =
         sum (index_tuples k (:N)) (\p. (tf y (\m. basis(p m))) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `mat 1:real^N^N`]
                LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[p2c_flat; MATRIX_INV_I; TRANSP_MAT; MATRIX_MUL_LID;
                  MATRIX_VECTOR_MUL_LID]);;

(* Comparison of the Euclidean and G norms when 1/2 <= G <= 2. *)

let P2C_FLAT_COMPARE = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\
     (!a. inv(&2) * (a dot a) <= a dot (G y ** a) /\ a dot (G y ** a) <= &2 * (a dot a))
     ==> ltnorm2 k p2c_flat tf y <= &2 pow k * ltnorm2 k G tf y /\
         ltnorm2 k G tf y <= &2 pow k * ltnorm2 k p2c_flat tf y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^N->bool` P2C_FLAT_METRIC_FIELD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &2`; p2c_flat; MATRIX_VECTOR_MUL_LID];
    MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &2`; p2c_flat; MATRIX_VECTOR_MUL_LID] THEN
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN REAL_ARITH_TAC]);;

(* Fields of the flat derivatives. *)

let P2C_FLAT_FIELD = prove
 (`!k U (tf:real^N->(num->real^N)->real).
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field (k + 1) U (lnabla k p2c_flat tf) /\
         (!u. smooth_map_on U (\y. lift(lnabla k p2c_flat tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD]);;

(* Symmetry of second flat derivatives in the last two slots. *)

let P2C_FLAT_SYM2 = prove
 (`!k U (tf:real^N->(num->real^N)->real) z w.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\ z IN U
     ==> lnabla (k + 1) p2c_flat (lnabla k p2c_flat tf) z w =
         lnabla (k + 1) p2c_flat (lnabla k p2c_flat tf) z
           (\m. if m = k + 1 then w(k + 2) else if m = k + 2 then w(k + 1) else w m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                 `lnabla k p2c_flat (tf:real^N->(num->real^N)->real)`;
                 `z:real^N`; `w:num->real^N`] P2C_FLAT_LNABLA) THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                 `lnabla k p2c_flat (tf:real^N->(num->real^N)->real)`; `z:real^N`;
                 `\m. if m = k + 1 then (w:num->real^N)(k + 2)
                      else if m = k + 2 then w(k + 1) else w m`] P2C_FLAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`; ARITH_RULE `~(k + 2 = k + 1)`] THEN
  ABBREV_TAC `f = \x:real^N. lift((tf:real^N->(num->real^N)->real) x w)` THEN
  SUBGOAL_THEN
   `!v. (!m. 1 <= m /\ m <= k ==> v m = (w:num->real^N) m)
        ==> !x. x IN U
                ==> lift(lnabla k p2c_flat tf x v) =
                    frechet_derivative (f:real^N->real^1) (at x) (v(k + 1))`
  (LABEL_TAC "inner") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                   `x:real^N`; `v:num->real^N`] P2C_FLAT_LNABLA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    AP_TERM_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift(lnabla k p2c_flat tf x w)) (at z) =
    frechet_derivative (\x. frechet_derivative (f:real^N->real^1) (at x) (w(k + 1)))
                       (at z) /\
    frechet_derivative (\x. lift(lnabla k p2c_flat tf x
       (\m. if m = k + 1 then w(k + 2) else if m = k + 2 then w(k + 1) else w m))) (at z) =
    frechet_derivative (\x. frechet_derivative (f:real^N->real^1) (at x) (w(k + 2)))
                       (at z)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN BETA_TAC THENL
     [USE_THEN "inner" (MP_TAC o SPEC `w:num->real^N`) THEN REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "inner" (MP_TAC o SPEC
        `\m. if m = k + 1 then (w:num->real^N)(k + 2) else if m = k + 2 then w(k + 1)
             else w m`) THEN
      ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN `~(m = k + 1) /\ ~(m = k + 2)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN
  ASM_REWRITE_TAC[]);;

(* Iterated flat derivatives are smooth tensor fields; Euclidean norms are   *)
(* nonnegative and dominate each squared component.                          *)

let P2C_FLAT_ITER_FIELD = prove
 (`!k U (tf:real^N->(num->real^N)->real).
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> !l. ltensor_field (k + l) U (lnabla_iter k l p2c_flat tf) /\
             (!u. smooth_map_on U (\y. lift(lnabla_iter k l p2c_flat tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LRG_LNABLA_ITER_FIELD THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD]);;

let P2C_FLAT_LTNORM2_POS = prove
 (`!k U (tf:real^N->(num->real^N)->real) y.
     ltensor_field k U tf /\ y IN U ==> &0 <= ltnorm2 k p2c_flat tf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`]
                P2C_FLAT_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE; REAL_LE_POW_2]);;

let P2C_FLAT_COMP_LE = prove
 (`!k U (tf:real^N->(num->real^N)->real) y p.
     ltensor_field k U tf /\ y IN U /\ p IN index_tuples k (:N)
     ==> (tf y (\m. basis(p m))) pow 2 <= ltnorm2 k p2c_flat tf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `y:real^N`]
                P2C_FLAT_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`{p:num->num}`; `index_tuples k (:N)`;
                 `\p:num->num. ((tf:real^N->(num->real^N)->real) y (\m. basis(p m))) pow 2`]
                SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; LRG_INDEX_TUPLES_FINITE; REAL_LE_POW_2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SING_SUBSET]);;

(* Expansion of a slot in the standard basis. *)

let P2C_SLOT_EXPAND = prove
 (`!k U (sf:real^N->(num->real^N)->real) z u i v.
     ltensor_field k U sf /\ z IN U /\ 1 <= i /\ i <= k
     ==> sf z (\m. if m = i then v else u m) =
         sum(1..dimindex(:N)) (\c. v$c * sf z (\m. if m = i then basis c else u m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\v. lift((sf:real^N->(num->real^N)->real) z
                                   (\m. if m = i then v else u m)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ltensor_field k U (sf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v. lift((sf:real^N->(num->real^N)->real) z
                                (\m. if m = i then v else u m))`;
                 `1..dimindex(:N)`; `\c:num. (v:real^N)$c`; `basis:num->real^N`]
                LINEAR_VSUM_MUL) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; BASIS_EXPANSION] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[LIFT_DROP; DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The radial derivative D T = (d T)(.., z) of a tensor field               *)
(* (the Euler operator), its expansion, and the commutation rule            *)
(* d (D T) = D (d T) + d T, iterated: d^j (D T) = D (d^j T) + j d^j T.       *)
(* ------------------------------------------------------------------------- *)

let p2c_dx = new_definition
 `p2c_dx k (tf:real^N->(num->real^N)->real) =
    \z u. lnabla k p2c_flat tf z (\m. if m = k + 1 then z else u m)`;;

let P2C_DX_EXPAND = prove
 (`!k U (tf:real^N->(num->real^N)->real) z u.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\ z IN U
     ==> p2c_dx k tf z u =
         sum(1..dimindex(:N))
          (\c. z$c * lnabla k p2c_flat tf z (\m. if m = k + 1 then basis c else u m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dx] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2C_SLOT_EXPAND THEN
  MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let P2C_DX_COMP = prove
 (`!k U (tf:real^N->(num->real^N)->real) z u.
     open U /\ ltensor_field k U tf /\ z IN U
     ==> p2c_dx k tf z u = drop(frechet_derivative (\x. lift(tf x u)) (at z) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dx] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `z:real^N`;
                 `\m. if m = k + 1 then z else (u:num->real^N) m`] P2C_FLAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let P2C_DX_FIELD = prove
 (`!k U (tf:real^N->(num->real^N)->real).
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field k U (p2c_dx k tf) /\
         (!u. smooth_map_on U (\y. lift(p2c_dx k tf y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field; p2c_dx] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
      MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!v:real^N. (\m. if m = k + 1 then y else if m = i then v else (u:num->real^N) m) =
                 (\j. if j = i then v else if j = k + 1 then y else u j)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m = k + 1` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(k + 1 = i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `ltensor_field (k + 1) U (lnabla k p2c_flat (tf:real^N->(num->real^N)->real))` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `\m. if m = k + 1 then y else (u:num->real^N) m`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. lift(sum(1..dimindex(:N))
     (\c. y$c * lnabla k p2c_flat (tf:real^N->(num->real^N)->real) y
                  (\m. if m = k + 1 then basis c else (u:num->real^N) m)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2C_DX_EXPAND THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE]]);;

let P2C_TUPLE_TAC =
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC) THEN ASM_ARITH_TAC;;

let P2C_DX_COMM = prove
 (`!k U (tf:real^N->(num->real^N)->real) z u.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\ z IN U
     ==> lnabla k p2c_flat (p2c_dx k tf) z u =
         p2c_dx (k + 1) (lnabla k p2c_flat tf) z u + lnabla k p2c_flat tf z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                 `lnabla k p2c_flat (tf:real^N->(num->real^N)->real)`] P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_DX_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `p2c_dx k (tf:real^N->(num->real^N)->real)`;
                 `z:real^N`; `u:num->real^N`] P2C_FLAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift(p2c_dx k (tf:real^N->(num->real^N)->real) x u)) (at z) =
    (\h. vsum(1..dimindex(:N))
          (\c. z$c % frechet_derivative
                       (\x. lift(lnabla k p2c_flat tf x
                                   (\m. if m = k + 1 then basis c else (u:num->real^N) m)))
                       (at z) h +
               h$c % lift(lnabla k p2c_flat tf z
                            (\m. if m = k + 1 then basis c else u m))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `frechet_derivative
        (\x. vsum(1..dimindex(:N))
          (\c. x$c % lift(lnabla k p2c_flat (tf:real^N->(num->real^N)->real) x
                            (\m. if m = k + 1 then basis c else (u:num->real^N) m))))
        (at z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                     `x:real^N`; `u:num->real^N`] P2C_DX_EXPAND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. x$c`; `\h:real^N. h$c`;
                   `\x. lift(lnabla k p2c_flat (tf:real^N->(num->real^N)->real) x
                               (\m. if m = k + 1 then basis c else (u:num->real^N) m))`;
                   `frechet_derivative
                      (\x. lift(lnabla k p2c_flat (tf:real^N->(num->real^N)->real) x
                               (\m. if m = k + 1 then basis c else (u:num->real^N) m))) (at z)`;
                   `z:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN BINOP_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                   `lnabla k p2c_flat (tf:real^N->(num->real^N)->real)`;
                   `z:real^N`; `u:num->real^N`; `k + 1`; `(u:num->real^N)(k + 1)`]
                  P2C_SLOT_EXPAND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`; LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN P2C_TUPLE_TAC] THEN
  SUBGOAL_THEN
   `!c. drop(frechet_derivative
          (\x. lift(lnabla k p2c_flat (tf:real^N->(num->real^N)->real) x
                      (\m. if m = k + 1 then basis c else (u:num->real^N) m)))
          (at z) (u(k + 1))) =
        lnabla (k + 1) p2c_flat (lnabla k p2c_flat tf) z
          (\m. if m = k + 1 then basis c else if m = k + 2 then u(k + 1) else u m)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `c:num` THEN
    MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`;
                   `lnabla k p2c_flat (tf:real^N->(num->real^N)->real)`; `z:real^N`;
                   `\m. if m = k + 1 then basis c else if m = k + 2 then (u:num->real^N)(k + 1)
                        else u m`] P2C_FLAT_LNABLA) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`; ARITH_RULE `~(k + 2 = k + 1)`] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
    MAP_EVERY EXISTS_TAC [`k + 1`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`;
                 `lnabla (k + 1) p2c_flat (lnabla k p2c_flat (tf:real^N->(num->real^N)->real))`;
                 `z:real^N`;
                 `\m. if m = k + 2 then (u:num->real^N)(k + 1) else u m`; `k + 1`; `z:real^N`]
                P2C_SLOT_EXPAND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1 /\ k + 1 <= k + 2`] THEN
    UNDISCH_TAC `ltensor_field ((k + 1) + 1) U
                   (lnabla (k + 1) p2c_flat (lnabla k p2c_flat
                     (tf:real^N->(num->real^N)->real)))` THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`; `z:real^N`;
                 `\m. if m = k + 1 then z else if m = k + 2 then (u:num->real^N)(k + 1)
                      else u m`] P2C_FLAT_SYM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2c_dx] THEN AP_TERM_TAC THEN P2C_TUPLE_TAC);;

let P2C_DX_COMM_ITER = prove
 (`!k U (tf:real^N->(num->real^N)->real).
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> !j z u. z IN U
                 ==> lnabla_iter k j p2c_flat (p2c_dx k tf) z u =
                     p2c_dx (k + j) (lnabla_iter k j p2c_flat tf) z u +
                     &j * lnabla_iter k j p2c_flat tf z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_DX_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla_iter] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  ABBREV_TAC `Tj = lnabla_iter k j p2c_flat (tf:real^N->(num->real^N)->real)` THEN
  MP_TAC(ISPECL [`k + j:num`; `U:real^N->bool`; `Tj:real^N->(num->real^N)->real`]
                P2C_DX_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lnabla (k + j) p2c_flat (lnabla_iter k j p2c_flat (p2c_dx k tf)) z u =
    lnabla (k + j) p2c_flat
      (\x u. p2c_dx (k + j) (Tj:real^N->(num->real^N)->real) x u +
             (\x u. &j * Tj x u) x u) z u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + j:num`; `p2c_flat:real^N->real^N^N`;
                 `p2c_dx (k + j) (Tj:real^N->(num->real^N)->real)`;
                 `\x u. &j * (Tj:real^N->(num->real^N)->real) x u`; `z:real^N`; `u:num->real^N`]
                LRG_LNABLA_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `&j`;
                   `\x. lift((Tj:real^N->(num->real^N)->real) x u)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k + j:num`; `p2c_flat:real^N->real^N^N`; `Tj:real^N->(num->real^N)->real`;
                 `&j`; `z:real^N`; `u:num->real^N`] LRG_LNABLA_CMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k + j:num`; `U:real^N->bool`; `Tj:real^N->(num->real^N)->real`; `z:real^N`;
                 `u:num->real^N`] P2C_DX_COMM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `k + SUC j = (k + j) + 1`; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The radial estimate.  If (p + D) T = H on a ball centred at               *)
(* the origin (p >= 1), then along the segment from t0 u to u the function  *)
(* s^p T(s u) has derivative s^(p-1) H(s u), so                              *)
(* |T(u)| <= t0^p |T(t0 u)| + (1 - t0) sup |H| (componentwise, by the mean   *)
(* value theorem), and in Euclidean tensor norms                             *)
(* |T(u)|^2 <= 2 t0^2 |T(t0 u)|^2 + 2 (1 - t0)^2 #tuples sup |H|^2.         *)
(* ------------------------------------------------------------------------- *)

let P2C_RAY_DERIV = prove
 (`!(f:real^N->real) u t.
     (\x. lift(f x)) differentiable at (t % u)
     ==> ((\s. f(s % u)) has_real_derivative
          drop(frechet_derivative (\x. lift(f x)) (at (t % u)) u)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative] THEN
  SUBGOAL_THEN
   `(lift o (\s. (f:real^N->real)(s % u)) o drop) =
    (\x. lift(f x)) o (\x:real^1. drop x % u)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. drop x %
       lift(drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at (t % u)) u))) =
    frechet_derivative (\x. lift(f x)) (at (t % u)) o (\x:real^1. drop x % u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; FUN_EQ_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    SIMP_TAC[LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]]);;

let P2C_RADIAL_SCALAR = prove
 (`!(f:real^N->real) h p rho u t0 H.
     1 <= p /\
     (!z. z IN ball(vec 0,rho)
          ==> (\x. lift(f x)) differentiable at z /\
              &p * f z + drop(frechet_derivative (\x. lift(f x)) (at z) z) = h z) /\
     u IN ball(vec 0,rho) /\ &0 <= t0 /\ t0 <= &1 /\
     (!t. t0 <= t /\ t <= &1 ==> abs(h(t % u)) <= H)
     ==> abs(f u) <= t0 pow p * abs(f(t0 % u)) + (&1 - t0) * H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "deq") MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hb")))) THEN
  SUBGOAL_THEN `&0 <= H` ASSUME_TAC THENL
   [USE_THEN "hb" (MP_TAC o SPEC `&1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> t % u IN ball(vec 0:real^N,rho)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `u IN ball(vec 0:real^N,rho)` THEN
    REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < r ==> a < r`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> ((\s. s pow p * (f:real^N->real)(s % u)) has_real_derivative
             s pow (p - 1) * h(s % u)) (atreal s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `s % u IN ball(vec 0:real^N,rho)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "deq" (MP_TAC o SPEC `s % u:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\s:real. s pow p`; `&p * s pow (p - 1)`; `\s. (f:real^N->real)(s % u)`;
                   `drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at (s % u)) u)`;
                   `s:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC P2C_RAY_DERIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    BETA_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    SIMP_TAC[LINEAR_CMUL; DROP_CMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s pow p = s pow (p - 1) * s` SUBST1_TAC THENL
     [SUBGOAL_THEN `p = (p - 1) + 1` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
      THENL [ASM_ARITH_TAC; REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. s pow p * (f:real^N->real)(s % u)`;
                 `\s. s pow (p - 1) * (h:real^N->real)(s % u)`;
                 `real_interval[t0,&1]`; `H:real`] REAL_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        USE_THEN "hb" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `t0:real`]) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POW_ONE; REAL_MUL_LID;
              VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(t0 pow p * (f:real^N->real)(t0 % u)) = t0 pow p * abs(f(t0 % u))`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `t0 <= &1 ==> abs(&1 - t0) = &1 - t0`] THEN REAL_ARITH_TAC);;

let P2C_SQ_SPLIT = prove
 (`!x a b. &0 <= a /\ &0 <= b /\ abs x <= a + b
           ==> x pow 2 <= &2 * a pow 2 + &2 * b pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a + b) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_SQ_LE THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `a - b` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let P2C_RADIAL_TENSOR = prove
 (`!m p rho (Tf:real^N->(num->real^N)->real) Hf u t0 Hs.
     1 <= p /\
     ltensor_field m (ball(vec 0,rho)) Tf /\
     (!w. smooth_map_on (ball(vec 0,rho)) (\y. lift(Tf y w))) /\
     ltensor_field m (ball(vec 0,rho)) Hf /\
     (!z w. z IN ball(vec 0,rho) ==> &p * Tf z w + p2c_dx m Tf z w = Hf z w) /\
     u IN ball(vec 0,rho) /\ &0 <= t0 /\ t0 <= &1 /\
     (!t. t0 <= t /\ t <= &1 ==> ltnorm2 m p2c_flat Hf (t % u) <= Hs)
     ==> ltnorm2 m p2c_flat Tf u <=
         &2 * t0 pow 2 * ltnorm2 m p2c_flat Tf (t0 % u) +
         &2 * (&1 - t0) pow 2 * &(CARD(index_tuples m (:N))) * Hs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sm") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hb"))))))))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> t % u IN ball(vec 0:real^N,rho)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `u IN ball(vec 0:real^N,rho)` THEN
    REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < r ==> a < r`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 % u IN ball(vec 0:real^N,rho)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Hs` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 m p2c_flat (Hf:real^N->(num->real^N)->real) (&1 % u)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_FLAT_LTNORM2_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID];
      USE_THEN "hb" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `ball(vec 0:real^N,rho)`; `Tf:real^N->(num->real^N)->real`;
                 `u:real^N`] P2C_FLAT_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`m:num`; `ball(vec 0:real^N,rho)`; `Tf:real^N->(num->real^N)->real`;
                 `t0 % u:real^N`] P2C_FLAT_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBGOAL_THEN
   `&2 * (&1 - t0) pow 2 * &(CARD(index_tuples m (:N))) * Hs =
    sum (index_tuples m (:N)) (\p:num->num. &2 * (&1 - t0) pow 2 * Hs)`
  SUBST1_TAC THENL
   [SIMP_TAC[SUM_CONST; LRG_INDEX_TUPLES_FINITE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM SUM_ADD; LRG_INDEX_TUPLES_FINITE] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `q:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\z. (Tf:real^N->(num->real^N)->real) z (\m. basis(q m))`;
                 `\z. (Hf:real^N->(num->real^N)->real) z (\m. basis(q m))`;
                 `p:num`; `rho:real`; `u:real^N`; `t0:real`; `sqrt Hs`] P2C_RADIAL_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `ball(vec 0:real^N,rho)` THEN ASM_REWRITE_TAC[OPEN_BALL];
        MP_TAC(ISPECL [`m:num`; `ball(vec 0:real^N,rho)`; `Tf:real^N->(num->real^N)->real`;
                       `z:real^N`; `\m. basis((q:num->num) m):real^N`] P2C_DX_COMP) THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `ltnorm2 m p2c_flat (Hf:real^N->(num->real^N)->real) (t % u)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2C_FLAT_COMP_LE THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "hb" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(Tf:real^N->(num->real^N)->real) u (\m. basis(q m))`;
                 `t0 pow p * abs((Tf:real^N->(num->real^N)->real) (t0 % u) (\m. basis(q m)))`;
                 `(&1 - t0) * sqrt Hs`] P2C_SQ_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS; SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b = b' ==> x <= &2 * a + &2 * b ==> x <= &2 * a' + &2 * b'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2; GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE];
      SUBGOAL_THEN `p = (p - 1) + 1` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
      THENL [ASM_ARITH_TAC; REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The shell bootstrap.  Two nonnegative continuous functions                *)
(* a, b on cball(0,r) obeying the radial estimates above in the form         *)
(*   a(u) <= 2 t0^2 a(t0 u) + c1 sup_segment b,                             *)
(*   b(u) <= 2 t0^2 b(t0 u) + c2 (((1 - t0) C0 |u|^2)^2 sup_segment (a + b) + K) *)
(* with C0 r^2 <= 1 are bounded by a constant depending only on c1, c2, K:  *)
(* induction over N shells i r / N < |u| <= (i + 1) r / N, absorbing the    *)
(* top-order coupling (at most c2 / N^2) with the maxima on each closed     *)
(* ball.                                                                     *)
(* ------------------------------------------------------------------------- *)

let p2c_shell = new_definition
 `p2c_shell c1 c2 K (a:real^N->real) b r C0 <=>
    &0 < r /\ &0 <= C0 /\ C0 * r pow 2 <= &1 /\
    (lift o a) continuous_on cball(vec 0,r) /\ (lift o b) continuous_on cball(vec 0,r) /\
    (!w. w IN cball(vec 0,r) ==> &0 <= a w /\ &0 <= b w) /\
    (!u t0 Bs. u IN cball(vec 0,r) /\ &0 <= t0 /\ t0 <= &1 /\
               (!t. t0 <= t /\ t <= &1 ==> b(t % u) <= Bs)
               ==> a u <= &2 * t0 pow 2 * a(t0 % u) + c1 * Bs) /\
    (!u t0 Hs. u IN cball(vec 0,r) /\ &0 <= t0 /\ t0 <= &1 /\
               (!t. t0 <= t /\ t <= &1 ==> a(t % u) + b(t % u) <= Hs)
               ==> b u <= &2 * t0 pow 2 * b(t0 % u) +
                          c2 * (((&1 - t0) * C0 * norm u pow 2) pow 2 * Hs + K))`;;

let P2C_BOOT_ALG = prove
 (`!A B M c1 c2 K e.
     &0 <= A /\ &0 <= B /\ &0 <= M /\ &0 <= c1 /\ &0 <= c2 /\ &0 <= K /\ &0 <= e /\
     e * (c1 + &1) <= inv(&2) /\
     A <= &2 * M + c1 * B /\ B <= &2 * M + e * (A + B) + c2 * K
     ==> A + B <= (&8 + &6 * c1) * M + &2 * c2 * K * (&1 + c1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e <= inv(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * (c1 + &1)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * (A + B) <= M + inv(&2) * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * (&2 * M + (c1 + &1) * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_ARITH `e * &2 * M = (e * &2) * M`] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `B <= &6 * M + &2 * c2 * K` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1 * B <= c1 * (&6 * M + &2 * c2 * K)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_BOOT_COUPLING = prove
 (`!C0 r N i x.
     &0 <= C0 /\ C0 * r pow 2 <= &1 /\ &0 < r /\ 1 <= N /\ i + 1 <= N /\
     &i * r / &N < x /\ x <= &(i + 1) * r / &N
     ==> &0 <= (&1 - (&i * r / &N) / x) * C0 * x pow 2 /\
         ((&1 - (&i * r / &N) / x) * C0 * x pow 2) pow 2 <= inv(&N pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &i * r / &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - (&i * r / &N) / x) * C0 * x pow 2 = C0 * x * (x - &i * r / &N)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `x - &i * r / &N <= r / &N` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a + d ==> x - a <= d`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(i + 1) * r / &N` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `C0 * x * (x - &i * r / &N) <= inv(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C0 * (&(i + 1) * r / &N) * (r / &N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C0 * (&(i + 1) * r / &N) * (r / &N) = (C0 * r pow 2) * &(i + 1) / &N pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &(i + 1) / &N pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * x * (x - &i * r / &N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]);;

let P2C_SHELL_BASE = prove
 (`!c1 c2 K (a:real^N->real) b r C0.
     p2c_shell c1 c2 K a b r C0 /\ &0 <= c1 /\ &0 <= c2
     ==> a(vec 0) + b(vec 0) <= (c1 + &1) * c2 * K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_shell] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")))))))) THEN
  SUBGOAL_THEN `vec 0 IN cball(vec 0:real^N,r)` ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "pos" (MP_TAC o SPEC `vec 0:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "h2" (MP_TAC o SPECL [`vec 0:real^N`; `&0`;
    `(a:real^N->real)(vec 0) + (b:real^N->real)(vec 0)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_POW_ZERO] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN DISCH_TAC THEN
  USE_THEN "h1" (MP_TAC o SPECL [`vec 0:real^N`; `&0`; `(b:real^N->real)(vec 0)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `c1 * (b:real^N->real)(vec 0) <= c1 * c2 * K` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_SHELL_STEP = prove
 (`!c1 c2 K N M i.
     &0 <= c1 /\ &0 <= c2 /\ &0 <= K /\ 1 <= N /\
     (c2 / &N pow 2) * (c1 + &1) <= inv(&2) /\ &0 <= M /\ i + 1 <= N
     ==> !(a:real^N->real) b r C0.
           p2c_shell c1 c2 K a b r C0 /\
           (!w. norm w <= &i * r / &N ==> a w + b w <= M)
           ==> !w. norm w <= &(i + 1) * r / &N
                   ==> a w + b w <= (&8 + &6 * c1) * M + &2 * c2 * K * (&1 + c1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[p2c_shell] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "ih")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")))))))) THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ri = &i * r / &N` THEN ABBREV_TAC `rj = &(i + 1) * r / &N` THEN
  SUBGOAL_THEN `&0 <= ri /\ ri <= rj /\ rj <= r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ri"; "rj"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,rj) SUBSET cball(vec 0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(cball(vec 0:real^N,rj)) /\ ~(cball(vec 0:real^N,rj) = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->real`; `cball(vec 0:real^N,rj)`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^N,r)` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `wa:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "amax")))] THEN
  MP_TAC(ISPECL [`b:real^N->real`; `cball(vec 0:real^N,rj)`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^N,r)` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `wb:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bmax")))] THEN
  SUBGOAL_THEN `&0 <= (a:real^N->real) wa /\ &0 <= (b:real^N->real) wb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "pos" (MP_TAC o SPEC `wa:real^N`); USE_THEN "pos" (MP_TAC o SPEC `wb:real^N`)] THEN
    ANTS_TAC THEN TRY(STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c2 / &N pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN cball(vec 0:real^N,rj)
        ==> (a:real^N->real) u <= &2 * M + c1 * (b:real^N->real) wb /\
            b u <= &2 * M + (c2 / &N pow 2) * (a wa + b wb) + c2 * K`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `u IN cball(vec 0:real^N,r)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "pos" (MP_TAC o SPEC `u:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= c1 * (b:real^N->real) wb /\
                  &0 <= (c2 / &N pow 2) * ((a:real^N->real) wa + b wb) /\ &0 <= c2 * K`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `norm(u:real^N) <= ri` THENL
     [USE_THEN "ih" (MP_TAC o SPEC `u:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(u:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `t0 = ri / norm(u:real^N)` THEN
    SUBGOAL_THEN `&0 <= t0 /\ t0 <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t0" THEN ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(t0 % u:real^N) = ri` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
      EXPAND_TAC "t0" THEN UNDISCH_TAC `&0 < norm(u:real^N)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N->real)(t0 % u) + (b:real^N->real)(t0 % u) <= M` ASSUME_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `t0 % u IN cball(vec 0:real^N,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pos" (MP_TAC o SPEC `t0 % u:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `!t. t0 <= t /\ t <= &1 ==> t % u IN cball(vec 0:real^N,rj)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_CBALL_0; NORM_MUL] THEN
      UNDISCH_TAC `u IN cball(vec 0:real^N,rj)` THEN REWRITE_TAC[IN_CBALL_0] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= r ==> a <= r`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t0 pow 2 * (a:real^N->real)(t0 % u) <= M /\
                  t0 pow 2 * (b:real^N->real)(t0 % u) <= M`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      (CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "h1" (MP_TAC o SPECL [`u:real^N`; `t0:real`; `(b:real^N->real) wb`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bmax" MATCH_MP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "h2" (MP_TAC o SPECL [`u:real^N`; `t0:real`;
      `(a:real^N->real) wa + (b:real^N->real) wb`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
      CONJ_TAC THENL [USE_THEN "amax" MATCH_MP_TAC; USE_THEN "bmax" MATCH_MP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`C0:real`; `r:real`; `N:num`; `i:num`; `norm(u:real^N)`]
                  P2C_BOOT_COUPLING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      UNDISCH_TAC `u IN cball(vec 0:real^N,rj)` THEN REWRITE_TAC[IN_CBALL_0] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `((&1 - t0) * C0 * norm(u:real^N) pow 2) pow 2 * ((a:real^N->real) wa + (b:real^N->real) wb)
      <= inv(&N pow 2) * (a wa + b wb)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [EXPAND_TAC "t0" THEN EXPAND_TAC "ri" THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (ASSUME `&0 <= c2`)) THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(a:real^N->real) wa`; `(b:real^N->real) wb`; `M:real`; `c1:real`;
                 `c2:real`; `K:real`; `c2 / &N pow 2`] P2C_BOOT_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `wa:real^N`) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `wb:real^N`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `w IN cball(vec 0:real^N,rj)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:real^N->real) wa + (b:real^N->real) wb` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL [USE_THEN "amax" MATCH_MP_TAC; USE_THEN "bmax" MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P2C_SHELL_BOOT = prove
 (`!c1 c2 K. &0 <= c1 /\ &0 <= c2 /\ &0 <= K
     ==> ?M. !(a:real^N->real) b r C0.
               p2c_shell c1 c2 K a b r C0
               ==> !w. w IN cball(vec 0,r) ==> a w + b w <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 * c2 * (c1 + &1) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `&0 <= c2 * (c1 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c2 / &N pow 2) * (c1 + &1) <= inv(&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c2 / &N pow 2) * (c1 + &1) = (c2 * (c1 + &1)) / &N pow 2` SUBST1_TAC
    THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    SUBGOAL_THEN `&N * &1 <= &N * &N` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= N ==> ?M. &0 <= M /\
          !(a:real^N->real) b r C0.
             p2c_shell c1 c2 K a b r C0
             ==> !w. norm w <= &i * r / &N ==> a w + b w <= M`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(c1 + &1) * c2 * K` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `w:real^N` THEN
      REWRITE_TAC[REAL_MUL_LZERO; NORM_LE_0] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC P2C_SHELL_BASE THEN
      MAP_EVERY EXISTS_TAC [`r:real`; `C0:real`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m"))) THEN
    EXISTS_TAC `(&8 + &6 * c1) * M + &2 * c2 * K * (&1 + c1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD1] THEN
    MP_TAC(ISPECL [`c1:real`; `c2:real`; `K:real`; `N:num`; `M:real`; `i:num`]
                  P2C_SHELL_STEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N->real`; `b:real^N->real`; `r:real`; `C0:real`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "m" (fun th -> MATCH_ACCEPT_TAC(MATCH_MP th
      (ASSUME `p2c_shell c1 c2 K (a:real^N->real) b r C0`)));
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m"))) THEN
  EXISTS_TAC `M:real` THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
  USE_THEN "m" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `p2c_shell c1 c2 K (a:real^N->real) b r C0`))) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `&N * r / &N = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The Leibniz bound.  For a bilinear tensor operation B of                  *)
(* the class lbilin_on (products, permutations, contractions), with the     *)
(* flat metric:                                                              *)
(*   |d^j B(S,T)|^2 <= c sum_{a <= j} |d^a S|^2 |d^(j-a) T|^2.               *)
(* Induction on j with P2C_LBILIN_ON_NABLA, P2C_LNABLA_ITER_SHIFT and the    *)
(* linearity of the iterated derivative.                                     *)
(* ------------------------------------------------------------------------- *)

(* The shift rule for iterated derivatives (the statement of                *)
(* RFA_LNABLA_ITER_SHIFT of pc_rfa_rmderiv, which is not in this closure).   *)

let P2C_LNABLA_ITER_SHIFT = prove
 (`!k l (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
        lnabla_iter (k + 1) l G (lnabla k G tf) = lnabla_iter k (l + 1) G tf`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; RFA_LNABLA_ITER_1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lnabla_iter; ARITH_RULE `SUC l + 1 = SUC(l + 1)`] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + l = k + l + 1`]);;

let P2C_SUM_SHIFT_LE = prove
 (`!(f:num->real) g j.
     (!a. &0 <= f a) /\ (!a. &0 <= g a)
     ==> sum(0..j) (\a. f(a + 1) * g(j - a)) <=
         sum(0..j + 1) (\a. f a * g((j + 1) - a)) /\
         sum(0..j) (\a. f a * g((j - a) + 1)) <=
         sum(0..j + 1) (\a. f a * g((j + 1) - a))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`1`; `\a. (f:num->real) a * g((j + 1) - a)`; `0`; `j:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ARITH_RULE `(j + 1) - (i + 1) = j - i`; ARITH_RULE `0 + 1 = 1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 = 1`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= x + s`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sum(0..j) (\a. (f:num->real) a * g((j - a) + 1)) =
                  sum(0..j) (\a. f a * g((j + 1) - a))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[SUM_ADD_SPLIT; LE_0; ARITH_RULE `0 <= j + 1`; SUM_SING_NUMSEG] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= s + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]]);;

let P2C_FLAT_NORM_ADD = prove
 (`!m U (X:real^N->(num->real^N)->real) Y z.
     open U /\ ltensor_field m U X /\ ltensor_field m U Y /\ z IN U
     ==> ltnorm2 m p2c_flat (\y u. X y u + Y y u) z <=
         &2 * ltnorm2 m p2c_flat X z + &2 * ltnorm2 m p2c_flat Y z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD]);;

let P2C_LEIBNIZ = prove
 (`!j k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q B
     ==> ?c. &0 <= c /\
             !U tf tg z.
               open U /\ ltensor_field p U tf /\ ltensor_field q U tg /\
               (!u. smooth_map_on U (\y. lift(tf y u))) /\
               (!u. smooth_map_on U (\y. lift(tg y u))) /\ z IN U
               ==> ltnorm2 (k + j) p2c_flat
                     (lnabla_iter k j p2c_flat (B p2c_flat tf tg)) z <=
                   c * sum(0..j)
                         (\a. ltnorm2 (p + a) p2c_flat (lnabla_iter p a p2c_flat tf) z *
                              ltnorm2 (q + (j - a)) p2c_flat
                                (lnabla_iter q (j - a) p2c_flat tg) z)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_NORM) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; SUM_SING_NUMSEG; SUB_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2C_LBILIN_ON_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nab"))))) THEN
  USE_THEN "ih" (fun ih -> MP_TAC(MATCH_MP (SPECL [`k + 1`; `p + 1`; `q:num`;
    `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] ih)
    (ASSUME `lbilin_on (k + 1) (p + 1) q
       (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b1"))) THEN
  USE_THEN "ih" (fun ih -> MP_TAC(MATCH_MP (SPECL [`k + 1`; `p:num`; `q + 1`;
    `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] ih)
    (ASSUME `lbilin_on (k + 1) p (q + 1)
       (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b2"))) THEN
  EXISTS_TAC `&2 * c1 + &2 * c2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `tg:real^N->(num->real^N)->real`]
                P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `p + 1`; `q:num`;
    `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `lnabla p p2c_flat (tf:real^N->(num->real^N)->real)`; `tg:real^N->(num->real^N)->real`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `p:num`; `q + 1`;
    `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`; `lnabla q p2c_flat (tg:real^N->(num->real^N)->real)`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  ABBREV_TAC `X1 = (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
        p2c_flat (lnabla p p2c_flat (tf:real^N->(num->real^N)->real)) tg` THEN
  ABBREV_TAC `X2 = (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
        p2c_flat (tf:real^N->(num->real^N)->real) (lnabla q p2c_flat tg)` THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `X1:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `X2:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. lnabla_iter k (SUC j) p2c_flat
          ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
           p2c_flat tf tg) z u =
        lnabla_iter (k + 1) j p2c_flat X1 z u + lnabla_iter (k + 1) j p2c_flat X2 z u`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ADD1; GSYM P2C_LNABLA_ITER_SHIFT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla_iter (k + 1) j p2c_flat
                  (\y u. &1 * (X1:real^N->(num->real^N)->real) y u +
                         &1 * (X2:real^N->(num->real^N)->real) y u) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`k + 1`; `p2c_flat:real^N->real^N^N`; `p2c_flat:real^N->real^N^N`;
        `lnabla k p2c_flat ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) p2c_flat tf tg)`;
        `\y u. &1 * (X1:real^N->(num->real^N)->real) y u +
               &1 * (X2:real^N->(num->real^N)->real) y u`;
        `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
        MAP_EVERY EXPAND_TAC ["X1"; "X2"] THEN
        USE_THEN "nab" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD];
        DISCH_THEN(MP_TAC o SPECL [`j:num`; `z:real^N`; `u:num->real^N`]) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                     `X1:real^N->(num->real^N)->real`; `X2:real^N->(num->real^N)->real`;
                     `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
      ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 (k + SUC j) p2c_flat
      (lnabla_iter k (SUC j) p2c_flat
         ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
          p2c_flat tf tg)) z =
    ltnorm2 ((k + 1) + j) p2c_flat
      (\y u. lnabla_iter (k + 1) j p2c_flat X1 y u + lnabla_iter (k + 1) j p2c_flat X2 y u) z`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k + SUC j = (k + 1) + j`] THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ltnorm2 ((k + 1) + j) p2c_flat
                     (lnabla_iter (k + 1) j p2c_flat (X1:real^N->(num->real^N)->real)) z +
              &2 * ltnorm2 ((k + 1) + j) p2c_flat
                     (lnabla_iter (k + 1) j p2c_flat (X2:real^N->(num->real^N)->real)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_FLAT_NORM_ADD THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "b1" (MP_TAC o SPECL [`U:real^N->bool`;
    `lnabla p p2c_flat (tf:real^N->(num->real^N)->real)`;
    `tg:real^N->(num->real^N)->real`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2C_LNABLA_ITER_SHIFT; ARITH_RULE `(p + 1) + a = p + (a + 1)`] THEN
  DISCH_TAC THEN
  USE_THEN "b2" (MP_TAC o SPECL [`U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
    `lnabla q p2c_flat (tg:real^N->(num->real^N)->real)`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2C_LNABLA_ITER_SHIFT; ARITH_RULE `(q + 1) + b = q + (b + 1)`] THEN
  DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\a. ltnorm2 (p + a) p2c_flat (lnabla_iter p a p2c_flat (tf:real^N->(num->real^N)->real)) z`;
    `\b. ltnorm2 (q + b) p2c_flat (lnabla_iter q b p2c_flat (tg:real^N->(num->real^N)->real)) z`;
    `j:num`] P2C_SUM_SHIFT_LE)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `a:num` THEN MATCH_MP_TAC P2C_FLAT_LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                    P2C_FLAT_ITER_FIELD);
      MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `tg:real^N->(num->real^N)->real`]
                    P2C_FLAT_ITER_FIELD)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN STRIP_TAC THEN
  ABBREV_TAC `S = sum(0..j + 1)
    (\a. ltnorm2 (p + a) p2c_flat (lnabla_iter p a p2c_flat (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + ((j + 1) - a)) p2c_flat
           (lnabla_iter q ((j + 1) - a) p2c_flat (tg:real^N->(num->real^N)->real)) z)` THEN
  SUBGOAL_THEN `c1 * sum(0..j) (\a. ltnorm2 (p + (a + 1)) p2c_flat
         (lnabla_iter p (a + 1) p2c_flat (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + (j - a)) p2c_flat
           (lnabla_iter q (j - a) p2c_flat (tg:real^N->(num->real^N)->real)) z) <= c1 * S /\
    c2 * sum(0..j) (\a. ltnorm2 (p + a) p2c_flat
         (lnabla_iter p a p2c_flat (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + ((j - a) + 1)) p2c_flat
           (lnabla_iter q ((j - a) + 1) p2c_flat (tg:real^N->(num->real^N)->real)) z) <= c2 * S`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bilinear operations used below, as members of lbilin_on              *)
(* (contractions of ltprod at two slots, RFA_LBILIN_ON_CTR_AT, then slot    *)
(* permutations and linear combinations), and their values for the flat    *)
(* metric:                                                                   *)
(*   p2c_mp   (S,T)(u1,u2)    = S(u1,e_c) T(e_c,u2)          (2 2 -> 2)      *)
(*   p2c_wop  (S,T)(u1,u2,u3) = S(u1,e_c) T(e_c,u2,u3)       (2 3 -> 3)      *)
(*   p2c_vop  (S,T)(u1,u2,u3) = S(u1,e_c,u3) T(e_c,u2)       (3 2 -> 3)      *)
(*   p2c_gam  (S,T)(u1,u2,u3) = S(u3,e_c) 1/2 (T(e_c,u2,u1) + T(e_c,u1,u2)  *)
(*                               - T(u1,u2,e_c))              (2 3 -> 3)      *)
(*   p2c_q1op (S,T)(u1,u2,u3) = S(e_c,u2,u1,u3) T(e_c)       (4 1 -> 3)      *)
(*   p2c_q2op (S,T)(u1,u2)    = S(u1,u2,e_c) T(e_c)          (3 1 -> 2)      *)
(* (summation over c, contraction with the inverse metric in general).      *)
(* ------------------------------------------------------------------------- *)

let P2C_ARGS_TAC : tactic = fun (asl,w as g) ->
  let f = rator(rator(lhs w)) in
  let th = snd(find (fun (_,th) -> let c = concl th in
                    try let h,args = strip_comb c in
                        fst(dest_const h) = "ltensor_field" && el 2 args = f
                    with Failure _ -> false) asl) in
  let args = snd(strip_comb(concl th)) in
  let k = el 0 args and uu = el 1 args in
  let n = dest_small_numeral k in
  let cases = list_mk_disj (map (fun i -> mk_eq(`m:num`, mk_small_numeral i)) (1--n)) in
  (MATCH_MP_TAC P2C_TF_ARGS THEN MAP_EVERY EXISTS_TAC [k; uu] THEN
   ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN cases (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   TRY ASM_ARITH_TAC THEN REWRITE_TAC[rfa_ins; ltperm] THEN P2C_NUM_EVAL_TAC) g;;

let P2C_CTR_LBILIN_TAC k p q i j defn =
  MP_TAC(ISPECL [mk_small_numeral k; mk_small_numeral p; mk_small_numeral q;
                 mk_small_numeral i; mk_small_numeral j;
                 mk_abs(`G:real^N->real^N^N`, mk_abs(`tf:real^N->(num->real^N)->real`,
                   mk_abs(`tg:real^N->(num->real^N)->real`,
                     list_mk_comb(`ltprod:num->(real^N->(num->real^N)->real)->
                        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`,
                        [mk_small_numeral p; `tf:real^N->(num->real^N)->real`;
                         `tg:real^N->(num->real^N)->real`]))))]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [mk_small_numeral p; mk_small_numeral q]
                  (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[defn; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THEN P2C_ARGS_TAC;;

let p2c_mp = new_definition
 `p2c_mp (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
         (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 1 else basis a) *
            tg y (\m. if m = 1 then basis b else u 2)))`;;

let P2C_MP_LBILIN = prove
 (`lbilin_on 2 2 2
     (p2c_mp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_LBILIN_TAC 2 2 2 2 3 p2c_mp);;

let P2C_CTR_PERM_LBILIN_TAC k p q i j s sperm defn =
  MP_TAC(ISPECL [mk_small_numeral k; mk_small_numeral p; mk_small_numeral q;
                 mk_small_numeral i; mk_small_numeral j;
                 mk_abs(`G:real^N->real^N^N`, mk_abs(`tf:real^N->(num->real^N)->real`,
                   mk_abs(`tg:real^N->(num->real^N)->real`,
                     list_mk_comb(`ltprod:num->(real^N->(num->real^N)->real)->
                        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`,
                        [mk_small_numeral p; `tf:real^N->(num->real^N)->real`;
                         `tg:real^N->(num->real^N)->real`]))))]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [mk_small_numeral p; mk_small_numeral q]
                  (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ sperm) THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[defn; ltprod; ltperm] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THEN P2C_ARGS_TAC;;

let P2C_PERM_213 = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 1 else m) permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 2 else if m = 2 then 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_PERM_132 = prove
 (`(\m. if m = 2 then 3 else if m = 3 then 2 else m) permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 2 then 3 else if m = 3 then 2 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_PERM_321 = prove
 (`(\m. if m = 1 then 3 else if m = 3 then 1 else m) permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 3 else if m = 3 then 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let p2c_wop = new_definition
 `p2c_wop (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 1 else basis a) *
            tg y (\m. if m = 1 then basis b else if m = 2 then u 2 else u 3)))`;;

let P2C_WOP_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_wop:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_LBILIN_TAC 3 2 3 2 3 p2c_wop);;

let p2c_vop = new_definition
 `p2c_vop (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 1 else if m = 2 then basis a else u 3) *
            tg y (\m. if m = 1 then basis b else u 2)))`;;

let P2C_VOP_LBILIN = prove
 (`lbilin_on 3 3 2
     (p2c_vop:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_PERM_LBILIN_TAC 3 3 2 2 4
    `\m. if m = 2 then 3 else if m = 3 then 2 else m` P2C_PERM_132 p2c_vop);;

let p2c_q1op = new_definition
 `p2c_q1op (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
           (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then basis a else if m = 2 then u 2 else if m = 3 then u 1
                      else u 3) *
            tg y (\m. basis b)))`;;

let P2C_Q1OP_LBILIN = prove
 (`lbilin_on 3 4 1
     (p2c_q1op:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_PERM_LBILIN_TAC 3 4 1 1 5
    `\m. if m = 1 then 2 else if m = 2 then 1 else m` P2C_PERM_213 p2c_q1op);;

let p2c_q2op = new_definition
 `p2c_q2op (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
           (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 1 else if m = 2 then u 2 else basis a) *
            tg y (\m. basis b)))`;;

let P2C_Q2OP_LBILIN = prove
 (`lbilin_on 2 3 1
     (p2c_q2op:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_LBILIN_TAC 2 3 1 3 4 p2c_q2op);;

let p2c_ga1 = new_definition
 `p2c_ga1 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 3 else basis a) *
            tg y (\m. if m = 1 then basis b else if m = 2 then u 2 else u 1)))`;;

let p2c_ga2 = new_definition
 `p2c_ga2 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 3 else basis a) *
            tg y (\m. if m = 1 then basis b else if m = 2 then u 1 else u 2)))`;;

let p2c_ga3 = new_definition
 `p2c_ga3 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 3 else basis a) *
            tg y (\m. if m = 1 then u 1 else if m = 2 then u 2 else basis b)))`;;

let P2C_GA1_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_ga1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_PERM_LBILIN_TAC 3 2 3 2 3
    `\m. if m = 1 then 3 else if m = 3 then 1 else m` P2C_PERM_321 p2c_ga1);;

let P2C_GA2_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_ga2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_PERM_LBILIN_TAC 3 2 3 2 3
    `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m`
    P2C_PERM_312 p2c_ga2);;

let P2C_GA3_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_ga3:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  P2C_CTR_PERM_LBILIN_TAC 3 2 3 2 5
    `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m`
    P2C_PERM_312 p2c_ga3);;

let p2c_gam = new_definition
 `p2c_gam (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    inv(&2) * (p2c_ga1 G tf tg y u + p2c_ga2 G tf tg y u - p2c_ga3 G tf tg y u)`;;

let P2C_GAM_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_gam:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(CONJ (INST_TYPE [`:N`,`:N`] P2C_GA1_LBILIN) (INST_TYPE [`:N`,`:N`] P2C_GA2_LBILIN)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_ADD) THEN
  DISCH_THEN(MP_TAC o C CONJ (INST_TYPE [`:N`,`:N`] P2C_GA3_LBILIN)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SUB) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP RFA_LBILIN_ON_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; p2c_gam] THEN REAL_ARITH_TAC);;

(* Contraction with the flat metric: the double sum collapses. *)

let P2C_FLAT_CONTR = prove
 (`!y (f:num->num->real).
     sum(1..dimindex(:N))
       (\a. sum(1..dimindex(:N))
          (\b. matrix_inv((p2c_flat:real^N->real^N^N) y)$a$b * f a b)) =
     sum(1..dimindex(:N)) (\a. f a a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flat; MATRIX_INV_I] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\b. if b = a then (f:num->num->real) a a else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[MAT_COMPONENT] THEN
    ASM_CASES_TAC `b:num = a` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tensors of the gauge argument and the radial identities              *)
(* for a metric field with G z z = z (Gauss lemma in normal coordinates):   *)
(*   Phi = (1/2) D G (p2c_phim, p2c_phi), Ginv (p2c_ginv), the position     *)
(*   1-form X (p2c_xt);                                                      *)
(*   D h = 2 Phi;  Gamma(z,a) = Ginv Phi a;  Gamma(z,z) = 0;                 *)
(*   (1 + D) Phi(u1,u2) = Rm(z,u2,u1,z) + (Phi Ginv Phi)(u1,u2) (Riccati);   *)
(*   d Ginv = -Ginv (d G) Ginv;  Gamma lowered = Ginv . (first derivatives). *)
(* ------------------------------------------------------------------------- *)

let p2c_phim = new_definition
 `p2c_phim (G:real^N->real^N^N) = \z. inv(&2) %% mderiv G z z`;;

let p2c_phi = new_definition
 `p2c_phi (G:real^N->real^N^N) = \z (u:num->real^N). u 1 dot (p2c_phim G z ** u 2)`;;

let p2c_ginv = new_definition
 `p2c_ginv (G:real^N->real^N^N) = \z (u:num->real^N). u 1 dot (matrix_inv(G z) ** u 2)`;;

let p2c_xt = new_definition
 `p2c_xt = \z:real^N. \u:num->real^N. u 1 dot z`;;

let P2C_MF_OPEN = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> open U`,
  SIMP_TAC[metric_field]);;

let P2C_MF_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`,
  SIMP_TAC[metric_field]);;

let P2C_MDERIV_DIAG_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U (vectorize o (\z. mderiv G z z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. mderiv G z z) =
    (\z. frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G) (at z) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; mderiv; VECTORIZE_MATRIFY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\z:real^N. frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                                 (at z)`;
                 `\z:real^N. z`] LRG_SMOOTH_LINEAR_ARG) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[]]);;

let P2C_PHIM_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U (vectorize o p2c_phim G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  REWRITE_TAC[p2c_phim; o_DEF; VECTORIZE_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_MDERIV_DIAG_SMOOTH) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* Dot forms: tensor fields of matrix fields and their flat derivatives. *)

let P2C_MATDOT_FIELD = prove
 (`!U (M:real^N->real^N^N).
     open U /\ smooth_map_on U (vectorize o M)
     ==> ltensor_field 2 U (\z u. u 1 dot (M z ** u 2)) /\
         (!u. smooth_map_on U (\y. lift(u 1 dot (M y ** u 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THEN TRY AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      REWRITE_TAC[LRG_LINEAR_DOT_MATVEC]];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]]);;

let P2C_MATDOT_DERIV = prove
 (`!U (M:real^N->real^N^N) z a b h.
     open U /\ smooth_map_on U (vectorize o M) /\ z IN U
     ==> drop(frechet_derivative (\x. lift(a dot (M x ** b))) (at z) h) =
         a dot (mderiv M z h ** b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (M:real^N->real^N^N))
                differentiable at (z:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`] o MATCH_MP LRG_HAS_DERIVATIVE_GDOT) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP]);;

let P2C_MATDOT_D = prove
 (`!U (M:real^N->real^N^N) z u.
     open U /\ smooth_map_on U (vectorize o M) /\ z IN U
     ==> lnabla 2 p2c_flat (\z u. u 1 dot (M z ** u 2)) z u =
         u 1 dot (mderiv M z (u 3) ** u 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `M:real^N->real^N^N`] P2C_MATDOT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`;
                 `\z:real^N. \u:num->real^N. u 1 dot ((M:real^N->real^N^N) z ** u 2)`;
                 `z:real^N`; `u:num->real^N`] P2C_FLAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC P2C_MATDOT_DERIV THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2C_MATDOT_DX = prove
 (`!U (M:real^N->real^N^N) z u.
     open U /\ smooth_map_on U (vectorize o M) /\ z IN U
     ==> p2c_dx 2 (\z u. u 1 dot (M z ** u 2)) z u = u 1 dot (mderiv M z z ** u 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `M:real^N->real^N^N`] P2C_MATDOT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`;
                 `\z:real^N. \u:num->real^N. u 1 dot ((M:real^N->real^N^N) z ** u 2)`;
                 `z:real^N`; `u:num->real^N`] P2C_DX_COMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2C_MATDOT_DERIV THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* The tensors Phi, Ginv, h = lmetric2 G and their basic properties. *)

let P2C_GINV_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U (vectorize o (\z. matrix_inv(G z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]);;

let P2C_LMETRIC2_EQ = prove
 (`!G:real^N->real^N^N. lmetric2 G = \z u. u 1 dot (G z ** u 2)`,
  REWRITE_TAC[FUN_EQ_THM; lmetric2]);;

let P2C_PHI_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (p2c_phi G) /\ (!u. smooth_map_on U (\y. lift(p2c_phi G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2c_phi] THEN
  MATCH_MP_TAC P2C_MATDOT_FIELD THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[P2C_PHIM_SMOOTH] THEN ASM_MESON_TAC[P2C_MF_OPEN]);;

let P2C_GINV_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (p2c_ginv G) /\ (!u. smooth_map_on U (\y. lift(p2c_ginv G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2c_ginv] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. matrix_inv((G:real^N->real^N^N) z)`]
                P2C_MATDOT_FIELD) THEN
  ASM_SIMP_TAC[P2C_GINV_SMOOTH] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; REWRITE_TAC[]]);;

let P2C_DH = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> lnabla 2 p2c_flat (lmetric2 G) z u = u 1 dot (mderiv G z (u 3) ** u 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_LMETRIC2_EQ] THEN
  MATCH_MP_TAC P2C_MATDOT_D THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]);;

let P2C_MDERIV_DIAG = prove
 (`!(G:real^N->real^N^N) z v. mderiv G z z ** v = &2 % (p2c_phim G z ** v)`,
  REWRITE_TAC[p2c_phim; MATRIX_VECTOR_LMUL; VECTOR_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID]);;

let P2C_DX_H = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> p2c_dx 2 (lmetric2 G) z u = &2 * p2c_phi G z u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_LMETRIC2_EQ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `u:num->real^N`]
                P2C_MATDOT_DX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p2c_phi; P2C_MDERIV_DIAG; DOT_RMUL]);;

let P2C_DX_PHI = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> p2c_dx 2 (p2c_phi G) z u = u 1 dot (mderiv (p2c_phim G) z z ** u 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_phi] THEN
  MATCH_MP_TAC P2C_MATDOT_DX THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[P2C_PHIM_SMOOTH] THEN ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]);;

(* Radial identities under the Gauss lemma G z z = z. *)

let P2C_GAUSS_PHIM = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> p2c_phim G z ** z = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `z:real^N`]
                CMPP_GAUSS_DERIV) THEN
  ASM_SIMP_TAC[P2C_MDERIV_DIAG] THEN VECTOR_ARITH_TAC);;

let P2C_G_GINV = prove
 (`!U (G:real^N->real^N^N) z v.
     metric_field U G /\ z IN U
     ==> G z ** (matrix_inv(G z) ** v) = v /\ matrix_inv(G z) ** (G z ** v) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

let P2C_G_GINV_INV = prove
 (`!(G:real^N->real^N^N) z v.
     invertible(G z)
     ==> G z ** (matrix_inv(G z) ** v) = v /\ matrix_inv(G z) ** (G z ** v) = v`,
  SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

let P2C_CHRIST_RAD = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> christoffel G z z a = matrix_inv(G z) ** (p2c_phim G z ** a) /\
         christoffel G z a z = matrix_inv(G z) ** (p2c_phim G z ** a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `christoffel G z z a = matrix_inv((G:real^N->real^N^N) z) ** (p2c_phim G z ** a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `z:real^N`;
                   `a:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `p2c_phim (G:real^N->real^N^N) z ** a`] P2C_G_GINV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                  CMPP_GAUSS_DERIV) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `w:real^N`]
                  CMPP_GAUSS_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. (a:real^N) dot v`) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. (w:real^N) dot v`) THEN
                         MP_TAC th) THEN
    REWRITE_TAC[DOT_RADD] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `w:real^N`;
                   `z:real^N`; `a:real^N`] LRG_MDERIV_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `w:real^N`;
                   `a:real^N`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[p2c_phim; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`;
                 `z:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[]);;

let P2C_CHRIST_RAD0 = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> christoffel G z z z = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `z:real^N`]
                P2C_CHRIST_RAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] P2C_GAUSS_PHIM) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO]);;

let P2C_CHRIST_LIN0 = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U
     ==> christoffel G z a (vec 0) = vec 0 /\ christoffel G z (vec 0) a = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `christoffel (G:real^N->real^N^N) z a` LINEAR_0) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_0 o SPEC `a:real^N`) THEN REWRITE_TAC[]]);;

let P2C_DCHRIST_YY = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> frechet_derivative (\x. christoffel G x z z) (at z) a =
         --(&2 % (matrix_inv(G z) ** (p2c_phim G z ** a)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`christoffel (G:real^N->real^N^N)`; `\x:real^N. x`; `\h:real^N. h`;
                 `\x:real^N. x`; `\h:real^N. h`; `U:real^N->bool`; `z:real^N`]
                LRG_HAS_DERIVATIVE_BILFAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    BETA_TAC THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. christoffel (G:real^N->real^N^N) x x x`;
                 `\x:real^N. vec 0:real^N`;
                 `\u. christoffel (G:real^N->real^N^N) z u z + christoffel G z z u +
                      frechet_derivative (\x. christoffel G x z z) (at z) u`;
                 `\h:real^N. vec 0:real^N`; `U:real^N->bool`; `z:real^N`]
                LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC P2C_CHRIST_RAD0 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `a:real^N`) THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_CHRIST_RAD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let P2C_DPA_HAS = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U
     ==> ((\x. matrix_inv(G x) ** (p2c_phim G x ** a)) has_derivative
          (\h. --(matrix_inv(G z) ** (mderiv G z h ** (matrix_inv(G z) ** (p2c_phim G z ** a)))) +
               matrix_inv(G z) ** (mderiv (p2c_phim G) z h ** a))) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `z:real^N`]
                LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `((\x. p2c_phim (G:real^N->real^N^N) x ** a) has_derivative
     (\h. mderiv (p2c_phim G) z h ** a)) (at z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2c_phim (G:real^N->real^N^N)`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        p2c_phim G) (at z)`;
                   `\x:real^N. a:real^N`; `\h:real^N. vec 0:real^N`; `z:real^N`]
                  LRG_HAS_DERIVATIVE_MATVEC) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[GSYM mderiv] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[P2C_PHIM_SMOOTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. matrix_inv((G:real^N->real^N^N) x)`;
                 `\h. vectorize(--(matrix_inv((G:real^N->real^N^N) z) **
                       matrify(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                                  (at z) h) **
                       matrix_inv(G z)))`;
                 `\x. p2c_phim (G:real^N->real^N^N) x ** a`;
                 `\h. mderiv (p2c_phim (G:real^N->real^N^N)) z h ** a`; `z:real^N`]
                LRG_HAS_DERIVATIVE_MATVEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; MATRIFY_VECTORIZE; GSYM mderiv] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; GSYM MATRIX_VECTOR_MUL_ASSOC]);;

let P2C_DCHRIST_AY = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> frechet_derivative (\x. christoffel G x a z) (at z) z =
         (--(matrix_inv(G z) ** (mderiv G z z ** (matrix_inv(G z) ** (p2c_phim G z ** a)))) +
          matrix_inv(G z) ** (mderiv (p2c_phim G) z z ** a)) -
         matrix_inv(G z) ** (p2c_phim G z ** a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`christoffel (G:real^N->real^N^N)`; `\x:real^N. a:real^N`;
                 `\h:real^N. vec 0:real^N`;
                 `\x:real^N. x`; `\h:real^N. h`; `U:real^N->bool`; `z:real^N`]
                LRG_HAS_DERIVATIVE_BILFAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    BETA_TAC THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_DPA_HAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. christoffel (G:real^N->real^N^N) x a x`;
                 `\x. matrix_inv((G:real^N->real^N^N) x) ** (p2c_phim G x ** (a:real^N))`;
                 `\u. christoffel (G:real^N->real^N^N) z (vec 0) z + christoffel G z (a:real^N) u +
                      frechet_derivative (\x. christoffel G x a z) (at z) u`;
                 `\h. --(matrix_inv((G:real^N->real^N^N) z) **
                         (mderiv G z h ** (matrix_inv(G z) ** (p2c_phim G z ** (a:real^N))))) +
                      matrix_inv(G z) ** (mderiv (p2c_phim G) z h ** a)`;
                 `U:real^N->bool`; `z:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`]
                  P2C_CHRIST_RAD) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_CHRIST_RAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `z:real^N`]
                P2C_CHRIST_LIN0) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let P2C_LRIEMANN_RAD = prove
 (`!U (G:real^N->real^N^N) z a.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> lriemann G z z a z =
         (matrix_inv(G z) ** (p2c_phim G z ** a) -
          matrix_inv(G z) ** (p2c_phim G z ** (matrix_inv(G z) ** (p2c_phim G z ** a)))) +
         matrix_inv(G z) ** (mderiv (p2c_phim G) z z ** a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lriemann] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_DCHRIST_AY) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_DCHRIST_YY) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] P2C_CHRIST_RAD0) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_CHRIST_RAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `matrix_inv((G:real^N->real^N^N) z) ** (p2c_phim G z ** a)`] P2C_CHRIST_RAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `a:real^N`]
                P2C_CHRIST_LIN0) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[P2C_MDERIV_DIAG; MATRIX_VECTOR_MUL_RMUL] THEN VECTOR_ARITH_TAC);;

(* The radial Riccati identity (1 + D) Phi = Rm(z,.,.,z) + Phi Ginv Phi. *)

let P2C_RICCATI = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U /\ (!z. z IN U ==> G z ** z = z)
     ==> p2c_phi G z u + p2c_dx 2 (p2c_phi G) z u =
         lrm4 G z (\m. if m = 1 then z else if m = 2 then u 2 else if m = 3 then u 1 else z) +
         u 1 dot (p2c_phim G z ** (matrix_inv(G z) ** (p2c_phim G z ** u 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `u:num->real^N`]
                P2C_DX_PHI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 2`] P2C_LRIEMANN_RAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
               P2C_G_GINV_INV] THEN
  REWRITE_TAC[p2c_phi; DOT_RADD; DOT_RSUB] THEN REAL_ARITH_TAC);;

(* The flat contraction forms of Phi Ginv Phi, Rm(z,.,.,z), d Ginv and Gamma. *)

let P2C_SUM_DOT_BASIS = prove
 (`!(a:real^N) (A:real^N^N) (f:num->real).
     sum(1..dimindex(:N)) (\c. (a dot (A ** basis c)) * f c) =
     a dot (A ** ((lambda c. f c):real^N))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[dot; MATRIX_VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN
  SIMP_TAC[dot; BASIS_COMPONENT; LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2C_SUM_DOT_BASIS2 = prove
 (`!(a:real^N) (A:real^N^N) v.
     sum(1..dimindex(:N)) (\c. (a dot (A ** basis c)) * (basis c dot v)) = a dot (A ** v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_SUM_DOT_BASIS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; DOT_BASIS]);;

let P2C_PGP_FORM = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> u 1 dot (p2c_phim G z ** (matrix_inv(G z) ** (p2c_phim G z ** u 2))) =
         p2c_mp p2c_flat (p2c_mp p2c_flat (p2c_phi G) (p2c_ginv G)) (p2c_phi G) z u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_mp; P2C_FLAT_CONTR] THEN
  REWRITE_TAC[p2c_phi; p2c_ginv] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; P2C_SUM_DOT_BASIS2] THEN
  SUBGOAL_THEN
   `!c. basis c dot (p2c_phim (G:real^N->real^N^N) z ** u 2) =
        basis c dot (p2c_phim G z ** (u:num->real^N) 2)` (K ALL_TAC) THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN REWRITE_TAC[P2C_SUM_DOT_BASIS2] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC]);;

let P2C_Q_FORM = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> lrm4 G z (\m. if m = 1 then z else if m = 2 then u 2 else if m = 3 then u 1 else z) =
         p2c_q2op p2c_flat (p2c_q1op p2c_flat (lrm4 G) p2c_xt) p2c_xt z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_q2op; p2c_q1op; P2C_FLAT_CONTR; p2c_xt] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
      (\d. (z:real^N)$d *
           lrm4 (G:real^N->real^N^N) z
             (\m. if m = 4 then basis d
                  else (\m. if m = 1 then z else if m = 2 then (u:num->real^N) 2
                            else if m = 3 then u 1 else z) m))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `lrm4 (G:real^N->real^N^N)`; `z:real^N`;
                   `\m. if m = 1 then z else if m = 2 then (u:num->real^N) 2
                        else if m = 3 then u 1 else z`; `4`; `z:real^N`]
                  P2C_SLOT_EXPAND) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    P2C_ARGS_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `lrm4 (G:real^N->real^N^N)`; `z:real^N`;
                 `\m. if m = 2 then (u:num->real^N) 2 else if m = 3 then u 1
                      else basis d`; `1`; `z:real^N`]
                P2C_SLOT_EXPAND) THEN
  ASM_REWRITE_TAC[ARITH] THEN BETA_TAC THEN
  MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' ==> a' = b' ==> a = b`) THEN CONJ_TAC THENL
   [P2C_ARGS_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[DOT_BASIS] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    AP_TERM_TAC THEN P2C_ARGS_TAC]);;

let P2C_MDERIV_GINV = prove
 (`!U (G:real^N->real^N^N) z h.
     metric_field U G /\ z IN U
     ==> mderiv (\x. matrix_inv(G x)) z h =
         --(matrix_inv(G z) ** mderiv G z h ** matrix_inv(G z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `z:real^N`]
                LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[mderiv] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE]);;

let P2C_DGINV_FORM = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> lnabla 2 p2c_flat (p2c_ginv G) z u =
         --(p2c_vop p2c_flat (p2c_wop p2c_flat (p2c_ginv G) (lnabla 2 p2c_flat (lmetric2 G)))
                    (p2c_ginv G) z u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN; P2C_MF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\x. matrix_inv((G:real^N->real^N^N) x)`; `z:real^N`;
                 `u:num->real^N`] P2C_MATDOT_D) THEN
  ASM_SIMP_TAC[P2C_GINV_SMOOTH] THEN REWRITE_TAC[GSYM p2c_ginv] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!h. mderiv (\x. matrix_inv((G:real^N->real^N^N) x)) z h =
        --(matrix_inv(G z) ** mderiv G z h ** matrix_inv(G z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2C_MDERIV_GINV THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_vop; p2c_wop; P2C_FLAT_CONTR] THEN
  SUBGOAL_THEN
   `!w. lnabla 2 p2c_flat (lmetric2 (G:real^N->real^N^N)) z w =
        w 1 dot (mderiv G z (w 3) ** w 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2C_DH THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_ginv] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[P2C_SUM_DOT_BASIS2] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; P2C_SUM_DOT_BASIS2] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; DOT_RNEG; GSYM MATRIX_VECTOR_MUL_ASSOC]);;

let P2C_CHRISTOFFEL_EXPAND = prove
 (`!(G:real^N->real^N^N) z a b.
     christoffel G z a b =
     matrix_inv(G z) **
     (inv(&2) % (mderiv G z a ** b + mderiv G z b ** a -
                 ((lambda c. a dot (mderiv G z (basis c) ** b)):real^N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[christoffel] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
           VECTOR_SUB_COMPONENT]);;

let P2C_FLAT_MUL = prove
 (`!z v. (p2c_flat:real^N->real^N^N) z ** v = v`,
  REWRITE_TAC[p2c_flat; MATRIX_VECTOR_MUL_LID]);;

let P2C_GINV_DOT_SYM = prove
 (`!U (G:real^N->real^N^N) z a b.
     metric_field U G /\ z IN U
     ==> a dot (matrix_inv(G z) ** b) = b dot (matrix_inv(G z) ** a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp(matrix_inv((G:real^N->real^N^N) z)) = matrix_inv(G z)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC DOT_SYM);;

let P2C_AF_FORM = prove
 (`!U (G:real^N->real^N^N) z u.
     metric_field U G /\ z IN U
     ==> p2c_af p2c_flat G z u =
         p2c_gam p2c_flat (p2c_ginv G) (lnabla 2 p2c_flat (lmetric2 G)) z u`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2c_af; P2C_FLAT_CHRISTOFFEL; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[P2C_FLAT_MUL] THEN
  REWRITE_TAC[p2c_gam; p2c_ga1; p2c_ga2; p2c_ga3; P2C_FLAT_CONTR] THEN
  SUBGOAL_THEN
   `!w. lnabla 2 p2c_flat (lmetric2 (G:real^N->real^N^N)) z w =
        w 1 dot (mderiv G z (w 3) ** w 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2C_DH THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_ginv] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[P2C_SUM_DOT_BASIS2; P2C_SUM_DOT_BASIS] THEN
  REWRITE_TAC[P2C_CHRISTOFFEL_EXPAND] THEN
  SUBGOAL_THEN
   `!v:real^N. (u:num->real^N) 3 dot (matrix_inv((G:real^N->real^N^N) z) ** v) =
               v dot (matrix_inv(G z) ** u 3)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2C_GINV_DOT_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL; DOT_LADD; DOT_LSUB] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Pointwise bounds.  p2c_dn k i T z = |d^i T|^2 (Euclidean)                 *)
(* at z; its algebra (shift, locality, sums, scalar multiples, Leibniz);     *)
(* entry bounds for 2-tensors; base bounds for h, Ginv, Phi; and the        *)
(* derivative bounds for Ginv and for the Christoffel tensor: lower orders   *)
(* bounded, the top order linear in |d^j h|^2.                               *)
(* ------------------------------------------------------------------------- *)

let p2c_dn = new_definition
 `p2c_dn k i (tf:real^N->(num->real^N)->real) z =
    ltnorm2 (k + i) p2c_flat (lnabla_iter k i p2c_flat tf) z`;;

let P2C_DN_POS = prove
 (`!k i U (tf:real^N->(num->real^N)->real) z.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\ z IN U
     ==> &0 <= p2c_dn k i tf z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn] THEN MATCH_MP_TAC P2C_FLAT_LTNORM2_POS THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[]);;

let P2C_DN_SHIFT = prove
 (`!k i (tf:real^N->(num->real^N)->real) z.
     p2c_dn (k + 1) i (lnabla k p2c_flat tf) z = p2c_dn k (i + 1) tf z`,
  REWRITE_TAC[p2c_dn; P2C_LNABLA_ITER_SHIFT; ARITH_RULE `(k + 1) + i = k + i + 1`]);;

let P2C_DN_LOCAL = prove
 (`!k i U (tf1:real^N->(num->real^N)->real) tf2 z.
     open U /\ z IN U /\ (!y u. y IN U ==> tf1 y u = tf2 y u)
     ==> p2c_dn k i tf1 z = p2c_dn k i tf2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn] THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
  REWRITE_TAC[] THEN GEN_TAC THEN
  MP_TAC(ISPECL [`k:num`; `p2c_flat:real^N->real^N^N`; `p2c_flat:real^N->real^N^N`;
                 `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
                 `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ASM_SIMP_TAC[]);;

let P2C_DN_LINCOMB = prove
 (`!k i U (tf1:real^N->(num->real^N)->real) tf2 a b z.
     open U /\ ltensor_field k U tf1 /\ (!u. smooth_map_on U (\y. lift(tf1 y u))) /\
     ltensor_field k U tf2 /\ (!u. smooth_map_on U (\y. lift(tf2 y u))) /\ z IN U
     ==> p2c_dn k i (\y u. a * tf1 y u + b * tf2 y u) z <=
         &2 * a pow 2 * p2c_dn k i tf1 z + &2 * b pow 2 * p2c_dn k i tf2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                 `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
                 `a:real`; `b:real`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf1:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf2:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ltnorm2 (k + i) p2c_flat
     (\y u. a * lnabla_iter k i p2c_flat (tf1:real^N->(num->real^N)->real) y u +
            b * lnabla_iter k i p2c_flat (tf2:real^N->(num->real^N)->real) y u) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ltnorm2 (k + i) p2c_flat
                (\y u. a * lnabla_iter k i p2c_flat (tf1:real^N->(num->real^N)->real) y u) z +
              &2 * ltnorm2 (k + i) p2c_flat
                (\y u. b * lnabla_iter k i p2c_flat (tf2:real^N->(num->real^N)->real) y u) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_FLAT_NORM_ADD THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LRG_TENSOR_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[RFA_LTNORM2_CMUL; ETA_AX] THEN REAL_ARITH_TAC]);;

let P2C_SUM_PROD_LE = prove
 (`!(f:num->real) g j Fm Gm.
     (!a. a <= j ==> &0 <= f a /\ f a <= Fm) /\ (!b. b <= j ==> &0 <= g b /\ g b <= Gm)
     ==> sum(0..j) (\a. f a * g(j - a)) <= &(j + 1) * Fm * Gm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..j) (\a:num. Fm * Gm)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - a:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(j + 1) - 0 = j + 1`; REAL_LE_REFL]]);;

let P2C_POLAR_BOUND = prove
 (`!(M:real^N^N) L a b.
     (!x y. x dot (M ** y) = y dot (M ** x)) /\
     (!x. abs(x dot (M ** x)) <= L * (x dot x))
     ==> abs(a dot (M ** b)) <= L * ((a dot a) + (b dot b)) / &2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `a + b:real^N` th) THEN MP_TAC(SPEC `a - b:real^N` th)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:real^N`; `a:real^N`]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let P2C_ENTRY_LTNORM2 = prove
 (`!U (M:real^N->real^N^N) z L.
     open U /\ smooth_map_on U (vectorize o M) /\ z IN U /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(basis i dot (M z ** basis j)) <= L)
     ==> ltnorm2 2 p2c_flat (\z u. u 1 dot (M z ** u 2)) z <=
         &(CARD(index_tuples 2 (:N))) * L pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `M:real^N->real^N^N`] P2C_MATDOT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `\z:real^N. \u:num->real^N. u 1 dot (M z ** u 2)`;
                 `z:real^N`] P2C_FLAT_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2C_SQ_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`p:num->num`; `2`; `1`] (INST_TYPE [`:N`,`:N`] LRG_INDEX_TUPLES_RANGE)) THEN
  MP_TAC(ISPECL [`p:num->num`; `2`; `2`] (INST_TYPE [`:N`,`:N`] LRG_INDEX_TUPLES_RANGE)) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Base bounds at a point where 1/2 <= G <= 2. *)

let P2C_GINV_NORM = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a))
     ==> !b. norm(matrix_inv(G z) ** b) <= &2 * norm b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `b:real^N` THEN
  ABBREV_TAC `v = matrix_inv((G:real^N->real^N^N) z) ** b` THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) z ** v = b` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                                       `b:real^N`] P2C_G_GINV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`v:real^N`; `b:real^N`] NORM_CAUCHY_SCHWARZ) THEN
  REWRITE_TAC[DOT_SQUARE_NORM] THEN
  ASM_CASES_TAC `norm(v:real^N) = &0` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `b:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(v:real^N) * (inv(&2) * norm v) <= norm v * norm(b:real^N)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]);;

let P2C_G_ENTRY = prove
 (`!U (G:real^N->real^N^N) z i j.
     metric_field U G /\ z IN U /\
     (!a. inv(&2) * (a dot a) <= a dot (G z ** a) /\ a dot (G z ** a) <= &2 * (a dot a)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> abs(basis i dot (G z ** basis j)) <= &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) z`; `&2`; `basis i:real^N`; `basis j:real^N`]
                P2C_POLAR_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      MP_TAC(ISPEC `x:real^N` DOT_POS_LE) THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[DOT_BASIS_BASIS] THEN REAL_ARITH_TAC]);;

let P2C_GINV_ENTRY = prove
 (`!U (G:real^N->real^N^N) z i j.
     metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> abs(basis i dot (matrix_inv(G z) ** basis j)) <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(basis i:real^N) * norm(matrix_inv((G:real^N->real^N^N) z) ** basis j)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN ASM_SIMP_TAC[NORM_BASIS; REAL_MUL_LID] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] P2C_GINV_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `basis j:real^N`) THEN
  ASM_SIMP_TAC[NORM_BASIS] THEN REAL_ARITH_TAC);;

let P2C_PHIM_ENTRY = prove
 (`!U (G:real^N->real^N^N) z C0 i j.
     metric_field U G /\ z IN U /\
     (!a. abs(a dot (mderiv G z z ** a)) <= &4 * C0 * norm z pow 2 * (a dot a)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> abs(basis i dot (p2c_phim G z ** basis j)) <= &2 * C0 * norm z pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p2c_phim (G:real^N->real^N^N) z`; `&2 * C0 * norm(z:real^N) pow 2`;
                 `basis i:real^N`; `basis j:real^N`] P2C_POLAR_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2c_phim; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_MDERIV_SYM THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[DOT_BASIS_BASIS] THEN REAL_ARITH_TAC]);;

let P2C_BASE_H = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\
     (!a. inv(&2) * (a dot a) <= a dot (G z ** a) /\ a dot (G z ** a) <= &2 * (a dot a))
     ==> p2c_dn 2 0 (lmetric2 G) z <= &(CARD(index_tuples 2 (:N))) * &4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES; P2C_LMETRIC2_EQ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `&2`]
                P2C_ENTRY_LTNORM2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[P2C_MF_OPEN]; ASM_MESON_TAC[P2C_MF_SMOOTH]; ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_G_ENTRY THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

let P2C_BASE_GINV = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a))
     ==> p2c_dn 2 0 (p2c_ginv G) z <= &(CARD(index_tuples 2 (:N))) * &4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES; p2c_ginv] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\x. matrix_inv((G:real^N->real^N^N) x)`; `z:real^N`; `&2`]
                P2C_ENTRY_LTNORM2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[P2C_MF_OPEN]; ASM_MESON_TAC[P2C_GINV_SMOOTH]; ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC P2C_GINV_ENTRY THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

let P2C_BASE_PHI = prove
 (`!U (G:real^N->real^N^N) z C0.
     metric_field U G /\ z IN U /\
     (!a. abs(a dot (mderiv G z z ** a)) <= &4 * C0 * norm z pow 2 * (a dot a))
     ==> p2c_dn 2 0 (p2c_phi G) z <=
         &(CARD(index_tuples 2 (:N))) * (&2 * C0 * norm z pow 2) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES; p2c_phi] THEN
  MATCH_MP_TAC P2C_ENTRY_LTNORM2 THEN EXISTS_TAC `U:real^N->bool` THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ASM_MESON_TAC[P2C_PHIM_SMOOTH]; ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_PHIM_ENTRY THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Negation does not change the norm (via P2C_DN_LINCOMB with a = -1). *)

let P2C_DN_NEG_LE = prove
 (`!k i U (tf:real^N->(num->real^N)->real) z.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\ z IN U
     ==> p2c_dn k i (\y u. --(tf y u)) z <= &2 * p2c_dn k i tf z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `i:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                 `tf:real^N->(num->real^N)->real`; `--(&1)`; `&0`; `z:real^N`]
                P2C_DN_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_DN_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Bound for a product of factors with at most one top-order factor:     *)
(* every term of a Leibniz sum is bounded by a constant times (L + E).   *)

let P2C_LEIB_BOUND = prove
 (`!c (f:num->real) g j Fm Gm.
     &0 <= c /\ (!a. a <= j ==> &0 <= f a /\ f a <= Fm) /\
     (!b. b <= j ==> &0 <= g b /\ g b <= Gm)
     ==> c * sum(0..j) (\a. f a * g(j - a)) <= c * &(j + 1) * Fm * Gm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2C_SUM_PROD_LE THEN ASM_REWRITE_TAC[]);;

(* The Leibniz bound with one constant for all orders up to m, in p2c_dn form. *)

let P2C_LEIBNIZ_UPTO = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q B
     ==> !m. ?c. &0 <= c /\
                 !a U tf tg z.
                   a <= m /\ open U /\ ltensor_field p U tf /\ ltensor_field q U tg /\
                   (!u. smooth_map_on U (\y. lift(tf y u))) /\
                   (!u. smooth_map_on U (\y. lift(tg y u))) /\ z IN U
                   ==> p2c_dn k a (B p2c_flat tf tg) z <=
                       c * sum(0..a) (\b. p2c_dn p b tf z * p2c_dn q (a - b) tg z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [MP_TAC(SPECL [`0`; `k:num`; `p:num`; `q:num`;
          `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LEIBNIZ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[p2c_dn] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  MP_TAC(SPECL [`SUC m`; `k:num`; `p:num`; `q:num`;
          `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LEIBNIZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c0 + c1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum(0..a) (\b. p2c_dn p b (tf:real^N->(num->real^N)->real) z *
                                    p2c_dn q (a - b) (tg:real^N->(num->real^N)->real) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a <= m:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c0 * sum(0..a) (\b. p2c_dn p b (tf:real^N->(num->real^N)->real) z *
                                   p2c_dn q (a - b) (tg:real^N->(num->real^N)->real) z)` THEN
    CONJ_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `a = SUC m:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c1 * sum(0..SUC m) (\b. p2c_dn p b (tf:real^N->(num->real^N)->real) z *
                                   p2c_dn q (SUC m - b) (tg:real^N->(num->real^N)->real) z)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[p2c_dn] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]);;

(* Derivatives of the inverse metric: d Ginv = -V(W(Ginv, d h), Ginv). *)

let P2C_GINV_DER = prove
 (`!L. &0 <= L
       ==> !j. ?c K. &0 <= c /\ &0 <= K /\
             !U (G:real^N->real^N^N) z.
               metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a)) /\
               (!i. i < j ==> p2c_dn 2 i (lmetric2 G) z <= L)
               ==> (!i. i < j ==> p2c_dn 2 i (p2c_ginv G) z <= K) /\
                   p2c_dn 2 j (p2c_ginv G) z <= c * p2c_dn 2 j (lmetric2 G) z + K`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `&(CARD(index_tuples 2 (:N))) * &4`] THEN
    REWRITE_TAC[REAL_LE_REFL; LT; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_BASE_GINV THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `K:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))))) THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_VOP_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lv"))) THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_WOP_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cw:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lw"))) THEN
  ABBREV_TAC `KI = c * L + K` THEN
  SUBGOAL_THEN `&0 <= KI` ASSUME_TAC THENL
   [EXPAND_TAC "KI" THEN ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL]; ALL_TAC] THEN
  ABBREV_TAC `Cc = &2 * (cv * &(j + 1) * (cw * &(j + 1) * KI) * KI)` THEN
  SUBGOAL_THEN `&0 <= Cc` ASSUME_TAC THENL
   [EXPAND_TAC "Cc" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Cc:real`; `KI + Cc * L`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] THEN
  STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) z <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= j ==> p2c_dn 2 i (p2c_ginv (G:real^N->real^N^N)) z <= KI`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < j:num` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "KI" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> k <= x + k`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL];
      SUBGOAL_THEN `i = j:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c * p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) z + K` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "KI" THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + k <= b + k`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `KI:real` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> k <= k + x`) THEN ASM_SIMP_TAC[REAL_LE_MUL]];
    ALL_TAC] THEN
  (* fields *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_GINV_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `lmetric2 (G:real^N->real^N^N)`] P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `E = p2c_dn 2 (SUC j) (lmetric2 (G:real^N->real^N^N)) z` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m <= j ==> &0 <= p2c_dn 3 m (lnabla 2 p2c_flat (lmetric2 (G:real^N->real^N^N))) z /\
                   p2c_dn 3 m (lnabla 2 p2c_flat (lmetric2 G)) z <= L + E`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `m:num`; `lmetric2 (G:real^N->real^N^N)`; `z:real^N`] P2C_DN_SHIFT) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `m + 1 < SUC j` THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= e /\ x <= l ==> x <= l + e`) THEN
        ASM_SIMP_TAC[];
        SUBGOAL_THEN `m + 1 = SUC j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `Wt = p2c_wop p2c_flat (p2c_ginv (G:real^N->real^N^N))
                     (lnabla 2 p2c_flat (lmetric2 G))` THEN
  MP_TAC(ISPECL [`3`; `2`; `3`; `p2c_wop:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  REWRITE_TAC[P2C_WOP_LBILIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `p2c_ginv (G:real^N->real^N^N)`; `lnabla 2 p2c_flat (lmetric2 (G:real^N->real^N^N))`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. a <= j ==> &0 <= p2c_dn 3 a (Wt:real^N->(num->real^N)->real) z /\
                   p2c_dn 3 a Wt z <= cw * &(j + 1) * KI * (L + E)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cw * sum(0..a) (\b. p2c_dn 2 b (p2c_ginv (G:real^N->real^N^N)) z *
                    p2c_dn 3 (a - b) (lnabla 2 p2c_flat (lmetric2 G)) z)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Wt" THEN USE_THEN "lw" MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cw * &(a + 1) * KI * (L + E)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      X_GEN_TAC `b:num` THEN DISCH_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `Vt = p2c_vop p2c_flat (Wt:real^N->(num->real^N)->real)
                     (p2c_ginv (G:real^N->real^N^N))` THEN
  MP_TAC(ISPECL [`3`; `3`; `2`; `p2c_vop:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  REWRITE_TAC[P2C_VOP_LBILIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `Wt:real^N->(num->real^N)->real`; `p2c_ginv (G:real^N->real^N^N)`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2c_dn 3 j (Vt:real^N->(num->real^N)->real) z <=
    cv * &(j + 1) * (cw * &(j + 1) * KI * (L + E)) * KI`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cv * sum(0..j) (\a. p2c_dn 3 a (Wt:real^N->(num->real^N)->real) z *
                    p2c_dn 2 (j - a) (p2c_ginv (G:real^N->real^N^N)) z)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Vt" THEN USE_THEN "lv" MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LE_REFL];
      MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `b:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * p2c_dn 3 j (Vt:real^N->(num->real^N)->real) z` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `j:num`; `p2c_ginv (G:real^N->real^N^N)`; `z:real^N`] P2C_DN_SHIFT) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2c_dn 3 j (\y u. --((Vt:real^N->(num->real^N)->real) y u)) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2C_DN_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `w:num->real^N`] THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["Vt"; "Wt"] THEN MATCH_MP_TAC P2C_DGINV_FORM THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_DN_NEG_LE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    EXPAND_TAC "Cc" THEN
    SUBGOAL_THEN `&2 * (cv * &(j + 1) * (cw * &(j + 1) * KI) * KI) * (L + E) =
                  &2 * (cv * &(j + 1) * (cw * &(j + 1) * KI * (L + E)) * KI)` MP_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* Derivatives of the Christoffel tensor AF = Gamma(Ginv, d h). *)

let P2C_AF_DER = prove
 (`!L. &0 <= L
       ==> !j. ?c K. &0 <= c /\ &0 <= K /\
             !U (G:real^N->real^N^N) z.
               metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a)) /\
               (!i. i < j ==> p2c_dn 2 i (lmetric2 G) z <= L)
               ==> (!a. a + 1 < j ==> p2c_dn 3 a (p2c_af p2c_flat G) z <= K) /\
                   (!a. a + 1 <= j
                        ==> p2c_dn 3 a (p2c_af p2c_flat G) z <=
                            c * p2c_dn 2 j (lmetric2 G) z + K)`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP P2C_GINV_DER) THEN
  DISCH_THEN(X_CHOOSE_THEN `cg0:real` (X_CHOOSE_THEN `Kg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gi"))))) THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_GAM_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lg"))) THEN
  MAP_EVERY EXISTS_TAC [`cm * &j * Kg`; `cm * &j * Kg * L`] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] THEN
  STRIP_TAC THEN
  USE_THEN "gi" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_GINV_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `lmetric2 (G:real^N->real^N^N)`] P2C_FLAT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `E = p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) z` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m + 1 <= j
        ==> &0 <= p2c_dn 3 m (lnabla 2 p2c_flat (lmetric2 (G:real^N->real^N^N))) z /\
            p2c_dn 3 m (lnabla 2 p2c_flat (lmetric2 G)) z <= L + E /\
            (m + 1 < j ==> p2c_dn 3 m (lnabla 2 p2c_flat (lmetric2 G)) z <= L)`
  (LABEL_TAC "dh") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `m:num`; `lmetric2 (G:real^N->real^N^N)`; `z:real^N`] P2C_DN_SHIFT) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `m + 1 < j` THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= e /\ x <= l ==> x <= l + e`) THEN ASM_SIMP_TAC[];
        SUBGOAL_THEN `m + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a + 1 <= j
        ==> p2c_dn 3 a (p2c_af p2c_flat (G:real^N->real^N^N)) z <=
            cm * sum(0..a) (\b. p2c_dn 2 b (p2c_ginv G) z *
                                p2c_dn 3 (a - b) (lnabla 2 p2c_flat (lmetric2 G)) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2c_dn 3 a (p2c_gam p2c_flat (p2c_ginv (G:real^N->real^N^N))
                              (lnabla 2 p2c_flat (lmetric2 G))) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2C_DN_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2C_AF_FORM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "lg" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `a:num` THEN DISCH_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm * sum(0..a) (\b. p2c_dn 2 b (p2c_ginv (G:real^N->real^N^N)) z *
                    p2c_dn 3 (a - b) (lnabla 2 p2c_flat (lmetric2 G)) z)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm * &(a + 1) * Kg * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      X_GEN_TAC `b:num` THEN DISCH_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        USE_THEN "dh" (MP_TAC o SPEC `b:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_MUL]]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm * sum(0..a) (\b. p2c_dn 2 b (p2c_ginv (G:real^N->real^N^N)) z *
                    p2c_dn 3 (a - b) (lnabla 2 p2c_flat (lmetric2 G)) z)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm * &(a + 1) * Kg * (L + E)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      X_GEN_TAC `b:num` THEN DISCH_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        USE_THEN "dh" (MP_TAC o SPEC `b:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
      SUBGOAL_THEN `cm * &(a + 1) * Kg * (L + E) <= cm * &j * Kg * (L + E)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Flat versus covariant derivatives.  d T = nabla_G T +                     *)
(* ins(T, AF) (P2C_CONN_DIFF with G0 = p2c_flat), so with the Christoffel    *)
(* tensor bounded up to order m - 1, |d^b T|^2 is bounded by the covariant   *)
(* norms |nabla^i T|^2 (Euclidean), i <= b <= m (P2C_CONV); at the top     *)
(* order the term |T|^2 |d^(j-1) AF|^2 is kept separately (P2C_TOPCONV).    *)
(* ------------------------------------------------------------------------- *)

let P2C_PSUM_MONO = prove
 (`!(f:num->real) a b. (!i. &0 <= f i) /\ a <= b ==> sum(0..a) f <= sum(0..b) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN ARITH_TAC);;

let P2C_PSUM_SHIFT = prove
 (`!(f:num->real) m. (!i. &0 <= f i) ==> sum(0..m) (\i. f(i + 1)) <= sum(0..m + 1) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `f:num->real`; `0`; `m:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 = 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= x + s`) THEN ASM_REWRITE_TAC[]);;

let P2C_FLAT_CONN = prove
 (`!k U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) z u.
     metric_field U G /\ ltensor_field k U Tf /\ z IN U
     ==> lnabla k p2c_flat Tf z u =
         &1 * lnabla k G Tf z u + &1 * p2c_ins k p2c_flat Tf (p2c_af p2c_flat G) z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `Tf:real^N->(num->real^N)->real`; `z:real^N`; `u:num->real^N`]
                P2C_CONN_DIFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_FLAT_METRIC_FIELD THEN
    ASM_MESON_TAC[P2C_MF_OPEN];
    REAL_ARITH_TAC]);;

let P2C_COV_NORM_POS = prove
 (`!k i U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) z.
     metric_field U G /\ ltensor_field k U Tf /\ (!u. smooth_map_on U (\y. lift(Tf y u))) /\
     z IN U
     ==> &0 <= ltnorm2 (k + i) p2c_flat (lnabla_iter k i G Tf) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_FLAT_LTNORM2_POS THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `Tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[]);;

let P2C_CONV = prove
 (`!M. &0 <= M
       ==> !m k. 1 <= k
           ==> ?c. &0 <= c /\
                 !U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) z.
                   metric_field U G /\ z IN U /\ ltensor_field k U Tf /\
                   (!u. smooth_map_on U (\y. lift(Tf y u))) /\
                   (!a. a < m ==> p2c_dn 3 a (p2c_af p2c_flat G) z <= M)
                   ==> !b. b <= m
                           ==> p2c_dn k b Tf z <=
                               c * sum(0..b) (\i. ltnorm2 (k + i) p2c_flat
                                                    (lnabla_iter k i G Tf) z)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS; LE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p2c_dn; lnabla_iter; SUM_SING_NUMSEG; ADD_CLAUSES; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ck"))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k + 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ck1"))) THEN
  MP_TAC(SPEC `m:num` (MATCH_MP P2C_LEIBNIZ_UPTO
    (MATCH_MP (INST_TYPE [`:N`,`:N`] P2C_INS_LBILIN) (ASSUME `1 <= k`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ci:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "li"))) THEN
  EXISTS_TAC `ck + &2 * ck1 + &2 * ci * &(m + 1) * ck * M` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `Tf:real^N->(num->real^N)->real`; `z:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `Nf = \i. ltnorm2 (k + i) p2c_flat
                        (lnabla_iter k i (G:real^N->real^N^N) Tf) (z:real^N)` THEN
  SUBGOAL_THEN `!i. &0 <= (Nf:num->real) i` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Nf" THEN BETA_TAC THEN MATCH_MP_TAC P2C_COV_NORM_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b. &0 <= sum(0..b) (Nf:num->real)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ck" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                 `Tf:real^N->(num->real^N)->real`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bk") THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN ASM_CASES_TAC `b <= m:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ck * sum(0..b) (Nf:num->real)` THEN
    CONJ_TAC THENL [USE_THEN "bk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> c <= c + x`) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b = SUC m:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = sum(0..SUC m) (Nf:num->real)` THEN
  (* fields *)
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `Tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `k:num`; `3`;
                 `p2c_ins k:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
                P2C_LBILIN_ON_SMOOTH) THEN
  ASM_SIMP_TAC[P2C_INS_LBILIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `Tf:real^N->(num->real^N)->real`; `p2c_af p2c_flat (G:real^N->real^N^N)`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * &1 pow 2 * p2c_dn (k + 1) m (lnabla k G (Tf:real^N->(num->real^N)->real)) z +
              &2 * &1 pow 2 * p2c_dn (k + 1) m
                (p2c_ins k p2c_flat Tf (p2c_af p2c_flat (G:real^N->real^N^N))) z` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ADD1; GSYM P2C_DN_SHIFT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2c_dn (k + 1) m
      (\y u. &1 * lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) y u +
             &1 * p2c_ins k p2c_flat Tf (p2c_af p2c_flat G) y u) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2C_DN_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2C_FLAT_CONN THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_DN_LINCOMB THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `p2c_dn (k + 1) m (lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real)) z <=
    ck1 * S`
  ASSUME_TAC THENL
   [USE_THEN "ck1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real)`;
                     `z:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2C_LNABLA_ITER_SHIFT; ARITH_RULE `(k + 1) + i = k + i + 1`] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[ADD1] THEN
    MP_TAC(ISPECL [`Nf:num->real`; `m:num`] P2C_PSUM_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Nf" THEN REWRITE_TAC[ADD_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_dn (k + 1) m (p2c_ins k p2c_flat (Tf:real^N->(num->real^N)->real)
                        (p2c_af p2c_flat (G:real^N->real^N^N))) z <=
    ci * &(m + 1) * (ck * S) * M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ci * sum(0..m) (\a. p2c_dn k a (Tf:real^N->(num->real^N)->real) z *
                    p2c_dn 3 (m - a) (p2c_af p2c_flat (G:real^N->real^N^N)) z)` THEN
    CONJ_TAC THENL
     [USE_THEN "li" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ck * sum(0..a) (Nf:num->real)` THEN
      CONJ_TAC THENL [USE_THEN "bk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
      MATCH_MP_TAC P2C_PSUM_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ck * S >= &0 /\ (ci * &(m + 1) * (ck * S) * M) =
                (ci * &(m + 1) * ck * M) * S` MP_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[real_ge] THEN ASM_SIMP_TAC[REAL_LE_MUL]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ck * S` MP_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_TOPCONV = prove
 (`!M j k. &0 <= M /\ 1 <= j /\ 1 <= k
     ==> ?c. &0 <= c /\
           !U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) z.
             metric_field U G /\ z IN U /\ ltensor_field k U Tf /\
             (!u. smooth_map_on U (\y. lift(Tf y u))) /\
             (!a. a + 1 < j ==> p2c_dn 3 a (p2c_af p2c_flat G) z <= M)
             ==> p2c_dn k j Tf z <=
                 c * sum(0..j) (\i. ltnorm2 (k + i) p2c_flat (lnabla_iter k i G Tf) z) +
                 c * p2c_dn k 0 Tf z * p2c_dn 3 (j - 1) (p2c_af p2c_flat G) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m. j = m + 1` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(m + 1) - 1 = m`] THEN
  MP_TAC(SPECL [`m:num`; `k + 1`] (MATCH_MP P2C_CONV (ASSUME `&0 <= M`))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ck1"))) THEN
  MP_TAC(SPECL [`m:num`; `k:num`] (MATCH_MP P2C_CONV (ASSUME `&0 <= M`))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ck"))) THEN
  MP_TAC(SPEC `m:num` (MATCH_MP P2C_LEIBNIZ_UPTO
    (MATCH_MP (INST_TYPE [`:N`,`:N`] P2C_INS_LBILIN) (ASSUME `1 <= k`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ci:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "li"))) THEN
  EXISTS_TAC `&2 * ck1 + &2 * ci * &m * ck * M + &2 * ci` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `Tf:real^N->(num->real^N)->real`; `z:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `Nf = \i. ltnorm2 (k + i) p2c_flat
                        (lnabla_iter k i (G:real^N->real^N^N) Tf) (z:real^N)` THEN
  SUBGOAL_THEN `!i. &0 <= (Nf:num->real) i` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Nf" THEN BETA_TAC THEN MATCH_MP_TAC P2C_COV_NORM_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = sum(0..m + 1) (Nf:num->real)` THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D0 = p2c_dn k 0 (Tf:real^N->(num->real^N)->real) z` THEN
  ABBREV_TAC `Fm = p2c_dn 3 m (p2c_af p2c_flat (G:real^N->real^N^N)) z` THEN
  SUBGOAL_THEN `&0 <= D0 /\ &0 <= Fm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D0"; "Fm"] THEN CONJ_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2C_AF_FIELD THEN ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD];
    ALL_TAC] THEN
  USE_THEN "ck" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                 `Tf:real^N->(num->real^N)->real`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bk") THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `Tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `k:num`; `3`;
                 `p2c_ins k:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
                P2C_LBILIN_ON_SMOOTH) THEN
  ASM_SIMP_TAC[P2C_INS_LBILIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
    `Tf:real^N->(num->real^N)->real`; `p2c_af p2c_flat (G:real^N->real^N^N)`]) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * &1 pow 2 * p2c_dn (k + 1) m (lnabla k G (Tf:real^N->(num->real^N)->real)) z +
              &2 * &1 pow 2 * p2c_dn (k + 1) m
                (p2c_ins k p2c_flat Tf (p2c_af p2c_flat (G:real^N->real^N^N))) z` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM P2C_DN_SHIFT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2c_dn (k + 1) m
      (\y u. &1 * lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) y u +
             &1 * p2c_ins k p2c_flat Tf (p2c_af p2c_flat G) y u) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2C_DN_LOCAL THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2C_FLAT_CONN THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_DN_LINCOMB THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `p2c_dn (k + 1) m (lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real)) z <=
    ck1 * S`
  ASSUME_TAC THENL
   [USE_THEN "ck1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `lnabla k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real)`;
                     `z:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2C_LNABLA_ITER_SHIFT; ARITH_RULE `(k + 1) + i = k + i + 1`] THEN
    EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`Nf:num->real`; `m:num`] P2C_PSUM_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Nf" THEN REWRITE_TAC[ADD_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_dn (k + 1) m (p2c_ins k p2c_flat (Tf:real^N->(num->real^N)->real)
                        (p2c_af p2c_flat (G:real^N->real^N^N))) z <=
    ci * (D0 * Fm + &m * (ck * S) * M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ci * sum(0..m) (\a. p2c_dn k a (Tf:real^N->(num->real^N)->real) z *
                    p2c_dn 3 (m - a) (p2c_af p2c_flat (G:real^N->real^N^N)) z)` THEN
    CONJ_TAC THENL
     [USE_THEN "li" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 = 1`; SUB_0] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..m) (\a:num. (ck * S) * M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ck * sum(0..a) (Nf:num->real)` THEN
        CONJ_TAC THENL [USE_THEN "bk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
        MATCH_MP_TAC P2C_PSUM_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(m + 1) - 1 = m`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ck * S /\ &0 <= D0 * Fm` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ci * (D0 * Fm + &m * (ck * S) * M) = ci * &m * ck * M * S + ci * (D0 * Fm)` SUBST_ALL_TAC
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * ck1 + &2 * ci * &m * ck * M + &2 * ci) * S =
                &2 * ck1 * S + &2 * ci * &m * ck * M * S + &2 * ci * S` SUBST1_TAC
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * ck1 + &2 * ci * &m * ck * M + &2 * ci) * D0 * Fm =
                &2 * ck1 * D0 * Fm + &2 * ci * &m * ck * M * D0 * Fm + &2 * ci * (D0 * Fm)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * ci * S /\ &0 <= &2 * ck1 * D0 * Fm /\
                &0 <= &2 * ci * &m * ck * M * D0 * Fm`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The radial equations and the structure estimate.                         *)
(*   j d^j h + D d^j h = 2 d^j Phi,                                          *)
(*   (1 + j) d^j Phi + D d^j Phi = d^j S,  S = Q + Phi Ginv Phi,             *)
(* and |d^j S|^2 <= c (C0 |z|^2)^2 (|d^j h|^2 + |d^j Phi|^2) + K under the   *)
(* lower-order, curvature and base bounds.                                   *)
(* ------------------------------------------------------------------------- *)

let P2C_XT_FIELD = prove
 (`!U:real^N->bool.
     open U ==> ltensor_field 1 U p2c_xt /\ (!u. smooth_map_on U (\y. lift(p2c_xt y u)))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ltensor_field; p2c_xt] THEN REPEAT STRIP_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT]];
    REWRITE_TAC[p2c_xt] THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_DOT]]);;

let P2C_XT_D = prove
 (`!U (z:real^N) u. open U /\ z IN U
     ==> lnabla 1 p2c_flat p2c_xt z u = lmetric2 p2c_flat z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` P2C_XT_FIELD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `p2c_xt:real^N->(num->real^N)->real`; `z:real^N`;
                 `u:num->real^N`] P2C_FLAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2c_xt; lmetric2; P2C_FLAT_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`\x:real^N. lift((u:num->real^N) 1 dot x)`; `at (z:real^N)`]
                HAS_DERIVATIVE_LINEAR) THEN
  REWRITE_TAC[LINEAR_LIFT_DOT] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP]);;

let P2C_XT_DN0 = prove
 (`!z:real^N. p2c_dn 1 0 p2c_xt z = norm z pow 2`,
  GEN_TAC THEN REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES; P2C_LTNORM2_1] THEN
  REWRITE_TAC[P2C_FLAT_CONTR; p2c_xt] THEN REWRITE_TAC[NORM_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let P2C_XT_DN_LE = prove
 (`!U (z:real^N) b. open U /\ z IN U
     ==> p2c_dn 1 b p2c_xt z <= norm z pow 2 + &(CARD(index_tuples 2 (:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &(CARD(index_tuples 2 (:N)))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
   [ASM_REWRITE_TAC[P2C_XT_DN0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?l. b = l + 1` (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `b - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM P2C_DN_SHIFT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p2c_dn 2 l (lnabla 1 p2c_flat p2c_xt) (z:real^N) =
                p2c_dn 2 l (lmetric2 p2c_flat) z` SUBST1_TAC THENL
   [MATCH_MP_TAC P2C_DN_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_XT_D THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ x <= c ==> x <= n + c`) THEN
  REWRITE_TAC[NORM_POW_2; DOT_POS_LE] THEN
  ASM_CASES_TAC `l = 0` THENL
   [ASM_REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES] THEN
    REWRITE_TAC[P2C_LMETRIC2_EQ; P2C_FLAT_MUL] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(\z. mat 1):real^N->real^N^N`; `z:real^N`; `&1`]
                  P2C_ENTRY_LTNORM2) THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST] THEN
    SIMP_TAC[DOT_BASIS_BASIS] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?l'. l = SUC l'` (X_CHOOSE_THEN `l':num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `l - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= c ==> x <= c`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p2c_dn] THEN
  MATCH_MP_TAC P2C_LTNORM2_ZERO THEN GEN_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` P2C_FLAT_METRIC_FIELD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LRG_LNABLA_ITER_METRIC) THEN ASM_SIMP_TAC[]);;

(* The source term S = Q + Phi Ginv Phi as a bilinear expression. *)

let p2c_qt = new_definition
 `p2c_qt (G:real^N->real^N^N) =
    p2c_q2op p2c_flat (p2c_q1op p2c_flat (lrm4 G) p2c_xt) p2c_xt`;;

let p2c_pgp = new_definition
 `p2c_pgp (G:real^N->real^N^N) =
    p2c_mp p2c_flat (p2c_mp p2c_flat (p2c_phi G) (p2c_ginv G)) (p2c_phi G)`;;

let p2c_ss = new_definition
 `p2c_ss (G:real^N->real^N^N) = \z u. &1 * p2c_qt G z u + &1 * p2c_pgp G z u`;;

let P2C_OP_FIELD_TAC th =
  MP_TAC(MATCH_MP P2C_LBILIN_ON_SMOOTH (INST_TYPE [`:N`,`:N`] th)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD];;

let P2C_QT_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (p2c_qt G) /\ (!u. smooth_map_on U (\y. lift(p2c_qt G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^N->bool` P2C_XT_FIELD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 3 U (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) /\
    (!u. smooth_map_on U (\y. lift(p2c_q1op p2c_flat (lrm4 G) p2c_xt y u)))`
  STRIP_ASSUME_TAC THENL [P2C_OP_FIELD_TAC P2C_Q1OP_LBILIN; ALL_TAC] THEN
  REWRITE_TAC[p2c_qt] THEN P2C_OP_FIELD_TAC P2C_Q2OP_LBILIN);;

let P2C_PGP_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (p2c_pgp G) /\ (!u. smooth_map_on U (\y. lift(p2c_pgp G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_GINV_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 2 U (p2c_mp p2c_flat (p2c_phi (G:real^N->real^N^N)) (p2c_ginv G)) /\
    (!u. smooth_map_on U (\y. lift(p2c_mp p2c_flat (p2c_phi G) (p2c_ginv G) y u)))`
  STRIP_ASSUME_TAC THENL [P2C_OP_FIELD_TAC P2C_MP_LBILIN; ALL_TAC] THEN
  REWRITE_TAC[p2c_pgp] THEN P2C_OP_FIELD_TAC P2C_MP_LBILIN);;

let P2C_SS_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (p2c_ss G) /\ (!u. smooth_map_on U (\y. lift(p2c_ss G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_QT_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PGP_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_ss] THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[]]);;

(* The radial equations for d^j h and d^j Phi. *)

let P2C_RAD_H = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> !j z u. z IN U
                 ==> &j * lnabla_iter 2 j p2c_flat (lmetric2 G) z u +
                     p2c_dx (2 + j) (lnabla_iter 2 j p2c_flat (lmetric2 G)) z u =
                     &2 * lnabla_iter 2 j p2c_flat (p2c_phi G) z u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `lmetric2 (G:real^N->real^N^N)`]
                P2C_DX_COMM_ITER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`j:num`; `z:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a = c + d ==> d + c = b`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla_iter 2 j p2c_flat
                (\y u. &2 * p2c_phi (G:real^N->real^N^N) y u + &0 * p2c_phi G y u) z u` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `p2c_flat:real^N->real^N^N`; `p2c_flat:real^N->real^N^N`;
                   `p2c_dx 2 (lmetric2 (G:real^N->real^N^N))`;
                   `\y u. &2 * p2c_phi (G:real^N->real^N^N) y u + &0 * p2c_phi G y u`;
                   `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      MATCH_MP_TAC P2C_DX_H THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                   `p2c_phi (G:real^N->real^N^N)`; `p2c_phi (G:real^N->real^N^N)`;
                   `&2`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN REAL_ARITH_TAC]);;

let P2C_RAD_PHI = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G /\ (!z. z IN U ==> G z ** z = z)
     ==> !j z u. z IN U
                 ==> &(1 + j) * lnabla_iter 2 j p2c_flat (p2c_phi G) z u +
                     p2c_dx (2 + j) (lnabla_iter 2 j p2c_flat (p2c_phi G)) z u =
                     lnabla_iter 2 j p2c_flat (p2c_ss G) z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `p2c_phi (G:real^N->real^N^N)`] P2C_DX_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `p2c_phi (G:real^N->real^N^N)`]
                P2C_DX_COMM_ITER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`j:num`; `z:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla_iter 2 j p2c_flat
                (\y u. &1 * p2c_phi (G:real^N->real^N^N) y u +
                       &1 * p2c_dx 2 (p2c_phi G) y u) z u` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                   `p2c_phi (G:real^N->real^N^N)`; `p2c_dx 2 (p2c_phi (G:real^N->real^N^N))`;
                   `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`2`; `p2c_flat:real^N->real^N^N`; `p2c_flat:real^N->real^N^N`;
                   `\y u. &1 * p2c_phi (G:real^N->real^N^N) y u +
                          &1 * p2c_dx 2 (p2c_phi G) y u`;
                   `p2c_ss (G:real^N->real^N^N)`; `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `w:num->real^N`] THEN
      DISCH_TAC THEN REWRITE_TAC[p2c_ss; p2c_qt; p2c_pgp; REAL_MUL_LID] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:num->real^N`]
                    P2C_RICCATI) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:num->real^N`]
                    P2C_Q_FORM) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:num->real^N`]
                    P2C_PGP_FORM) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* Splitting off the extreme terms of a Leibniz sum. *)

let P2C_SUM_LAST_SPLIT = prove
 (`!(f:num->real) g j Fm Gm.
     1 <= j /\ (!a. a < j ==> &0 <= f a /\ f a <= Fm) /\
     (!b. 1 <= b /\ b <= j ==> &0 <= g b /\ g b <= Gm)
     ==> sum(0..j) (\a. f a * g(j - a)) <= f j * g 0 + &j * Fm * Gm`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m. j = m + 1` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; SUM_SING_NUMSEG; SUB_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= t ==> s + x <= x + t`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..m) (\a:num. Fm * Gm)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(m + 1) - a`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(m + 1) - 0 = m + 1`] THEN
    REAL_ARITH_TAC]);;

let P2C_SUM_ENDS_SPLIT = prove
 (`!(f:num->real) g j Fm Gm.
     1 <= j /\ &0 <= Fm /\ &0 <= Gm /\
     (!a. 0 < a /\ a < j ==> &0 <= f a /\ f a <= Fm) /\
     (!b. 0 < b /\ b < j ==> &0 <= g b /\ g b <= Gm)
     ==> sum(0..j) (\a. f a * g(j - a)) <= f j * g 0 + f 0 * g j + &j * Fm * Gm`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m. j = m + 1` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; SUM_SING_NUMSEG; SUB_REFL] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; SUB_0; ARITH_RULE `0 + 1 = 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= t ==> (y + s) + x <= x + y + t`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..m) (\a:num. Fm * Gm)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(m + 1) - a`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(m + 1) - 1 = m`] THEN
    SUBGOAL_THEN `&0 <= Fm * Gm` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL]; REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]]);;

(* The curvature part Q = Rm(z,.,.,z) of S. *)

let P2C_QT_BOUND = prove
 (`!j KR rho. 1 <= j /\ &0 <= KR /\ &0 <= rho
     ==> ?c K. &0 <= c /\ &0 <= K /\
           !U (G:real^N->real^N^N) z.
             metric_field U G /\ z IN U /\ norm z <= rho /\
             (!b. b < j ==> p2c_dn 4 b (lrm4 G) z <= KR)
             ==> p2c_dn 2 j (p2c_qt G) z <= c * norm z pow 4 * p2c_dn 4 j (lrm4 G) z + K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_Q2OP_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2"))) THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_Q1OP_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1"))) THEN
  ABBREV_TAC `Xm = rho pow 2 + &(CARD(index_tuples 2 (:N)))` THEN
  SUBGOAL_THEN `&0 <= Xm` ASSUME_TAC THENL
   [EXPAND_TAC "Xm" THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `Q1m = c1 * &j * KR * Xm` THEN
  SUBGOAL_THEN `&0 <= Q1m` ASSUME_TAC THENL
   [EXPAND_TAC "Q1m" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`c2 * c1`; `c2 * c1 * &j * KR * Xm * rho pow 2 + c2 * &j * Q1m * Xm`] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^N->bool` P2C_XT_FIELD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 3 U (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) /\
    (!u. smooth_map_on U (\y. lift(p2c_q1op p2c_flat (lrm4 G) p2c_xt y u)))`
  STRIP_ASSUME_TAC THENL [P2C_OP_FIELD_TAC P2C_Q1OP_LBILIN; ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^N) pow 2 <= rho pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!b. &0 <= p2c_dn 1 b p2c_xt (z:real^N) /\ p2c_dn 1 b p2c_xt z <= Xm`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(z:real^N) pow 2 + &(CARD(index_tuples 2 (:N)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2C_XT_DN_LE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "Xm" THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b. &0 <= p2c_dn 4 b (lrm4 (G:real^N->real^N^N)) z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < j ==> &0 <= p2c_dn 3 a (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) z /\
                  p2c_dn 3 a (p2c_q1op p2c_flat (lrm4 G) p2c_xt) z <= Q1m`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c1 * sum(0..a) (\b. p2c_dn 4 b (lrm4 (G:real^N->real^N^N)) z *
                                   p2c_dn 1 (a - b) p2c_xt z)` THEN
    CONJ_TAC THENL
     [USE_THEN "l1" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 * &(a + 1) * KR * Xm` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      EXPAND_TAC "Q1m" THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_OF_NUM_LE; ARITH_RULE `a < j ==> a + 1 <= j`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_dn 3 j (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) z <=
    c1 * (p2c_dn 4 j (lrm4 G) z * norm z pow 2 + &j * KR * Xm)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c1 * sum(0..j) (\b. p2c_dn 4 b (lrm4 (G:real^N->real^N^N)) z *
                                   p2c_dn 1 (j - b) p2c_xt z)` THEN
    CONJ_TAC THENL
     [USE_THEN "l1" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM P2C_XT_DN0] THEN
    MATCH_MP_TAC P2C_SUM_LAST_SPLIT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c2 * sum(0..j) (\a. p2c_dn 3 a (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N))
                                                p2c_xt) z * p2c_dn 1 (j - a) p2c_xt z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2c_qt] THEN USE_THEN "l2" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c2 * (p2c_dn 3 j (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) z *
                    norm(z:real^N) pow 2 + &j * Q1m * Xm)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM P2C_XT_DN0] THEN
    MATCH_MP_TAC P2C_SUM_LAST_SPLIT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c2 * p2c_dn 3 j (p2c_q1op p2c_flat (lrm4 (G:real^N->real^N^N)) p2c_xt) z * norm(z:real^N) pow 2
    <= c2 * (c1 * (p2c_dn 4 j (lrm4 G) z * norm z pow 2 + &j * KR * Xm)) * norm z pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `c2 * c1 * &j * KR * Xm * norm(z:real^N) pow 2 <=
                c2 * c1 * &j * KR * Xm * rho pow 2` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN TRY(ASM_REWRITE_TAC[REAL_POS])) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN REAL_ARITH_TAC);;

(* The quadratic part Phi Ginv Phi of S. *)

let P2C_PGP_BOUND = prove
 (`!j L KI Pm. 1 <= j /\ &0 <= L /\ &0 <= KI /\ &0 <= Pm
     ==> ?c K. &0 <= c /\ &0 <= K /\
           !U (G:real^N->real^N^N) z.
             metric_field U G /\ z IN U /\
             (!b. b < j ==> p2c_dn 2 b (p2c_phi G) z <= L /\ p2c_dn 2 b (p2c_ginv G) z <= KI) /\
             p2c_dn 2 0 (p2c_phi G) z <= Pm
             ==> p2c_dn 2 j (p2c_pgp G) z <=
                 c * p2c_dn 2 0 (p2c_phi G) z *
                     (p2c_dn 2 j (p2c_phi G) z + p2c_dn 2 j (p2c_ginv G) z) + K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `j:num` (MATCH_MP P2C_LEIBNIZ_UPTO (INST_TYPE [`:N`,`:N`] P2C_MP_LBILIN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lm"))) THEN
  ABBREV_TAC `Ym = cm * &j * L * KI` THEN
  SUBGOAL_THEN `&0 <= Ym` ASSUME_TAC THENL
   [EXPAND_TAC "Ym" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`&2 * cm * cm * KI + cm * cm * Pm`; `cm * cm * &j * L * KI * Pm + cm * &j * Ym * L`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "low") ASSUME_TAC))) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_GINV_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Yt = p2c_mp p2c_flat (p2c_phi (G:real^N->real^N^N)) (p2c_ginv G)` THEN
  SUBGOAL_THEN
   `ltensor_field 2 U (Yt:real^N->(num->real^N)->real) /\
    (!u. smooth_map_on U (\y. lift(Yt y u)))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "Yt" THEN P2C_OP_FIELD_TAC P2C_MP_LBILIN; ALL_TAC] THEN
  ABBREV_TAC `P0 = p2c_dn 2 0 (p2c_phi (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `Pj = p2c_dn 2 j (p2c_phi (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `Ij = p2c_dn 2 j (p2c_ginv (G:real^N->real^N^N)) z` THEN
  SUBGOAL_THEN `!b. &0 <= p2c_dn 2 b (p2c_phi (G:real^N->real^N^N)) z /\
                    &0 <= p2c_dn 2 b (p2c_ginv G) z /\
                    &0 <= p2c_dn 2 b (Yt:real^N->(num->real^N)->real) z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P0 /\ &0 <= Pj /\ &0 <= Ij` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P0"; "Pj"; "Ij"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. a < j ==> p2c_dn 2 a (Yt:real^N->(num->real^N)->real) z <= Ym`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm * sum(0..a) (\b. p2c_dn 2 b (p2c_phi (G:real^N->real^N^N)) z *
                                   p2c_dn 2 (a - b) (p2c_ginv G) z)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Yt" THEN USE_THEN "lm" MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm * &(a + 1) * L * KI` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LEIB_BOUND THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
      USE_THEN "low" (MP_TAC o SPEC `b:num`) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);
      EXPAND_TAC "Ym" THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_OF_NUM_LE; ARITH_RULE `a < j ==> a + 1 <= j`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_dn 2 0 (p2c_ginv (G:real^N->real^N^N)) z <= KI /\
                p2c_dn 2 0 (p2c_phi G) z <= L` STRIP_ASSUME_TAC THENL
   [USE_THEN "low" (MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_dn 2 0 (Yt:real^N->(num->real^N)->real) z <= cm * P0 * KI` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm * sum(0..0) (\b. p2c_dn 2 b (p2c_phi (G:real^N->real^N^N)) z *
                                   p2c_dn 2 (0 - b) (p2c_ginv G) z)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Yt" THEN USE_THEN "lm" MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LE_0];
      REWRITE_TAC[SUM_SING_NUMSEG; SUB_REFL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_dn 2 j (Yt:real^N->(num->real^N)->real) z <=
                cm * (Pj * KI + P0 * Ij + &j * L * KI)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm * sum(0..j) (\b. p2c_dn 2 b (p2c_phi (G:real^N->real^N^N)) z *
                                   p2c_dn 2 (j - b) (p2c_ginv G) z)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Yt" THEN USE_THEN "lm" MATCH_MP_TAC THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Pj * p2c_dn 2 0 (p2c_ginv (G:real^N->real^N^N)) z + P0 * Ij + &j * L * KI` THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Pj"; "P0"; "Ij"] THEN
      MATCH_MP_TAC P2C_SUM_ENDS_SPLIT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      USE_THEN "low" (MP_TAC o SPEC `b:num`) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cm * sum(0..j) (\a. p2c_dn 2 a (Yt:real^N->(num->real^N)->real) z *
                                 p2c_dn 2 (j - a) (p2c_phi (G:real^N->real^N^N)) z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2c_pgp] THEN ASM_REWRITE_TAC[] THEN USE_THEN "lm" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cm * (p2c_dn 2 j (Yt:real^N->(num->real^N)->real) z * P0 +
                    p2c_dn 2 0 Yt z * Pj + &j * Ym * L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["Pj"; "P0"] THEN
    MATCH_MP_TAC P2C_SUM_ENDS_SPLIT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `b:num` THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      USE_THEN "low" (MP_TAC o SPEC `b:num`) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_dn 2 j (Yt:real^N->(num->real^N)->real) z * P0 <=
    (cm * (Pj * KI + P0 * Ij + &j * L * KI)) * P0 /\
    p2c_dn 2 0 Yt z * Pj <= (cm * P0 * KI) * Pj /\
    P0 * P0 * Ij <= Pm * P0 * Ij /\ P0 * (&j * L * KI) <= Pm * (&j * L * KI)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
      MAP_EVERY EXPAND_TAC ["P0"] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      MAP_EVERY EXPAND_TAC ["P0"] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cm * (p2c_dn 2 j (Yt:real^N->(num->real^N)->real) z * P0 + p2c_dn 2 0 Yt z * Pj +
          &j * Ym * L) <=
    cm * (cm * (Pj * KI + P0 * Ij + &j * L * KI) * P0 + (cm * P0 * KI) * Pj + &j * Ym * L)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cm * cm * KI * P0 * Ij /\ &0 <= cm * cm * Pm * P0 * Pj /\
                cm * cm * (P0 * P0 * Ij) <= cm * cm * (Pm * P0 * Ij) /\
                cm * cm * (P0 * (&j * L * KI)) <= cm * cm * (Pm * (&j * L * KI))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Curvature norms in Euclidean form. *)

let P2C_RMD_FLAT = prove
 (`!U (G:real^N->real^N^N) z i.
     metric_field U G /\ z IN U /\
     (!a. inv(&2) * (a dot a) <= a dot (G z ** a) /\ a dot (G z ** a) <= &2 * (a dot a))
     ==> ltnorm2 (4 + i) p2c_flat (lnabla_iter 4 i G (lrm4 G)) z <=
         &2 pow (4 + i) * lrm_deriv_norm2 i G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`]
                LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4 + i`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla_iter 4 i (G:real^N->real^N^N) (lrm4 G)`; `z:real^N`]
                P2C_FLAT_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2C_RMD_SUM = prove
 (`!U (G:real^N->real^N^N) z j Cc b.
     metric_field U G /\ z IN U /\
     (!a. inv(&2) * (a dot a) <= a dot (G z ** a) /\ a dot (G z ** a) <= &2 * (a dot a)) /\
     (!i. i <= j ==> lrm_deriv_norm2 i G z <= Cc) /\ &0 <= Cc /\ b <= j
     ==> sum(0..b) (\i. ltnorm2 (4 + i) p2c_flat (lnabla_iter 4 i G (lrm4 G)) z) <=
         &(j + 1) * &2 pow (4 + j) * Cc`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..b) (\i:num. &2 pow (4 + j) * Cc)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow (4 + i) * lrm_deriv_norm2 i (G:real^N->real^N^N) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_RMD_FLAT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC[REAL_POW_LE; REAL_POS];
        MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REWRITE_TAC[lrm_deriv_norm2] THEN MATCH_MP_TAC LTNORM2_POS THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                       `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(b + 1) - 0 = b + 1`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

(* The structure estimate for d^j S. *)

let P2C_SS_BOUND = prove
 (`!j L Cc rho. 1 <= j /\ &0 <= L /\ &0 <= Cc /\ &0 <= rho
     ==> ?c K. &0 <= c /\ &0 <= K /\
           !U (G:real^N->real^N^N) z C0.
             metric_field U G /\ z IN U /\ norm z <= rho /\ &0 <= C0 /\
             C0 * norm z pow 2 <= &1 /\
             (!a. inv(&2) * (a dot a) <= a dot (G z ** a) /\
                  a dot (G z ** a) <= &2 * (a dot a)) /\
             (!a. abs(a dot (mderiv G z z ** a)) <= &4 * C0 * norm z pow 2 * (a dot a)) /\
             (!i. i <= j ==> lrm_deriv_norm2 i G z <= Cc) /\
             lrm_deriv_norm2 0 G z <= C0 pow 2 /\
             (!i. i < j ==> p2c_dn 2 i (lmetric2 G) z <= L /\ p2c_dn 2 i (p2c_phi G) z <= L)
             ==> p2c_dn 2 j (p2c_ss G) z <=
                 c * (C0 * norm z pow 2) pow 2 *
                     (p2c_dn 2 j (lmetric2 G) z + p2c_dn 2 j (p2c_phi G) z) + K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP P2C_GINV_DER o
    check (fun th -> concl th = `&0 <= L`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `cI:real` (X_CHOOSE_THEN `KI:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gi"))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP P2C_AF_DER o
    check (fun th -> concl th = `&0 <= L`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `cF:real` (X_CHOOSE_THEN `KF:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "af"))))) THEN
  MP_TAC(SPECL [`j - 1`; `4`] (MATCH_MP P2C_CONV (ASSUME `&0 <= KF`))) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `cR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cv"))) THEN
  MP_TAC(SPECL [`KF:real`; `j:num`; `4`] P2C_TOPCONV) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `cT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tc"))) THEN
  ABBREV_TAC `NB = &(j + 1) * &2 pow (4 + j) * Cc` THEN
  SUBGOAL_THEN `&0 <= NB` ASSUME_TAC THENL
   [EXPAND_TAC "NB" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`j:num`; `cR * NB`; `rho:real`] P2C_QT_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cQ:real` (X_CHOOSE_THEN `KQ:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qb"))))) THEN
  ABBREV_TAC `C2 = &(CARD(index_tuples 2 (:N)))` THEN
  SUBGOAL_THEN `&0 <= C2` ASSUME_TAC THENL [EXPAND_TAC "C2" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`j:num`; `L:real`; `KI:real`; `&4 * C2`] P2C_PGP_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cP:real` (X_CHOOSE_THEN `KP:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pb"))))) THEN
  EXISTS_TAC `&2 * cQ * cT * &16 * cF + &2 * cP * &4 * C2 * (&1 + cI)` THEN
  EXISTS_TAC `&2 * (cQ * rho pow 4 * cT * NB + cQ * cT * &16 * KF + KQ) +
              &2 * (cP * &4 * C2 * KI + KP)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `C0:real`] THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
      [a1;a2;a3;a4;a5;a6;a7;a8;a9;a10] ->
        MAP_EVERY ASSUME_TAC [a1;a2;a3;a4;a5] THEN LABEL_TAC "gb" a6 THEN
        LABEL_TAC "hess" a7 THEN LABEL_TAC "cc" a8 THEN LABEL_TAC "r0" a9 THEN
        LABEL_TAC "low" a10
    | _ -> failwith "P2C_SS_BOUND: hypotheses") THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2C_MF_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_GINV_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_QT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] P2C_PGP_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  (* Ginv and AF derivative bounds at z *)
  USE_THEN "gi" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    TRY(USE_THEN "gb" (MP_TAC o SPEC `a:real^N`) THEN SIMP_TAC[] THEN NO_TAC) THEN
    USE_THEN "low" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ilow") (LABEL_TAC "itop"))] THEN
  USE_THEN "af" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    TRY(USE_THEN "gb" (MP_TAC o SPEC `a:real^N`) THEN SIMP_TAC[] THEN NO_TAC) THEN
    USE_THEN "low" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "flow") (LABEL_TAC "ftop"))] THEN
  (* curvature derivatives below the top order *)
  SUBGOAL_THEN `!b. b < j ==> p2c_dn 4 b (lrm4 (G:real^N->real^N^N)) z <= cR * NB`
  (LABEL_TAC "rlow") THENL
   [X_GEN_TAC `b:num` THEN DISCH_TAC THEN
    USE_THEN "cv" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                   `lrm4 (G:real^N->real^N^N)`; `z:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "flow" MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `b:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "NB" THEN
    MATCH_MP_TAC P2C_RMD_SUM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the top curvature derivative *)
  SUBGOAL_THEN `p2c_dn 4 0 (lrm4 (G:real^N->real^N^N)) z <= &16 * C0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow (4 + 0) * lrm_deriv_norm2 0 (G:real^N->real^N^N) z` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `0`]
                    P2C_RMD_FLAT) THEN
      ASM_REWRITE_TAC[p2c_dn; lnabla_iter];
      CONV_TAC NUM_REDUCE_CONV THEN USE_THEN "r0" MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_dn 4 j (lrm4 (G:real^N->real^N^N)) z <=
    cT * NB + cT * (&16 * C0 pow 2) *
              (cF * p2c_dn 2 j (lmetric2 G) z + KF)`
  ASSUME_TAC THENL
   [USE_THEN "tc" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                   `lrm4 (G:real^N->real^N^N)`; `z:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "flow" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> x <= a + b ==> x <= a' + b'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "NB" THEN
      MATCH_MP_TAC P2C_RMD_SUM THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "ftop" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  (* the curvature part *)
  USE_THEN "qb" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; DISCH_TAC] THEN
  (* the quadratic part *)
  SUBGOAL_THEN `p2c_dn 2 0 (p2c_phi (G:real^N->real^N^N)) z <=
                &4 * C2 * (C0 * norm z pow 2) pow 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `C0:real`]
                  P2C_BASE_PHI) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "hess" (fun th -> REWRITE_TAC[th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (C0 * norm(z:real^N) pow 2) pow 2 /\ (C0 * norm z pow 2) pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE];
    ALL_TAC] THEN
  USE_THEN "pb" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `b:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "low" (MP_TAC o SPEC `b:num`) THEN ASM_SIMP_TAC[];
        USE_THEN "ilow" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * C2 * (C0 * norm(z:real^N) pow 2) pow 2` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  (* splitting S = Q + Phi Ginv Phi *)
  MP_TAC(ISPECL [`2`; `j:num`; `U:real^N->bool`; `p2c_qt (G:real^N->real^N^N)`;
                 `p2c_pgp (G:real^N->real^N^N)`; `&1`; `&1`; `z:real^N`] P2C_DN_LINCOMB) THEN
  ASM_REWRITE_TAC[GSYM p2c_ss; REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_TAC THEN
  (* positivity of the quantities *)
  SUBGOAL_THEN
   `&0 <= p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) z /\
    &0 <= p2c_dn 2 j (p2c_phi G) z /\ &0 <= p2c_dn 2 j (p2c_ginv G) z /\
    &0 <= p2c_dn 4 j (lrm4 G) z /\ &0 <= p2c_dn 2 0 (p2c_phi G) z`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Hj = p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `Pj = p2c_dn 2 j (p2c_phi (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `Ij = p2c_dn 2 j (p2c_ginv (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `Rj = p2c_dn 4 j (lrm4 (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `P0 = p2c_dn 2 0 (p2c_phi (G:real^N->real^N^N)) z` THEN
  ABBREV_TAC `sm = (C0 * norm(z:real^N) pow 2) pow 2` THEN
  ABBREV_TAC `z4 = norm(z:real^N) pow 4` THEN
  SUBGOAL_THEN `&0 <= z4 /\ z4 <= rho pow 4 /\ z4 * C0 pow 2 = sm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z4"; "sm"] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* product inequalities *)
  SUBGOAL_THEN
   `z4 * Rj <= z4 * (cT * NB) + cT * &16 * sm * (cF * Hj + KF)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `z4 * (cT * NB + cT * (&16 * C0 pow 2) * (cF * Hj + KF))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `sm:real`)) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cQ * (z4 * Rj) <= cQ * (rho pow 4 * (cT * NB) + cT * &16 * sm * cF * Hj + cT * &16 * KF)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `z4 * (cT * NB) <= rho pow 4 * (cT * NB) /\
                  cT * &16 * sm * KF <= cT * &16 * KF` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `P0 <= &4 * C2 * sm` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P0"; "sm"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cP * P0 * (Pj + Ij) <= cP * &4 * C2 * (&1 + cI) * sm * (Hj + Pj) + cP * &4 * C2 * KI`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cP * (&4 * C2 * sm) * (Pj + cI * Hj + KI)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        USE_THEN "itop" MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= cP * &4 * C2 * sm * Hj /\ &0 <= cP * &4 * C2 * cI * sm * Pj /\
                  cP * &4 * C2 * sm * KI <= cP * &4 * C2 * KI` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cQ * cT * cF * sm * Pj` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bootstrap.  Under the gauge hypotheses p2c_ghyp on                    *)
(* ball(0,rho) (Gauss lemma, 1/2 <= G <= 2, |D_X G| <= 4 C0 |z|^2, |Rm|^2 <= *)
(* C0^2, C0 rho^2 <= 1) and |nabla^i Rm|^2 <= Cc for i <= k, the radial     *)
(* estimates for d^j h and d^j Phi, the structure estimate and the shell    *)
(* bootstrap bound |d^j h|^2 + |d^j Phi|^2 on cball(0,r), r < rho, order by  *)
(* order (P2C_ORDER_STEP, P2C_ALL_ORDERS).                                   *)
(* ------------------------------------------------------------------------- *)

let p2c_ghyp = new_definition
 `p2c_ghyp rho C0 (G:real^N->real^N^N) <=>
    metric_field (ball(vec 0,rho)) G /\
    (!z. z IN ball(vec 0,rho) ==> G z ** z = z) /\
    (!z a. z IN ball(vec 0,rho)
           ==> inv(&2) * (a dot a) <= a dot (G z ** a) /\ a dot (G z ** a) <= &2 * (a dot a)) /\
    (!z a. z IN ball(vec 0,rho)
           ==> abs(a dot (mderiv G z z ** a)) <= &4 * C0 * norm z pow 2 * (a dot a)) /\
    (!z. z IN ball(vec 0,rho) ==> lrm_deriv_norm2 0 G z <= C0 pow 2) /\
    &0 <= C0 /\ C0 * rho pow 2 <= &1`;;

let P2C_DN_CONT = prove
 (`!k i U (tf:real^N->(num->real^N)->real) S.
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\
     S SUBSET U
     ==> (lift o (\w. p2c_dn k i tf w)) continuous_on S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[o_DEF; p2c_dn] THEN
  MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[]);;

let P2C_SEG_CBALL = prove
 (`!(u:real^N) r t. u IN cball(vec 0,r) /\ &0 <= t /\ t <= &1
                    ==> t % u IN cball(vec 0,r) /\ norm(t % u) <= norm u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL_0; NORM_MUL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs t * norm(u:real^N) <= norm u` (fun th -> MP_TAC th THEN ASM_REAL_ARITH_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let P2C_CBALL_BALL = prove
 (`!(z:real^N) r rho. z IN cball(vec 0,r) /\ r < rho ==> z IN ball(vec 0,rho)`,
  REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC);;

let P2C_ORDER_STEP = prove
 (`!j L Cc rho r. 1 <= j /\ &0 <= L /\ &0 <= Cc /\ &0 < r /\ r < rho
     ==> ?M. !(G:real^N->real^N^N) C0.
               p2c_ghyp rho C0 G /\
               (!z i. z IN ball(vec 0,rho) /\ i <= j ==> lrm_deriv_norm2 i G z <= Cc) /\
               (!z i. z IN cball(vec 0,r) /\ i < j
                      ==> p2c_dn 2 i (lmetric2 G) z <= L /\ p2c_dn 2 i (p2c_phi G) z <= L)
               ==> !z. z IN cball(vec 0,r)
                       ==> p2c_dn 2 j (lmetric2 G) z + p2c_dn 2 j (p2c_phi G) z <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`j:num`; `L:real`; `Cc:real`; `rho:real`] P2C_SS_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `K:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ss"))))) THEN
  ABBREV_TAC `NT = &(CARD(index_tuples (2 + j) (:N)))` THEN
  SUBGOAL_THEN `&0 <= NT` ASSUME_TAC THENL [EXPAND_TAC "NT" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`&8 * NT`; `&2 * NT * (c + &1)`; `K:real`] P2C_SHELL_BOOT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (LABEL_TAC "boot")) THEN
  EXISTS_TAC `M:real` THEN MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `C0:real`] THEN
  REWRITE_TAC[p2c_ghyp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cc") (LABEL_TAC "low"))) THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
      [a1;a2;a3;a4;a5;a6;a7] ->
        ASSUME_TAC a1 THEN LABEL_TAC "gauss" a2 THEN LABEL_TAC "gb" a3 THEN
        LABEL_TAC "hess" a4 THEN LABEL_TAC "r0" a5 THEN ASSUME_TAC a6 THEN ASSUME_TAC a7
    | _ -> failwith "P2C_ORDER_STEP: hypotheses") THEN
  ABBREV_TAC `B = ball(vec 0:real^N,rho)` THEN
  SUBGOAL_THEN `open(B:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z IN cball(vec 0,r) ==> z IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_CBALL_BALL THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C0 * r pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * rho pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* fields on the ball *)
  MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] P2C_PHI_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] P2C_SS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `B:real^N->bool`; `lmetric2 (G:real^N->real^N^N)`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `B:real^N->bool`; `p2c_phi (G:real^N->real^N^N)`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `B:real^N->bool`; `p2c_ss (G:real^N->real^N^N)`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^N. w IN B ==> &0 <= p2c_dn 2 j (lmetric2 G) w /\
                                       &0 <= p2c_dn 2 j (p2c_phi G) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN
    EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "boot" (MP_TAC o SPECL
    [`\w. p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) w`;
     `\w. p2c_dn 2 j (p2c_phi (G:real^N->real^N^N)) w`; `r:real`; `C0:real`]) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[p2c_shell] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,r) SUBSET B` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2C_DN_CONT THEN EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2C_DN_CONT THEN EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    (* the radial estimate for d^j h *)
    MAP_EVERY X_GEN_TAC [`u:real^N`; `t0:real`; `Bs:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= Bs` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2c_dn 2 j (p2c_phi (G:real^N->real^N^N)) (&1 % u)` THEN CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2 + j`; `j:num`; `rho:real`;
                   `lnabla_iter 2 j p2c_flat (lmetric2 (G:real^N->real^N^N))`;
                   `\z u. &2 * lnabla_iter 2 j p2c_flat (p2c_phi (G:real^N->real^N^N)) z u`;
                   `u:real^N`; `t0:real`; `&4 * Bs`] P2C_RADIAL_TENSOR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LRG_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
        REPEAT STRIP_TAC THEN BETA_TAC THEN
        MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] P2C_RAD_H) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        REWRITE_TAC[RFA_LTNORM2_CMUL; ETA_AX] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= b ==> &2 pow 2 * x <= &4 * b`) THEN
        REWRITE_TAC[GSYM p2c_dn] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM p2c_dn] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= w + y ==> x <= w + z`) THEN
    SUBGOAL_THEN `(&1 - t0) pow 2 <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t0) pow 2 * (NT * &4 * Bs) <= &1 * (NT * &4 * Bs)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; REAL_ARITH_TAC];
    (* the radial estimate for d^j Phi *)
    MAP_EVERY X_GEN_TAC [`u:real^N`; `t0:real`; `Hs:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= Hs` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) (&1 % u) +
                  p2c_dn 2 j (p2c_phi G) (&1 % u)` THEN CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_LID] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2 + j`; `1 + j`; `rho:real`;
                   `lnabla_iter 2 j p2c_flat (p2c_phi (G:real^N->real^N^N))`;
                   `lnabla_iter 2 j p2c_flat (p2c_ss (G:real^N->real^N^N))`;
                   `u:real^N`; `t0:real`;
                   `c * (C0 * norm(u:real^N) pow 2) pow 2 * Hs + K`] P2C_RADIAL_TENSOR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] P2C_RAD_PHI) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM p2c_dn] THEN
      MP_TAC(ISPECL [`u:real^N`; `r:real`; `t:real`] P2C_SEG_CBALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c * (C0 * norm(t % u:real^N) pow 2) pow 2 *
                  (p2c_dn 2 j (lmetric2 (G:real^N->real^N^N)) (t % u) +
                   p2c_dn 2 j (p2c_phi G) (t % u)) + K` THEN
      CONJ_TAC THENL
       [USE_THEN "ss" MATCH_MP_TAC THEN EXISTS_TAC `B:real^N->bool` THEN
        ASM_SIMP_TAC[] THEN
        SUBGOAL_THEN `norm(t % u:real^N) <= r` ASSUME_TAC THENL
         [UNDISCH_TAC `t % u IN cball(vec 0:real^N,r)` THEN REWRITE_TAC[IN_CBALL_0];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * r pow 2` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + k <= y + k`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM p2c_dn] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= w + y ==> x <= w + z`) THEN
    SUBGOAL_THEN `(&1 - t0) pow 2 <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= NT * ((&1 - t0) * C0 * norm(u:real^N) pow 2) pow 2 * Hs /\
                  &0 <= NT * c * K /\ &0 <= NT * K * (&1 - (&1 - t0) pow 2)` MP_TAC THENL
     [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let P2C_ALL_ORDERS = prove
 (`!Cc rho r. &0 <= Cc /\ &0 < r /\ r < rho
     ==> !k. ?L. &0 <= L /\
           !(G:real^N->real^N^N) C0.
             p2c_ghyp rho C0 G /\
             (!z i. z IN ball(vec 0,rho) /\ i <= k ==> lrm_deriv_norm2 i G z <= Cc)
             ==> !z i. z IN cball(vec 0,r) /\ i <= k
                       ==> p2c_dn 2 i (lmetric2 G) z <= L /\ p2c_dn 2 i (p2c_phi G) z <= L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `&(CARD(index_tuples 2 (:N))) * &4` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `C0:real`] THEN
    REWRITE_TAC[p2c_ghyp; LE] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2C_CBALL_BALL THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_BASE_H THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(index_tuples 2 (:N))) * (&2 * C0 * norm(z:real^N) pow 2) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2C_BASE_PHI THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        SUBGOAL_THEN `C0 * norm(z:real^N) pow 2 <= &1 /\ &0 <= C0 * norm z pow 2`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * rho pow 2` THEN
            ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
            UNDISCH_TAC `(z:real^N) IN ball(vec 0,rho)` THEN REWRITE_TAC[IN_BALL_0] THEN
            REAL_ARITH_TAC;
            ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE]];
          ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_MUL] THEN
        SUBGOAL_THEN `(C0 * norm(z:real^N) pow 2) pow 2 <= &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  MP_TAC(SPECL [`SUC k`; `L:real`; `Cc:real`; `rho:real`; `r:real`] P2C_ORDER_STEP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC k`] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (LABEL_TAC "st")) THEN
  EXISTS_TAC `L + abs M` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `C0:real`] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL [`G:real^N->real^N^N`; `C0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "low")] THEN
  USE_THEN "st" (MP_TAC o SPECL [`G:real^N->real^N^N`; `C0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "low" (MP_TAC o SPECL [`z:real^N`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "top")] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_CBALL_BALL THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i <= k:num` THENL
   [USE_THEN "low" (MP_TAC o SPECL [`z:real^N`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = SUC k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "top" (MP_TAC o SPEC `z:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2c_dn 2 (SUC k) (lmetric2 (G:real^N->real^N^N)) z /\
                &0 <= p2c_dn 2 (SUC k) (p2c_phi G) z` MP_TAC THENL
   [UNDISCH_TAC `p2c_ghyp rho C0 (G:real^N->real^N^N)` THEN REWRITE_TAC[p2c_ghyp] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC P2C_DN_POS THEN
    EXISTS_TAC `ball(vec 0:real^N,rho)` THEN ASM_REWRITE_TAC[OPEN_BALL] THENL
     [MATCH_MP_TAC LRG_LMETRIC2_FIELD; MATCH_MP_TAC P2C_PHI_FIELD] THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The C^k bound in normal coordinates for a metric field obeying the gauge  *)
(* hypotheses (local form of MT Lemma 5.7).                                  *)

let P2C_LCK_TERM_BOUND = prove
 (`!(G:real^N->real^N^N) rho w l L.
     metric_field (ball(vec 0,rho)) G /\ w IN ball(vec 0,rho) /\
     p2c_dn 2 l (lmetric2 G) w <= L
     ==> ltnorm2 (2 + l) p2c_flat
           (lnabla_iter 2 l p2c_flat (\z u. lmetric2 G z u - lmetric2 p2c_flat z u)) w <=
         &2 * L + &2 * &(CARD(index_tuples 2 (:N)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = ball(vec 0:real^N,rho)` THEN
  SUBGOAL_THEN `open(B:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `B:real^N->bool` P2C_FLAT_METRIC_FIELD) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `p2c_flat:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p2c_dn 2 l (lmetric2 (G:real^N->real^N^N)) w` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_DN_POS THEN EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `l = 0` THENL
   [ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * ltnorm2 2 p2c_flat (lmetric2 (G:real^N->real^N^N)) w +
                &2 * ltnorm2 2 p2c_flat (lmetric2 p2c_flat) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `B:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= l /\ b <= c ==> &2 * a + &2 * b <= &2 * l + &2 * c`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `p2c_dn 2 l (lmetric2 (G:real^N->real^N^N)) w <= L` THEN
      ASM_REWRITE_TAC[p2c_dn; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[P2C_LMETRIC2_EQ; P2C_FLAT_MUL] THEN
      MP_TAC(ISPECL [`B:real^N->bool`; `(\z. mat 1):real^N->real^N^N`; `w:real^N`; `&1`]
                    P2C_ENTRY_LTNORM2) THEN
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; MATRIX_VECTOR_MUL_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST] THEN
      SIMP_TAC[DOT_BASIS_BASIS] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?l'. l = SUC l'` (X_CHOOSE_THEN `l':num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `l - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2c_dn 2 (SUC l') (lmetric2 (G:real^N->real^N^N)) w` THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPEC `CARD(index_tuples 2 (:N))` REAL_POS) THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[p2c_dn] THEN
  MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN X_GEN_TAC `u:num->real^N` THEN
  MP_TAC(ISPECL [`2`; `B:real^N->bool`; `p2c_flat:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`; `lmetric2 (p2c_flat:real^N->real^N^N)`;
                 `&1`; `--(&1)`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`SUC l'`; `w:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`B:real^N->bool`; `p2c_flat:real^N->real^N^N`] LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l':num`; `w:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x = &1 * z + --(&1) * &0 ==> y = z`) THEN
  MP_TAC(ISPECL [`2`; `p2c_flat:real^N->real^N^N`; `p2c_flat:real^N->real^N^N`;
                 `\x u. &1 * lmetric2 (G:real^N->real^N^N) x u +
                        --(&1) * lmetric2 (p2c_flat:real^N->real^N^N) x u`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u -
                        lmetric2 (p2c_flat:real^N->real^N^N) z u`;
                 `B:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`SUC l'`; `w:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[]);;

let P2C_GAUGE_LOCAL = prove
 (`!k (C:num->real) rho rho'.
     (!l. &0 <= C l) /\ &0 < rho' /\ rho' < rho
     ==> ?B. !(G:real^N->real^N^N).
               p2c_ghyp rho (C 0) G /\
               (!z l. z IN ball(vec 0,rho) /\ l <= k ==> lrm_deriv_norm2 l G z <= C l pow 2)
               ==> !w. norm w < rho' ==> lck_dist2 k p2c_flat G w <= B`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Cc = sum(0..k) (\l. (C:num->real) l pow 2)` THEN
  SUBGOAL_THEN `&0 <= Cc /\ !l. l <= k ==> (C:num->real) l pow 2 <= Cc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Cc" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`{l:num}`; `0..k`; `\l. (C:num->real) l pow 2`] SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG; REAL_LE_POW_2; SING_SUBSET; IN_NUMSEG] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Cc:real`; `rho:real`; `rho':real`] P2C_ALL_ORDERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  EXISTS_TAC `&(k + 1) * (&2 * L + &2 * &(CARD(index_tuples 2 (:N))))` THEN
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  USE_THEN "all" (MP_TAC o SPECL [`G:real^N->real^N^N`; `(C:num->real) 0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C:num->real) i pow 2` THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN cball(vec 0,rho') /\ w IN ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..k) (\l:num. &2 * L + &2 * &(CARD(index_tuples 2 (:N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC P2C_LCK_TERM_BOUND THEN EXISTS_TAC `rho:real` THEN
    UNDISCH_TAC `p2c_ghyp rho (C 0) (G:real^N->real^N^N)` THEN
    SIMP_TAC[p2c_ghyp] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `l:num`]) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(k + 1) - 0 = k + 1`; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The manifold side.  For G = cmp_expmetric (the pullback of                *)
(* g by w |-> exp_x(E w)) the hypotheses p2c_ghyp hold on ball(0,rho) by    *)
(* CMP_EXP_PULLBACK (with K = C 0) and the curvature bounds transfer to G:  *)
(* near w0, G is the pullback of the chart metric by the local             *)
(* diffeomorphism w |-> chart(exp_x(E w)) (smooth inverse function theorem),*)
(* so |nabla^l Rm|^2 is the same (LRM_DERIV_NORM2_PULLBACK).                *)
(* ------------------------------------------------------------------------- *)

let P2C_EXP_CHART_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) (c:(A->bool)#(A->real^N)).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ c IN atlas
     ==> open {w | E ** w IN mfd_exp_dom (top,atlas) g x /\
                   mfd_exp (top,atlas) g x (E ** w) IN FST c} /\
         smooth_map_on {w | E ** w IN mfd_exp_dom (top,atlas) g x /\
                            mfd_exp (top,atlas) g x (E ** w) IN FST c}
           (\w. SND c (mfd_exp (top,atlas) g x (E ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = {v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                       mfd_exp (top,atlas) g x v IN FST (c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CMPP_EXP_CHART_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
         mfd_exp (top,atlas) g x (E ** w) IN FST (c:(A->bool)#(A->real^N))} =
    {w | E ** w IN V}`
  SUBST1_TAC THENL [EXPAND_TAC "V" THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x
                                             ((E:real^N^N) ** w))) =
    (\v. SND c (mfd_exp (top,atlas) g x v)) o (\w. E ** w)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
    MP_TAC(ISPECL [`{w | (E:real^N^N) ** w IN V}`; `\x:real^N. x`;
                   `\w. (E:real^N^N) ** w`] SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_exp (top,atlas) (g:A->real^N^N) x`;
                   `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                   `c:(A->bool)#(A->real^N)`] GEOP_CHART_REP) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN SIMP_TAC[]]);;

let P2C_EXP_RMD = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) U w0 l.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     open U /\ w0 IN U /\ (!w. w IN U ==> E ** w IN mfd_exp_dom (top,atlas) g x) /\
     metric_field U (cmp_expmetric (top,atlas) g x E)
     ==> lrm_deriv_norm2 l (cmp_expmetric (top,atlas) g x E) w0 =
         lrm_deriv_norm2 l
           (metric_local atlas (chart_at atlas (mfd_exp (top,atlas) g x (E ** w0))) g)
           (SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** w0)))
               (mfd_exp (top,atlas) g x (E ** w0)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y0 = mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w0)` THEN
  SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y0:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (y0:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `E:real^N^N`; `c:(A->bool)#(A->real^N)`] P2C_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `W = {w | (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                       mfd_exp (top,atlas) g x (E ** w) IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `h = \w. SND (c:(A->bool)#(A->real^N))
                       (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w))` THEN
  STRIP_TAC THEN
  ABBREV_TAC `Gc = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  SUBGOAL_THEN `(w0:real^N) IN W INTER U` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open((W:real^N->bool) INTER U)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN (W:real^N->bool) INTER U
        ==> cmp_expmetric (top,atlas) (g:A->real^N^N) x E w = mpullback h Gc w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["h"; "Gc"] THEN
    MATCH_MP_TAC CMPP_EXPMETRIC_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(det(matrix(frechet_derivative (h:real^N->real^N) (at w0))) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `metric_field U (cmp_expmetric (top,atlas) (g:A->real^N^N) x E)` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `w0:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cmp_expmetric (top,atlas) (g:A->real^N^N) x E w0 = mpullback h Gc w0`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `(W:real^N->bool) INTER U`; `w0:real^N`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `hinv:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `metric_field (u:real^N->bool) Gc` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Gc" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    UNDISCH_TAC `diffeomorphism_on t u (h:real^N->real^N) hinv` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `u:real^N->bool`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN W` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "h" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lrm_deriv_norm2 l (mpullback (h:real^N->real^N) Gc) w0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `lrm_deriv_norm2 l Gc ((h:real^N->real^N) w0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `t:real^N->bool`; `hinv:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "h" THEN ASM_REWRITE_TAC[]]);;

let P2C_EXP_IN_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ mfd_orthonormal_frame g x E /\
     mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\ norm w < rho
     ==> mfd_exp (top,atlas) g x (E ** w) IN mfd_ball (top,atlas) g x rho`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN UNDISCH_TAC `norm(w:real^N) < rho` THEN
    ASM_REWRITE_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `u = inv(norm w) % (w:real^N)` THEN
  SUBGOAL_THEN `norm(u:real^N) = &1 /\ w = norm w % u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`] CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `norm(w:real^N)`) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM; REAL_MUL_RID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E:real^N^N) ** w = norm(w:real^N) % (E ** u)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ASSUME `w = norm(w:real^N) % u`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPP_RAY_IN_BALL THEN ASM_REWRITE_TAC[REAL_ABS_NORM]);;

let P2C_RM_NORM_LE = prove
 (`!top atlas (g:A->real^N^N) y K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top /\
     2 <= dimindex(:N) /\ &0 <= K /\
     lrm_deriv_norm2 0 (metric_local atlas (chart_at atlas y) g)
                       (SND(chart_at atlas y) y) <= K pow 2
     ==> mfd_rm_norm atlas g y <= K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`abs(mfd_sectional atlas (g:A->real^N^N) y (basis 1) (basis 2))`;
                          `basis 1:real^N`; `basis 2:real^N`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC APX_ORTHO_NOT_COLLINEAR THEN
    SUBGOAL_THEN `1 <= dimindex(:N) /\ 2 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_BASIS; DOT_BASIS_BASIS; ARITH_RULE `~(1 = 2)`; ARITH; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lrm_deriv_norm2 0 (metric_local atlas (chart_at atlas y) (g:A->real^N^N))
                                     (SND(chart_at atlas (y:A)) y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_sectional] THEN MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                      (FST(chart_at atlas y))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
           CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    ASM_MESON_TAC[riemannian_metric];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(K pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[lrm_deriv_norm2] THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                        (FST(chart_at atlas y))` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
             CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at atlas (y:A))) (FST(chart_at atlas y)))
                      (metric_local atlas (chart_at atlas y) (g:A->real^N^N))`
      ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                            (FST(chart_at atlas y))`;
                     `metric_local atlas (chart_at atlas (y:A)) (g:A->real^N^N)`]
                    LRM4_TENSOR_FIELD) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`4`; `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                                 (FST(chart_at atlas y))`;
                     `metric_local atlas (chart_at atlas (y:A)) (g:A->real^N^N)`;
                     `lrm4(metric_local atlas (chart_at atlas (y:A)) (g:A->real^N^N))`]
                    LRG_LNABLA_ITER_FIELD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN SIMP_TAC[];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL]]]);;

(* The bound on D_X G from the Hessian comparison of CMP_EXP_PULLBACK. *)

let P2C_HESS_TO_PHI = prove
 (`!(G:real^N->real^N^N) rho K w a.
     metric_field (ball(vec 0,rho)) G /\ (!z. z IN ball(vec 0,rho) ==> G z ** z = z) /\
     &0 <= K /\ norm w < rho /\ a dot (G w ** a) <= &2 * (a dot a) /\
     (&0 < norm w
      ==> (inv(norm w) - K * norm w) * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2) <=
          cmp_lhess G (\z. norm z) w a a /\
          cmp_lhess G (\z. norm z) w a a <=
          (inv(norm w) + K * norm w) * (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2))
     ==> abs(a dot (mderiv G w w ** a)) <= &4 * K * norm w pow 2 * (a dot a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[NORM_0] THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `vec 0:real^N`] LRG_MDERIV_LINEAR) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `vec 0:real^N`]
                    LRG_METRIC_FIELD_DIFF) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `vec 0:real^N`] o CONJUNCT2) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; MATRIX_CMUL_LZERO; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; REAL_ABS_0; REAL_POW_2; REAL_MUL_LZERO;
             REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
                CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `n = norm(w:real^N)` THEN
  ABBREV_TAC `A = (a:real^N) dot ((G:real^N->real^N^N) w ** a)` THEN
  ABBREV_TAC `D = ((w:real^N) dot a) pow 2` THEN
  ABBREV_TAC `V = (a:real^N) dot (mderiv (G:real^N->real^N^N) w w ** a)` THEN
  ABBREV_TAC `Z = A - D / n pow 2` THEN
  SUBGOAL_THEN `A / n - D / n pow 3 = inv n * Z` SUBST1_TAC THENL
   [EXPAND_TAC "Z" THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `x = V / (&2 * n)` THEN
  SUBGOAL_THEN `V = (&2 * n) * x` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs x <= K * n * Z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D / n pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `Z <= &2 * ((a:real^N) dot a)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `abs n = n` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < n` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * n) * (K * n * Z)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K * n pow 2) * Z <= (&2 * K * n pow 2) * (&2 * ((a:real^N) dot a))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem P2C_GAUGE (MT Lemma 5.7, gauge of Cheeger-Gromov         *)
(* compactness).  In normal coordinates w |-> exp_x(E w) (E an orthonormal   *)
(* frame at x), on a tangent ball of radius rho inside the domain of exp_x,  *)
(* with C 0 rho^2 <= 1 and |nabla^l Rm|^2 <= C l^2 (l <= k) on the metric    *)
(* ball B(x,rho), the pulled-back metric is a metric field on ball(0,rho)    *)
(* and its squared C^k distance from the Euclidean metric is bounded on      *)
(* ball(0,rho'), rho' < rho, by a constant depending only on k, C, rho,      *)
(* rho'.  The statement constant is in pc_p2c_iface.                         *)
(* ------------------------------------------------------------------------- *)

let P2C_GAUGE = prove
 (`!u:A->bool. P2C_GAUGE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_GAUGE_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `C:num->real`; `rho:real`; `rho':real`]
                (INST_TYPE [`:3`,`:N`] P2C_GAUGE_LOCAL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "loc")) THEN
  EXISTS_TAC `B:real` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM(LABEL_TAC "curv") THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^3^3) x E` THEN
  (* sectional curvature bound on the metric ball *)
  SUBGOAL_THEN `!y. y IN mfd_ball (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                              (g:A->real^3^3) x rho
                    ==> mfd_rm_norm atlas g y <= (C:num->real) 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2C_RM_NORM_LE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                                      (g:A->real^3^3) x rho` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    USE_THEN "curv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  (* CMP_EXP_PULLBACK with K = C 0 *)
  MP_TAC(ISPECL [`u:A->bool`; `(:3)`] CMP_EXP_PULLBACK) THEN
  REWRITE_TAC[CMP_EXP_PULLBACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`; `x:A`; `E:real^3^3`; `(C:num->real) 0`;
                             `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. w IN ball(vec 0,rho)
                           ==> (E:real^3^3) ** w IN
                               mfd_exp_dom (top:A topology,
                                            atlas:((A->bool)#(A->real^3))->bool)
                                           (g:A->real^3^3) (x:A)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `x:A`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* curvature transfer to G *)
  SUBGOAL_THEN `!z l. z IN ball(vec 0,rho) /\ l <= k
                      ==> lrm_deriv_norm2 l (G:real^3->real^3^3) z <= C l pow 2`
  (LABEL_TAC "gcurv") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `E:real^3^3`; `ball(vec 0:real^3,rho)`;
                   `z:real^3`; `l:num`] P2C_EXP_RMD) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "curv" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_EXP_IN_BALL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,rho)` THEN REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM p2c_flat] THEN
  USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p2c_ghyp] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2C_HESS_TO_PHI THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[IN_BALL_0];
    REPEAT STRIP_TAC THEN USE_THEN "gcurv" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_0]]);;

