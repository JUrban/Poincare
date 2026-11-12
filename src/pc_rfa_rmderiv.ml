(* ========================================================================= *)
(* Unit pc_rfa_rmderiv: the evolution of nabla^m Rm and of |nabla^m Rm|^2    *)
(* for every m under a local Ricci flow: the commutator of nabla and the     *)
(* rough Laplacian (RFA_LTLAP_COMMUTE), the evolution of nabla^m Rm          *)
(* (RFA_LRM_DERIV_EVOLUTION) and the evolution inequality for |nabla^m Rm|^2 *)
(* (RFA_LRM_DERIV_NORM2_EVOLUTION).                                          *)
(* ========================================================================= *)

needs "src/pc_rfa_mfd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Time derivatives along a jointly smooth family of tensor                  *)
(* fields: of a spatial derivative (time-space swap), of a slot insertion,  *)
(* and of the covariant derivative under a local Ricci flow.                *)
(* ========================================================================= *)

let RFA_TSLICE_FRECHET = prove
 (`!W (f:real^(1,N)finite_sum->real^1) t z d.
        open W /\ smooth_map_on W f /\ pastecart (lift t) z IN W /\
        ((\s. drop(f(pastecart (lift s) z))) has_real_derivative d) (atreal t)
        ==> frechet_derivative f (at (pastecart (lift t) z))
                               (pastecart (lift(&1)) (vec 0)) = lift d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^1`; `t:real`; `z:real^N`]
         LRG_TIME_CURVE_VDERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_VECTOR_DERIVATIVE_AT]) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  MESON_TAC[VECTOR_DERIVATIVE_UNIQUE_AT]);;

let RFA_DT_SPACE_DERIV = prove
 (`!U a b (Tf:real->real^N->(num->real^N)->real) Tf' t y u w.
        open U /\ a < t /\ t < b /\ y IN U /\
        smooth_map_on (interval(lift a,lift b) PCROSS U)
          (\z. lift(Tf (drop(fstcart z)) (sndcart z) u)) /\
        (!z. z IN U ==> ((\s. Tf s z u) has_real_derivative Tf' z u) (atreal t))
        ==> ((\s. drop(frechet_derivative (\z. lift(Tf s z u)) (at y) w))
             has_real_derivative
             drop(frechet_derivative (\z. lift(Tf' z u)) (at y) w)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(W:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s x. pastecart (lift s) x IN W <=> a < s /\ s < b /\ (x:real^N) IN U`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> frechet_derivative
              (\z. lift((Tf:real->real^N->(num->real^N)->real)
                          (drop(fstcart z)) (sndcart z) u))
              (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)) =
            lift(Tf' x u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TSLICE_FRECHET THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `\z. lift((Tf:real->real^N->(num->real^N)->real)
                             (drop(fstcart z)) (sndcart z) u)`;
                 `t:real`; `y:real^N`; `w:real^N`] LRG_TIME_SPACE_SWAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\x. frechet_derivative
             (\z. lift((Tf:real->real^N->(num->real^N)->real)
                         (drop(fstcart z)) (sndcart z) u))
             (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))) (at y) =
    frechet_derivative (\x. lift(Tf' x u)) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\r. frechet_derivative
           (\x. lift((Tf:real->real^N->(num->real^N)->real) r x u)) (at y) (w:real^N)`;
    `frechet_derivative (\x. lift((Tf':real^N->(num->real^N)->real) x u)) (at y)
                        (w:real^N)`;
    `t:real`; `1`] LRG_VDERIV_COMPONENT_REAL) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_DT_SLOT = prove
 (`!(Tf:real->real^N->(num->real^N)->real) Tf' (X:real->real^N) X' a b t y i u.
        a < t /\ t < b /\
        (!s. a < s /\ s < b
             ==> linear (\v. lift(Tf s y (\j. if j = i then v else u j)))) /\
        linear (\v. lift(Tf' y (\j. if j = i then v else u j))) /\
        (!v. ((\s. Tf s y (\j. if j = i then v else u j)) has_real_derivative
              Tf' y (\j. if j = i then v else u j)) (atreal t)) /\
        ((\s. X(drop s)) has_vector_derivative X') (at (lift t))
        ==> ((\s. Tf s y (\j. if j = i then X s else u j)) has_real_derivative
             Tf' y (\j. if j = i then X t else u j) +
             Tf t y (\j. if j = i then X' else u j)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. sum(1..dimindex(:N))
                    (\q. (X:real->real^N) s$q *
                         (Tf:real->real^N->(num->real^N)->real) s y
                           (\j. if j = i then basis q else u j))` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Tf':real^N->(num->real^N)->real) y (\j. if j = i then (X:real->real^N) t else u j) +
    (Tf:real->real^N->(num->real^N)->real) t y (\j. if j = i then X' else u j) =
    sum(1..dimindex(:N))
      (\q. X t$q * Tf' y (\j. if j = i then basis q else u j) +
           X'$q * Tf t y (\j. if j = i then basis q else u j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG] THEN BINOP_TAC THEN
    MATCH_MP_TAC LRG_SLOT_EXPAND THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (X:real->real^N) s$q`; `(X':real^N)$q`;
                 `\s. (Tf:real->real^N->(num->real^N)->real) s y
                        (\j. if j = i then basis q else u j)`;
                 `(Tf':real^N->(num->real^N)->real) y
                    (\j. if j = i then basis q else (u:num->real^N) j)`;
                 `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`X:real->real^N`; `X':real^N`; `t:real`; `q:num`]
           LRG_VDERIV_COMPONENT_REAL) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(MESON[]
     `(x:real) = y ==> (f has_real_derivative x) net
                     ==> (f has_real_derivative y) net`) THEN
    REAL_ARITH_TAC]);;

(* The time derivative of the covariant derivative of a smooth family Tf   *)
(* with time derivative Tf' at t: lnabla Tf' minus the insertion of the     *)
(* time derivative ldgamma of the Christoffel symbols.                      *)

let RFA_LNABLA_DT = prove
 (`!k U a b (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real)
    Tf' t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
        (!s. a < s /\ s < b ==> ltensor_field k U (Tf s)) /\
        ltensor_field k U Tf' /\
        (!u. smooth_map_on (interval(lift a,lift b) PCROSS U)
               (\z. lift(Tf (drop(fstcart z)) (sndcart z) u))) /\
        (!z u. z IN U ==> ((\s. Tf s z u) has_real_derivative Tf' z u) (atreal t))
        ==> ((\s. lnabla k (G s) (Tf s) y u) has_real_derivative
             lnabla k (G t) Tf' y u -
             sum(1..k) (\i. Tf t y (\j. if j = i then ldgamma G t y (u(k + 1)) (u i)
                                     else u j))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  REWRITE_TAC[lnabla] THEN
  REWRITE_TAC[REAL_ARITH `(d - x) - y = d - (x + y:real)`; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_DT_SPACE_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Tf:real->real^N->(num->real^N)->real`;
                 `Tf':real^N->(num->real^N)->real`;
                 `\s. christoffel ((G:real->real^N->real^N^N) s) y
                                  ((u:num->real^N)(k + 1)) (u i)`;
                 `ldgamma (G:real->real^N->real^N^N) t y ((u:num->real^N)(k + 1)) (u i)`;
                 `a:real`; `b:real`; `t:real`; `y:real^N`; `i:num`; `u:num->real^N`]
         RFA_DT_SLOT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ltensor_field k U ((Tf:real->real^N->(num->real^N)->real) s)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `ltensor_field k U (Tf':real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[ldgamma] THEN MATCH_MP_TAC LRG_FLOW_GAMMA_VDERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Joint smoothness in (t,y) of covariant derivatives of a                   *)
(* jointly smooth family of tensor fields, and of nabla^m Rm, for a smooth *)
(* family of local metrics.                                                  *)
(* ========================================================================= *)

let RFA_LSMOOTH_LNABLA = prove
 (`!k U ta tb (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real).
     lrg_lsmooth U ta tb G /\
     (!s. ta < s /\ s < tb ==> ltensor_field k U (Tf s)) /\
     (!u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift(Tf (drop(fstcart z)) (sndcart z) u)))
     ==> !u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
               (\z. lift(lnabla k (G (drop(fstcart z))) (Tf (drop(fstcart z)))
                                (sndcart z) u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lnabla; LIFT_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                   `\z. lift((Tf:real->real^N->(num->real^N)->real)
                               (drop(fstcart z)) (sndcart z) u)`;
                   `(u:num->real^N)(k + 1)`] LRG_JOINT_PARTIAL) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
    `\z v. lift((Tf:real->real^N->(num->real^N)->real) (drop(fstcart z)) (sndcart z)
                  (\j. if j = i then v else (u:num->real^N) j))`;
    `\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z)
                     ((u:num->real^N)(k + 1)) (u i)`] LRG_SMOOTH_LINEAR_ARG) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltensor_field k U ((Tf:real->real^N->(num->real^N)->real) (drop(fstcart z))) /\
    sndcart z IN U`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ltensor_field] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `sndcart(z:real^(1,N)finite_sum)`)
                             ASSUME_TAC) THEN
  ASM_SIMP_TAC[]);;

let RFA_LSMOOTH_LNABLA_ITER = prove
 (`!k U ta tb (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real).
     lrg_lsmooth U ta tb G /\
     (!s. ta < s /\ s < tb
          ==> ltensor_field k U (Tf s) /\ (!u. smooth_map_on U (\y. lift(Tf s y u)))) /\
     (!u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift(Tf (drop(fstcart z)) (sndcart z) u)))
     ==> !l u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                 (\z. lift(lnabla_iter k l (G (drop(fstcart z))) (Tf (drop(fstcart z)))
                                       (sndcart z) u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  INDUCT_TAC THENL [ASM_REWRITE_TAC[lnabla_iter]; ALL_TAC] THEN
  REWRITE_TAC[lnabla_iter] THEN
  MP_TAC(ISPECL [`k + l:num`; `U:real^N->bool`; `ta:real`; `tb:real`;
                 `G:real->real^N->real^N^N`;
                 `\s. lnabla_iter k l ((G:real->real^N->real^N^N) s)
                        ((Tf:real->real^N->(num->real^N)->real) s)`]
         RFA_LSMOOTH_LNABLA) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) s`;
                 `(Tf:real->real^N->(num->real^N)->real) s`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[]);;

let RFA_LSMOOTH_LRM_DERIV = prove
 (`!U ta tb (G:real->real^N->real^N^N) m u.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lnabla_iter 4 m (G (drop(fstcart z))) (lrm4 (G (drop(fstcart z))))
                                 (sndcart z) u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `ta:real`; `tb:real`;
                 `G:real->real^N->real^N^N`;
                 `\s. lrm4 ((G:real->real^N->real^N^N) s)`] RFA_LSMOOTH_LNABLA_ITER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_LSMOOTH_LRM4; LRM4_TENSOR_FIELD]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* The action of a (0,3)-tensor on a (0,k)-tensor through one                *)
(* slot (the shape of the time derivative of the Christoffel symbols        *)
(* inserted into a tensor), and its membership in the bilinear class.       *)
(* ========================================================================= *)

let rfa_gact = new_definition
 `rfa_gact k (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
           (tf:real^N->(num->real^N)->real) y u =
    sum(1..k) (\i. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b *
       sf y (\m. if m = 1 then u i else if m = 2 then basis a else u(k + 1)) *
       tf y (\m. if m = i then basis b else u m))))`;;

let RFA_GACT_PERM = prove
 (`!k i. 1 <= i /\ i <= k
         ==> (\n. if n = 1 then i else if n = 2 then k + 1
                  else if 3 <= n /\ n <= i + 1 then n - 2
                  else if i + 2 <= n /\ n <= k + 1 then n - 1 else n)
             permutes 1..k + 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = i then 1 else if m = k + 1 then 2
                  else if 1 <= m /\ m < i then m + 2
                  else if i < m /\ m <= k then m + 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_GACT_TERM = prove
 (`!k i. 1 <= i /\ i <= k
         ==> lbilin_on (k + 1) 3 k
               (\(G:real^N->real^N^N) sf tf y u.
                  sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                    matrix_inv(G y)$a$b *
                    sf y (\m. if m = 1 then u i else if m = 2 then basis a
                              else u(k + 1)) *
                    tf y (\m. if m = i then basis b else u m))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tau = \n. if n = 1 then i else if n = 2 then k + 1
                        else if 3 <= n /\ n <= i + 1 then n - 2
                        else if i + 2 <= n /\ n <= k + 1 then n - 1 else n` THEN
  SUBGOAL_THEN `tau permutes 1..k + 1` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC RFA_GACT_PERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `3`; `k:num`; `2`; `3 + i`;
    `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
      (tf:real^N->(num->real^N)->real). ltprod 3 sf tf`] RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(k + 1) + 2 = 3 + k`] THEN
    REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau:num->num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ISPECL [`k + 1`; `3`; `k:num`] RFA_LBILIN_ON_PERM))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "tau" THEN
  UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `(i:num) <= k` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `sf:real^N->(num->real^N)->real`;
                       `tf:real^N->(num->real^N)->real`; `y:real^N`;
                       `u:num->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field 3 U (sf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THENL
     [SUBGOAL_THEN `~(1 = 3 + i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN `m = 3` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(3 = 3 + i) /\ 3 < 3 + i` (fun th -> REWRITE_TAC[th; ARITH]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
    check (fun th -> concl th = `ltensor_field k U (tf:real^N->(num->real^N)->real)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
  SUBGOAL_THEN `~(m + 3 = 2) /\ ~(m + 3 < 2) /\ (m + 3 = 3 + i <=> m = i) /\
                (m + 3 < 3 + i <=> m < i)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m < (i:num)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~((m + 3) - 1 = 1) /\ ~((m + 3) - 1 = 2) /\
                  3 <= (m + 3) - 1 /\ (m + 3) - 1 <= i + 1 /\ ((m + 3) - 1) - 2 = m`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~((m + 3) - 2 = 1) /\ ~((m + 3) - 2 = 2) /\
                  ~(3 <= (m + 3) - 2 /\ (m + 3) - 2 <= i + 1) /\
                  i + 2 <= (m + 3) - 2 /\ (m + 3) - 2 <= k + 1 /\
                  ((m + 3) - 2) - 1 = m`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let RFA_GACT_LBILIN = prove
 (`!k. lbilin_on (k + 1) 3 k (rfa_gact k:(real^N->real^N^N)->
         (real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->
         real^N->(num->real^N)->real)`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    EXISTS_TAC `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
                 (tf:real^N->(num->real^N)->real) y u.
                 &0 * ltcontr G (ltprod 3 sf tf) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN
      MP_TAC(ISPECL [`1`; `3`; `0`;
        `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
          (tf:real^N->(num->real^N)->real). ltprod 3 sf tf`] RFA_LBILIN_ON_CONTR) THEN
      REWRITE_TAC[ARITH_RULE `1 + 2 = 3 + 0`; ARITH_RULE `0 + 1 = 1`] THEN
      REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN REWRITE_TAC[ETA_AX];
      REWRITE_TAC[rfa_gact; SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `3`; `k:num`; `k:num`;
    `\i (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
       sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
         matrix_inv(G y)$a$b *
         sf y (\m. if m = 1 then u i else if m = 2 then basis a else u(k + 1)) *
         tf y (\m. if m = i then basis b else u m)))`] RFA_LBILIN_ON_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GACT_TERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; rfa_gact]);;

(* ========================================================================= *)
(* The time derivative of the Christoffel symbols inserted                   *)
(* into a tensor is a bilinear-class action of nabla Rm on the tensor.      *)
(* ========================================================================= *)

let RFA_PERM312_PERMUTES = prove
 (`(\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m)
   permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_N2_PERM13 = prove
 (`!U (G:real^N->real^N^N) z p q r.
        metric_field U G /\ z IN U
        ==> ltperm (swap(1,3)) (lnabla 2 G (lric2 G)) z
              (\m. if m = 1 then p else if m = 2 then q else r) =
            lnabla 2 G (lric2 G) z (\m. if m = 1 then r else if m = 2 then q else p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltperm] THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[swap; ARITH]);;

let RFA_N2_PERM312 = prove
 (`!U (G:real^N->real^N^N) z p q r.
        metric_field U G /\ z IN U
        ==> ltperm (\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m)
              (lnabla 2 G (lric2 G)) z
              (\m. if m = 1 then p else if m = 2 then q else r) =
            lnabla 2 G (lric2 G) z (\m. if m = 1 then r else if m = 2 then p else q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltperm] THEN
  MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH]);;

let RFA_LDGAMMA_INSERT = prove
 (`!k U a b (G:real->real^N->real^N^N) (tf:real^N->(num->real^N)->real) t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ ltensor_field k U tf
        ==> sum(1..k) (\i. tf y (\j. if j = i then ldgamma G t y (u(k + 1)) (u i)
                                   else u j)) =
            --(rfa_gact k (G t) (lnabla 2 (G t) (lric2 (G t))) tf y u +
               (rfa_gact k (G t) (ltperm (swap(1,3)) (lnabla 2 (G t) (lric2 (G t))))
                  tf y u -
                rfa_gact k (G t)
                  (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                               else if m = 3 then 2 else m)
                          (lnabla 2 (G t) (lric2 (G t)))) tf y u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `gi = matrix_inv((G:real->real^N->real^N^N) t y)` THEN
  REWRITE_TAC[rfa_gact] THEN
  REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `i:num`;
                 `u:num->real^N`;
                 `ldgamma (G:real->real^N->real^N^N) t y ((u:num->real^N)(k + 1)) (u i)`]
         RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(u:num->real^N)(k + 1)`; `(u:num->real^N) i`;
                 `p:num`] LRG_FLOW_DGAMMA) THEN
  ASM_REWRITE_TAC[GSYM ldgamma] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) i`; `basis p:real^N`; `(u:num->real^N)(k + 1)`]
         RFA_N2_PERM13) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) i`; `basis p:real^N`; `(u:num->real^N)(k + 1)`]
         RFA_N2_PERM312) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_ACCEPT_TAC(REAL_RING
   `!g A B C X:real. g * --(A + B - C) * X = --(g * A * X + g * B * X - g * C * X)`));;

let RFA_NABLA_RIC_CONTR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> !u. lnabla 2 G (lric2 G) y u =
                ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G))) y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..4` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 2 (G:real^N->real^N^N)
                (ltcontr G (ltperm (swap(2,3)) (lrm4 G))) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RFA_LRIC2_CONTR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[ARITH]
   (ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))`; `y:real^N`;
            `u:num->real^N`] RFA_LNABLA_LTCONTR)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_FIELD; RFA_LTPERM_SMOOTH]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ltcontr] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[RFA_LNABLA_LTPERM]);;

let RFA_GACT_CONG = prove
 (`!k (G:real^N->real^N^N) sf sf' tf y u.
        (!v. sf y v = sf' y v)
        ==> rfa_gact k G sf tf y u = rfa_gact k G sf' tf y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_gact] THEN ASM_REWRITE_TAC[]);;

let RFA_LTPERM_CONG = prove
 (`!s (sf:real^N->(num->real^N)->real) sf' y.
        (!v. sf y v = sf' y v) ==> !v. ltperm s sf y v = ltperm s sf' y v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltperm] THEN ASM_REWRITE_TAC[]);;

let RFA_GACT_RM_LBILIN = prove
 (`!k s. s permutes 1..3
         ==> lbilin_on (k + 1) 5 k
               (\(G:real^N->real^N^N) sf tf y u.
                  rfa_gact k G (ltperm s (ltcontr G (ltperm (swap(2,3)) sf))) tf y u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` RFA_GACT_LBILIN) THEN
  DISCH_THEN(MP_TAC o SPEC `s:num->num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ISPECL [`k + 1`; `3`; `k:num`] RFA_LBILIN_ON_SUBST1_PERM))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SUBST1_CONTR) THEN
  REWRITE_TAC[ARITH] THEN
  DISCH_THEN(MP_TAC o SPEC `swap(2,3)` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ISPECL [`k + 1`; `5`; `k:num`] RFA_LBILIN_ON_SUBST1_PERM))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[ETA_AX]]);;

let RFA_DGAMMA_TERM = prove
 (`!k. ?E. lbilin_on (k + 1) 5 k E /\
           !U a b (G:real->real^N->real^N^N) (tf:real^N->(num->real^N)->real) t y u.
              lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ ltensor_field k U tf
              ==> sum(1..k) (\i. tf y (\j. if j = i
                                         then ldgamma G t y (u(k + 1)) (u i)
                                         else u j)) =
                  E (G t) (lnabla 4 (G t) (lrm4 (G t))) tf y u`,
  GEN_TAC THEN
  EXISTS_TAC
   `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
     (tf:real^N->(num->real^N)->real) y u.
      --(rfa_gact k G (ltperm (\m. m) (ltcontr G (ltperm (swap(2,3)) sf))) tf y u +
         (rfa_gact k G (ltperm (swap(1,3)) (ltcontr G (ltperm (swap(2,3)) sf)))
            tf y u -
          rfa_gact k G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                                    else if m = 3 then 2 else m)
                          (ltcontr G (ltperm (swap(2,3)) sf))) tf y u))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    EXISTS_TAC
     `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
        --(&1) *
        (\G sf tf y u.
          rfa_gact k G (ltperm (\m. m) (ltcontr G (ltperm (swap(2,3)) sf))) tf y u +
          (\G sf tf y u.
             rfa_gact k G (ltperm (swap(1,3)) (ltcontr G (ltperm (swap(2,3)) sf)))
               tf y u -
             rfa_gact k G (ltperm (\m. if m = 1 then 3 else if m = 2 then 1
                                       else if m = 3 then 2 else m)
                             (ltcontr G (ltperm (swap(2,3)) sf))) tf y u)
          G sf tf y u) G sf tf y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_GACT_RM_LBILIN THEN
        REWRITE_TAC[GSYM I_DEF; PERMUTES_I];
        ALL_TAC] THEN
      MATCH_MP_TAC RFA_LBILIN_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC RFA_GACT_RM_LBILIN THEN
      REWRITE_TAC[RFA_PERM312_PERMUTES] THEN
      MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `tf:real^N->(num->real^N)->real`;
                 `t:real`; `y:real^N`; `u:num->real^N`] RFA_LDGAMMA_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
         RFA_NABLA_RIC_CONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC RFA_GACT_CONG THEN ASM_REWRITE_TAC[ltperm; ETA_AX];
    BINOP_TAC THEN MATCH_MP_TAC RFA_GACT_CONG THEN
    MATCH_MP_TAC RFA_LTPERM_CONG THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The commutator of the covariant derivative and the rough Laplacian        *)
(* (RFA_LTLAP_COMMUTE):                                                      *)
(* nabla Lap T = Lap nabla T + Rm x nabla T + nabla Rm x T.                  *)
(* ========================================================================= *)

let RFA_LNABLA_ITER_SHIFT = prove
 (`!k l (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
        lnabla_iter (k + 1) l G (lnabla k G tf) = lnabla_iter k (l + 1) G tf`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; RFA_LNABLA_ITER_1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lnabla_iter; ARITH_RULE `SUC l + 1 = SUC(l + 1)`] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + l = k + l + 1`]);;

let RFA_LNABLA_LTLAP = prove
 (`!k U (G:real^N->real^N^N) tf y u.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla k G (ltlap k G tf) y u =
            sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
              matrix_inv(G y)$a$b *
              lnabla_iter k 3 G tf y (rfa_ins (k + 1) (k + 2) (basis a) (basis b) u)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla k (G:real^N->real^N^N)
      (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
               matrix_inv(G z)$a$b *
               lnabla_iter k 2 G tf z (rfa_ins (k + 1) (k + 2) (basis a) (basis b) w))))
      y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN REWRITE_TAC[ltlap] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th =
        `ltensor_field (k + 2) U (lnabla_iter k 2 (G:real^N->real^N^N) tf)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins] THEN
    ASM_CASES_TAC `m = k + 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m = k + 2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m < k + 1` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla_iter k 2 (G:real^N->real^N^N) tf`; `k + 1`; `k + 2`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA_CTR_AT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[num_CONV `3`; lnabla_iter]);;

let RFA_LTLAP_LNABLA = prove
 (`!k (G:real^N->real^N^N) tf y u.
        ltlap (k + 1) G (lnabla k G tf) y u =
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          lnabla_iter k 3 G tf y
            (\m. if m = k + 2 then basis a else if m = k + 3 then basis b else u m)))`,
  REWRITE_TAC[ltlap; RFA_LNABLA_ITER_SHIFT; ARITH_RULE `2 + 1 = 3`;
              ARITH_RULE `(k + 1) + 1 = k + 2`; ARITH_RULE `(k + 1) + 2 = k + 3`]);;

(* Agreement of two index tuples on the slots 1..k+n, by cases on the slot. *)

let RFA_KTUPLE_TAC =
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[rfa_ins; swap] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN TRY ASM_ARITH_TAC;;

let RFA_COMMUTE_SUMMAND = prove
 (`!k (Bp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) Bk Bk1 Bk2
    U G tf y u v w.
        (!U G tf y u.
            metric_field U G /\ ltensor_field (k + 1) U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla_iter (k + 1) 2 G tf y u -
                lnabla_iter (k + 1) 2 G tf y
                  (\m. if m = (k + 1) + 1 then u((k + 1) + 2)
                       else if m = (k + 1) + 2 then u((k + 1) + 1) else u m) =
                Bp G (lrm4 G) tf y u) /\
        (!U G tf y u.
            metric_field U G /\ ltensor_field k U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla_iter k 2 G tf y u -
                lnabla_iter k 2 G tf y
                  (\m. if m = k + 1 then u(k + 2) else if m = k + 2 then u(k + 1)
                       else u m) =
                Bk G (lrm4 G) tf y u) /\
        (!U G tf tg y u.
            metric_field U G /\ y IN U /\
            ltensor_field 4 U tf /\ ltensor_field k U tg /\
            (!u. smooth_map_on U (\y. lift(tf y u))) /\
            (!u. smooth_map_on U (\y. lift(tg y u)))
            ==> lnabla (k + 2) G (Bk G tf tg) y u =
                Bk1 G (lnabla 4 G tf) tg y u + Bk2 G tf (lnabla k G tg) y u) /\
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla_iter k 3 G tf y (rfa_ins (k + 1) (k + 2) v w u) -
            lnabla_iter k 3 G tf y
              (\m. if m = k + 2 then v else if m = k + 3 then w else u m) =
            Bp G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 2) v w u) +
            Bk1 G (lnabla 4 G (lrm4 G)) tf y (rfa_ins (k + 1) (k + 3) v w u) +
            Bk2 G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 3) v w u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hp") (CONJUNCTS_THEN2 (LABEL_TAC "hk")
    (CONJUNCTS_THEN2 (LABEL_TAC "hn") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltensor_field (k + 1) U (lnabla k (G:real^N->real^N^N) tf) /\
    (!u. smooth_map_on U (\x. lift(lnabla k G tf x u)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field (k + 2) U (lnabla_iter k 2 (G:real^N->real^N^N) tf) /\
    (!u. smooth_map_on U (\x. lift(lnabla_iter k 2 G tf x u))) /\
    ltensor_field (k + 3) U (lnabla_iter k 3 G tf)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p p'. (!m. 1 <= m /\ m <= k + 3 ==> p m = p' m)
           ==> lnabla_iter k 3 (G:real^N->real^N^N) tf y p =
               lnabla_iter k 3 G tf y p'`
  (LABEL_TAC "agree") THENL
   [UNDISCH_TAC `ltensor_field (k + 3) U (lnabla_iter k 3 (G:real^N->real^N^N) tf)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o C MP (ASSUME `(y:real^N) IN U`) o
               SPEC `y:real^N`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 2) v w u) -
    lnabla_iter k 3 G tf y (rfa_ins (k + 1) (k + 3) v w u) =
    Bp G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 2) v w u)`
  ASSUME_TAC THENL
   [USE_THEN "hp" (MP_TAC o SPECL
      [`U:real^N->bool`; `G:real^N->real^N^N`;
       `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`;
       `rfa_ins (k + 1) (k + 2) (v:real^N) w (u:num->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[RFA_LNABLA_ITER_SHIFT; ARITH_RULE `2 + 1 = 3`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    USE_THEN "agree" MATCH_MP_TAC THEN RFA_KTUPLE_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `swap(k + 1,k + 2) permutes 1..k + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y
      (\m. if m = k + 2 then v else if m = k + 3 then w else u m) =
    lnabla (k + 2) G (ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 G tf)) y
      (rfa_ins (k + 1) (k + 3) v w u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATCH_MP RFA_LNABLA_LTPERM
      (ASSUME `swap(k + 1,k + 2) permutes 1..k + 2`)] THEN
    REWRITE_TAC[ltperm; GSYM(CONJUNCT2 lnabla_iter); ARITH_RULE `SUC 2 = 3`] THEN
    USE_THEN "agree" MATCH_MP_TAC THEN RFA_KTUPLE_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (\z. lift(lnabla_iter k 2 (G:real^N->real^N^N) tf z x)) differentiable at y /\
        (\z. lift(ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 G tf) z x))
        differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[RFA_LTPERM_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 3) v w u) -
    lnabla (k + 2) G (ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 G tf)) y
      (rfa_ins (k + 1) (k + 3) v w u) =
    Bk1 G (lnabla 4 G (lrm4 G)) tf y (rfa_ins (k + 1) (k + 3) v w u) +
    Bk2 G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 3) v w u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[num_CONV `3`; lnabla_iter; ARITH_RULE `k + 2 = k + 2`] THEN
    REWRITE_TAC[GSYM(num_CONV `3`)] THEN
    MP_TAC(ISPECL [`k + 2`; `G:real^N->real^N^N`;
                   `lnabla_iter k 2 (G:real^N->real^N^N) tf`;
                   `ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 (G:real^N->real^N^N) tf)`;
                   `y:real^N`; `rfa_ins (k + 1) (k + 3) (v:real^N) w (u:num->real^N)`]
           LRG_LNABLA_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla (k + 2) (G:real^N->real^N^N)
                  (Bk G (lrm4 G) (tf:real^N->(num->real^N)->real)) y
                  (rfa_ins (k + 1) (k + 3) (v:real^N) w (u:num->real^N))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `x:num->real^N`] THEN
      DISCH_TAC THEN
      USE_THEN "hk" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
        `tf:real^N->(num->real^N)->real`; `z:real^N`; `x:num->real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[ltperm] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; swap] THEN GEN_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN TRY ASM_ARITH_TAC;
      USE_THEN "hn" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 3) v w u) =
    lnabla (k + 2) G (lnabla_iter k 2 G tf) y (rfa_ins (k + 1) (k + 3) v w u)`
  ASSUME_TAC THENL [REWRITE_TAC[num_CONV `3`; lnabla_iter]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  UNDISCH_TAC
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 3) v w u) -
    lnabla (k + 2) G (ltperm (swap(k + 1,k + 2)) (lnabla_iter k 2 G tf)) y
      (rfa_ins (k + 1) (k + 3) v w u) =
    Bk1 G (lnabla 4 G (lrm4 G)) tf y (rfa_ins (k + 1) (k + 3) v w u) +
    Bk2 G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 3) v w u)` THEN
  UNDISCH_TAC
   `lnabla_iter k 3 (G:real^N->real^N^N) tf y (rfa_ins (k + 1) (k + 2) v w u) -
    lnabla_iter k 3 G tf y (rfa_ins (k + 1) (k + 3) v w u) =
    Bp G (lrm4 G) (lnabla k G tf) y (rfa_ins (k + 1) (k + 2) v w u)` THEN
  REAL_ARITH_TAC);;

let RFA_LTLAP_COMMUTE_ON = prove
 (`!k. ?E1 E2.
         lbilin_on (k + 1) 4 (k + 1) E1 /\ lbilin_on (k + 1) 5 k E2 /\
         !U (G:real^N->real^N^N) tf y u.
            metric_field U G /\ ltensor_field k U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla k G (ltlap k G tf) y u =
                ltlap (k + 1) G (lnabla k G tf) y u +
                E1 G (lrm4 G) (lnabla k G tf) y u +
                E2 G (lnabla 4 G (lrm4 G)) tf y u`,
  GEN_TAC THEN
  MP_TAC(SPEC `k + 1` RFA_RICCI_IDENTITY_LB) THEN
  DISCH_THEN(X_CHOOSE_THEN
   `Bp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hp"))) THEN
  MP_TAC(SPEC `k:num` RFA_RICCI_IDENTITY_LB) THEN
  DISCH_THEN(X_CHOOSE_THEN
   `Bk:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hk"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LBILIN_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN
   `Bk1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (X_CHOOSE_THEN
   `Bk2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hn"))))) THEN
  EXISTS_TAC
   `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
     (tg:real^N->(num->real^N)->real) y u.
      sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
        matrix_inv(G y)$a$b *
        (Bp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
          G sf tg y (rfa_ins (k + 1) (k + 2) (basis a) (basis b) u))) +
      sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
        matrix_inv(G y)$a$b *
        (Bk2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
          G sf tg y (rfa_ins (k + 1) (k + 3) (basis a) (basis b) u)))` THEN
  EXISTS_TAC
   `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
     (tf:real^N->(num->real^N)->real) y u.
      sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
        matrix_inv(G y)$a$b *
        (Bk1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
          G sf tf y (rfa_ins (k + 1) (k + 3) (basis a) (basis b) u)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k + 1`; `4`; `k + 1`; `k + 1`; `k + 2`;
         `Bp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
         RFA_LBILIN_ON_CTR_AT) THEN
      ASM_SIMP_TAC[RFA_LBILIN_ON_LBILIN] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      MP_TAC(ISPECL [`k + 1`; `4`; `k + 1`; `k + 1`; `k + 3`;
         `Bk2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
         RFA_LBILIN_ON_CTR_AT) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(k + 2) + 1 = (k + 1) + 2`]) THEN
      ASM_SIMP_TAC[RFA_LBILIN_ON_LBILIN] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[]];
    MP_TAC(ISPECL [`k + 1`; `5`; `k:num`; `k + 1`; `k + 3`;
       `Bk1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
       RFA_LBILIN_ON_CTR_AT) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(k + 2) + 1 = (k + 1) + 2`;
                                ARITH_RULE `4 + 1 = 5`]) THEN
    ASM_SIMP_TAC[RFA_LBILIN_ON_LBILIN] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]
         RFA_LNABLA_LTLAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_LTLAP_LNABLA] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`k:num`;
    `Bp:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `Bk:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `Bk1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
         (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `Bk2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
         (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `U:real^N->bool`; `G:real^N->real^N^N`; `tf:real^N->(num->real^N)->real`;
    `y:real^N`; `u:num->real^N`; `basis a:real^N`; `basis b:real^N`]
   RFA_COMMUTE_SUMMAND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "hp" ACCEPT_TAC; USE_THEN "hk" ACCEPT_TAC; USE_THEN "hn" ACCEPT_TAC];
    ALL_TAC] THEN
  CONV_TAC REAL_RING);;

(* RFA_LTLAP_COMMUTE, with the bilinear operations in lbilin.               *)

let RFA_LTLAP_COMMUTE = prove
 (`!k. ?B1 B2.
         lbilin (k + 1) 4 (k + 1) B1 /\ lbilin (k + 1) 5 k B2 /\
         !U (G:real^N->real^N^N) tf y u.
            metric_field U G /\ ltensor_field k U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla k G (ltlap k G tf) y u =
                ltlap (k + 1) G (lnabla k G tf) y u +
                B1 G (lrm4 G) (lnabla k G tf) y u +
                B2 G (lnabla 4 G (lrm4 G)) tf y u`,
  GEN_TAC THEN
  X_CHOOSE_THEN
   `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (X_CHOOSE_THEN
   `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "id"))))
   (SPEC `k:num` RFA_LTLAP_COMMUTE_ON) THEN
  REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  MAP_EVERY EXISTS_TAC
   [`B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "id" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`; `y:real^N`; `u:num->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [USE_THEN "e1" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "e2" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Support for the induction on m (RFA_LRM_DERIV_EVOLUTION): the rough       *)
(* Laplacian of a smooth tensor field is a smooth tensor field, lnabla of a  *)
(* finite sum, smoothness and the Leibniz rule for the class lbilin_on.      *)
(* ========================================================================= *)

let RFA_LTLAP_CTR = prove
 (`!k U (G:real^N->real^N^N) tf y u.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> ltlap k G tf y u =
            ltcontr G (ltperm (rfa_sig (k + 1) (k + 2)) (lnabla_iter k 2 G tf)) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN STRIP_TAC THEN
  SIMP_TAC[RFA_LTCONTR_SIG; ARITH_RULE `1 <= k + 1 /\ k + 1 < k + 2`] THEN
  REWRITE_TAC[ltlap] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
    check (fun th -> concl th =
      `ltensor_field (k + 2) U (lnabla_iter k 2 (G:real^N->real^N^N) tf)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  RFA_KTUPLE_TAC);;

let RFA_LTLAP_FIELD = prove
 (`!k U (G:real^N->real^N^N) tf.
        metric_field U G /\ ltensor_field k U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u)))
        ==> ltensor_field k U (ltlap k G tf) /\
            (!u. smooth_map_on U (\x. lift(ltlap k G tf x u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfa_sig (k + 1) (k + 2) permutes 1..k + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_SIG_PERMUTES THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = ltperm (rfa_sig (k + 1) (k + 2))
                         (lnabla_iter k 2 (G:real^N->real^N^N) tf)` THEN
  SUBGOAL_THEN `ltensor_field (k + 2) U (X:real^N->(num->real^N)->real) /\
                (!u. smooth_map_on U (\x. lift(X x u)))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[RFA_LTPERM_FIELD; RFA_LTPERM_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u. x IN U ==> ltlap k (G:real^N->real^N^N) tf x u = ltcontr G X x u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "X" THEN MATCH_MP_TAC RFA_LTLAP_CTR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTENSOR_FIELD_EQ THEN
    EXISTS_TAC `ltcontr (G:real^N->real^N^N) X` THEN
    ASM_SIMP_TAC[RFA_LTCONTR_FIELD];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\x. lift(ltcontr (G:real^N->real^N^N) X x u)` THEN
    ASM_SIMP_TAC[RFA_LTCONTR_SMOOTH]]);;

let RFA_LNABLA_SUM = prove
 (`!k (G:real^N->real^N^N) (tf:num->real^N->(num->real^N)->real) y u n.
        (!i. i <= n ==> (\x. lift(tf i x u)) differentiable at y)
        ==> lnabla k G (\x u. sum(0..n) (\i. tf i x u)) y u =
            sum(0..n) (\i. lnabla k G (tf i) y u)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ETA_AX]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`;
                 `\x:real^N u:num->real^N. sum(0..n) (\i. (tf:num->real^N->(num->real^N)->real) i x u)`;
                 `(tf:num->real^N->(num->real^N)->real) (SUC n)`;
                 `y:real^N`; `u:num->real^N`] LRG_LNABLA_ADD) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUM; o_DEF] THEN
      MATCH_MP_TAC DIFFERENTIABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RFA_LBILIN_ON_SMOOTH = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> !U G tf tg.
               metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
               (!u. smooth_map_on U (\y. lift(tf y u))) /\
               (!u. smooth_map_on U (\y. lift(tg y u)))
               ==> ltensor_field k U (E G tf tg) /\
                   (!u. smooth_map_on U (\y. lift(E G tf tg y u)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agr"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
    `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
    RFA_LBILIN_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y u. y IN U
          ==> (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                 (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                G tf tg y u = B G tf tg y u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "agr" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTENSOR_FIELD_EQ THEN
    EXISTS_TAC `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                  (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                G tf tg` THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\y. lift((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                         G tf tg y u)` THEN
    ASM_SIMP_TAC[]]);;

let RFA_LBILIN_ON_NABLA = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E
        ==> ?E1 E2.
              lbilin_on (k + 1) (p + 1) q E1 /\ lbilin_on (k + 1) p (q + 1) E2 /\
              !U G tf tg y u.
                 metric_field U G /\ y IN U /\
                 ltensor_field p U tf /\ ltensor_field q U tg /\
                 (!u. smooth_map_on U (\y. lift(tf y u))) /\
                 (!u. smooth_map_on U (\y. lift(tg y u)))
                 ==> lnabla k G (E G tf tg) y u =
                     E1 G (lnabla p G tf) tg y u + E2 G tf (lnabla q G tg) y u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agr"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LBILIN_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN
   `B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (X_CHOOSE_THEN
   `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leib"))))) THEN
  MAP_EVERY EXISTS_TAC
   [`B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
    `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                   (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                   (real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla k (G:real^N->real^N^N)
                ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                    (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                 G tf tg) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "agr" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "leib" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Bookkeeping for the induction on m: index conversions and                *)
(* conditional sums in the class, tensor-field sums over 0..n, and the      *)
(* regrouping of the sum over i + j = m + 1.                                 *)
(* ========================================================================= *)

let RFA_LBILIN_ON_IDX = prove
 (`!k p q k' p' q' (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                       (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin_on k p q E /\ k = k' /\ p = p' /\ q = q' ==> lbilin_on k' p' q' E`,
  MESON_TAC[]);;

let RFA_LBILIN_ON_ADD_COND = prove
 (`!k p q (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) E2 P.
        lbilin_on k p q E1 /\ (P ==> lbilin_on k p q E2)
        ==> lbilin_on k p q
              (\G sf tf y u. E1 G sf tf y u + (if P then E2 G sf tf y u else &0))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN ASM_SIMP_TAC[];
    REWRITE_TAC[REAL_ADD_RID; ETA_AX] THEN ASM_REWRITE_TAC[]]);;

let RFA_TENSOR_FIELD_SUM0 = prove
 (`!k U (f:num->real^N->(num->real^N)->real) n.
        open U /\
        (!i. i <= n ==> ltensor_field k U (f i) /\
                        (!u. smooth_map_on U (\y. lift(f i y u))))
        ==> ltensor_field k U (\z u. sum(0..n) (\i. f i z u)) /\
            (!u. smooth_map_on U (\y. lift(sum(0..n) (\i. f i y u))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL; ETA_AX];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]]);;

let RFA_SUM_REGROUP = prove
 (`!m (w:num->real) (x:num->real) (ya:num->real) (zb:num->real).
        sum(0..SUC m) (\j. (if j = 0 then w j else &0) + (if j = 1 then x j else &0) +
                           (if 1 <= j then ya j else &0) + (if j <= m then zb j else &0)) =
        w 0 + x 1 + sum(0..m) (\i. ya (i + 1)) + sum(0..m) zb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN `!c (f:num->real). (\j. if j = c then f j else &0) =
                                  (\j. if j = c then f c else &0)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; ARITH_RULE `1 <= SUC m`] THEN
  SUBGOAL_THEN
   `sum(0..SUC m) (\j. if 1 <= j then (ya:num->real) j else &0) =
    sum(0..m) (\i. ya (i + 1))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
      [MATCH_MP SUM_CLAUSES_LEFT (ARITH_RULE `0 <= SUC m`)] THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= 0)`; REAL_ADD_LID; ADD_CLAUSES] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1..SUC m) (ya:num->real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
      REWRITE_TAC[ADD1] THEN
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o LAND_CONV)
        [ARITH_RULE `1 = 0 + 1`] THEN
      REWRITE_TAC[SUM_OFFSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..SUC m) (\j. if j <= m then (zb:num->real) j else &0) = sum(0..m) zb`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC m <= m)`;
                REAL_ADD_RID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
    REFL_TAC]);;

let RFA_A9_CLASS = prove
 (`!m (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
    lbilin_on ((4 + m) + 1) 4 ((4 + m) + 1) E1 /\
    lbilin_on ((4 + m) + 1) 5 (4 + m) E2 /\
    lbilin_on ((4 + m) + 1) 5 (4 + m) Eg /\
    (!i. i <= m ==> lbilin_on ((4 + m) + 1) ((4 + i) + 1) (4 + (m - i)) (Ea i) /\
                    lbilin_on ((4 + m) + 1) (4 + i) ((4 + (m - i)) + 1) (Eb i))
    ==> !j. j <= SUC m
            ==> lbilin_on (4 + SUC m) (4 + j) (4 + (SUC m - j))
                  (\G sf tf y u. (if j = 0 then E1 G sf tf y u else &0) +
                                 (if j = 1 then E2 G sf tf y u - Eg G sf tf y u
                                  else &0) +
                                 (if 1 <= j then Ea (j - 1) G sf tf y u else &0) +
                                 (if j <= m then Eb j G sf tf y u else &0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hab")))) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ARITH; LE_0; REAL_ADD_LID] THEN
    MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RFA_LBILIN_ON_IDX THENL
     [MAP_EVERY EXISTS_TAC [`(4 + m) + 1`; `4`; `(4 + m) + 1`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`(4 + m) + 1`; `4 + 0`; `(4 + (m - 0)) + 1`] THEN
      CONJ_TAC THENL
       [USE_THEN "hab" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0; ETA_AX] THEN
        SIMP_TAC[];
        ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC
   `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
     (tf:real^N->(num->real^N)->real) y u.
      (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
        (tf:real^N->(num->real^N)->real) y u.
         (Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (j - 1) G sf tf y u +
         (if j = 1 then (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y u - (Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y u else &0))
       G sf tf y u +
      (if j <= m then (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) j G sf tf y u else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_ADD_COND THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LBILIN_ON_ADD_COND THEN CONJ_TAC THENL
       [MATCH_MP_TAC RFA_LBILIN_ON_IDX THEN
        MAP_EVERY EXISTS_TAC [`(4 + m) + 1`; `(4 + (j - 1)) + 1`; `4 + (m - (j - 1))`] THEN
        CONJ_TAC THENL
         [USE_THEN "hab" (MP_TAC o SPEC `j - 1`) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ETA_AX] THEN SIMP_TAC[]];
          ASM_ARITH_TAC];
        DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC RFA_LBILIN_ON_IDX THEN
        MAP_EVERY EXISTS_TAC [`(4 + m) + 1`; `5`; `4 + m`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_IDX THEN
      MAP_EVERY EXISTS_TAC [`(4 + m) + 1`; `4 + j`; `(4 + (m - j)) + 1`] THEN
      CONJ_TAC THENL
       [USE_THEN "hab" (MP_TAC o SPEC `j:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ETA_AX] THEN SIMP_TAC[]];
        ASM_ARITH_TAC]];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The derivative of nabla^(m+1) Rm in the induction step, before           *)
(* regrouping: from RFA_LNABLA_DT, RFA_LTLAP_COMMUTE, the Leibniz rule and  *)
(* RFA_DGAMMA_TERM.                                                         *)

let RFA_A9_FIELDS = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> !s j. a < s /\ s < b
               ==> ltensor_field (4 + j) U (lnabla_iter 4 j (G s) (lrm4 (G s))) /\
                   (!u. smooth_map_on U (\x. lift(lnabla_iter 4 j (G s) (lrm4 (G s)) x u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) s`]
         LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `(G:real->real^N->real^N^N) s`;
                 `lrm4 ((G:real->real^N->real^N^N) s)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[]);;

let RFA_A9_DERIV = prove
 (`!m (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
    U a b (G:real->real^N->real^N^N) t y u.
     (!i. i <= m ==> lbilin_on (4 + m) (4 + i) (4 + (m - i)) (E i)) /\
     (!U a b (G:real->real^N->real^N^N) t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lnabla_iter 4 m (G s) (lrm4 (G s)) y u) has_real_derivative
             ltlap (4 + m) (G t) (lnabla_iter 4 m (G t) (lrm4 (G t))) y u +
             sum(0..m) (\i. E i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                    (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) y u))
            (atreal t)) /\
     (!U (G:real^N->real^N^N) tf y u.
        metric_field U G /\ ltensor_field (4 + m) U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla (4 + m) G (ltlap (4 + m) G tf) y u =
            ltlap ((4 + m) + 1) G (lnabla (4 + m) G tf) y u +
            E1 G (lrm4 G) (lnabla (4 + m) G tf) y u +
            E2 G (lnabla 4 G (lrm4 G)) tf y u) /\
     (!U a b (G:real->real^N->real^N^N) (tf:real^N->(num->real^N)->real) t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
        ltensor_field (4 + m) U tf
        ==> sum(1..4 + m) (\i. tf y (\j. if j = i
                                       then ldgamma G t y (u((4 + m) + 1)) (u i)
                                       else u j)) =
            Eg (G t) (lnabla 4 (G t) (lrm4 (G t))) tf y u) /\
     (!i. i <= m
          ==> !U G tf tg y u.
                 metric_field U G /\ y IN U /\
                 ltensor_field (4 + i) U tf /\ ltensor_field (4 + (m - i)) U tg /\
                 (!u. smooth_map_on U (\y. lift(tf y u))) /\
                 (!u. smooth_map_on U (\y. lift(tg y u)))
                 ==> lnabla (4 + m) G (E i G tf tg) y u =
                     Ea i G (lnabla (4 + i) G tf) tg y u +
                     Eb i G tf (lnabla (4 + (m - i)) G tg) y u) /\
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. lnabla (4 + m) (G s) (lnabla_iter 4 m (G s) (lrm4 (G s))) y u)
          has_real_derivative
          ((ltlap ((4 + m) + 1) (G t)
              (lnabla (4 + m) (G t) (lnabla_iter 4 m (G t) (lrm4 (G t)))) y u +
            E1 (G t) (lrm4 (G t))
              (lnabla (4 + m) (G t) (lnabla_iter 4 m (G t) (lrm4 (G t)))) y u +
            E2 (G t) (lnabla 4 (G t) (lrm4 (G t))) (lnabla_iter 4 m (G t) (lrm4 (G t)))
              y u) +
           sum(0..m) (\i. Ea i (G t)
                            (lnabla (4 + i) (G t) (lnabla_iter 4 i (G t) (lrm4 (G t))))
                            (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) y u +
                          Eb i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                            (lnabla (4 + (m - i)) (G t)
                               (lnabla_iter 4 (m - i) (G t) (lrm4 (G t)))) y u)) -
          Eg (G t) (lnabla 4 (G t) (lrm4 (G t))) (lnabla_iter 4 m (G t) (lrm4 (G t))) y u)
         (atreal t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cls") (CONJUNCTS_THEN2 (LABEL_TAC "ih")
   (CONJUNCTS_THEN2 (LABEL_TAC "a5") (CONJUNCTS_THEN2 (LABEL_TAC "dg")
   (CONJUNCTS_THEN2 (LABEL_TAC "lb") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "tt" o MATCH_MP RFA_A9_FIELDS) THEN
  SUBGOAL_THEN
   `!j. ltensor_field (4 + j) U
          (lnabla_iter 4 j ((G:real->real^N->real^N^N) t) (lrm4 (G t))) /\
        (!u. smooth_map_on U (\x. lift(lnabla_iter 4 j (G t) (lrm4 (G t)) x u)))`
  (LABEL_TAC "ttt") THENL
   [GEN_TAC THEN USE_THEN "tt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= m
        ==> ltensor_field (4 + m) U
              ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i ((G:real->real^N->real^N^N) t)
                 (lnabla_iter 4 i (G t) (lrm4 (G t)))
                 (lnabla_iter 4 (m - i) (G t) (lrm4 (G t)))) /\
            (!u. smooth_map_on U
                   (\x. lift(E i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                       (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) x u)))`
  (LABEL_TAC "ef") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cls" (MP_TAC o MATCH_MP RFA_LBILIN_ON_SMOOTH o
                    C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ttt" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field (4 + m) U
      (\z v. ltlap (4 + m) ((G:real->real^N->real^N^N) t)
               (lnabla_iter 4 m (G t) (lrm4 (G t))) z v +
             sum(0..m) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                 (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) z v)) /\
    (!u. (\x. lift(ltlap (4 + m) ((G:real->real^N->real^N^N) t)
                     (lnabla_iter 4 m (G t) (lrm4 (G t))) x u)) differentiable at y) /\
    (!u. (\x. lift(sum(0..m) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i ((G:real->real^N->real^N^N) t)
                         (lnabla_iter 4 i (G t) (lrm4 (G t)))
                         (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) x u)))
         differentiable at y)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4 + m`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lnabla_iter 4 m ((G:real->real^N->real^N^N) t) (lrm4 (G t))`]
           RFA_LTLAP_FIELD) THEN
    USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`4 + m`; `U:real^N->bool`;
      `\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i ((G:real->real^N->real^N^N) t)
             (lnabla_iter 4 i (G t) (lrm4 (G t)))
             (lnabla_iter 4 (m - i) (G t) (lrm4 (G t)))`; `m:num`]
      RFA_TENSOR_FIELD_SUM0) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "ef" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[ETA_AX];
      STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4 + m`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`;
                 `\s. lnabla_iter 4 m ((G:real->real^N->real^N^N) s) (lrm4 (G s))`;
                 `\z v. ltlap (4 + m) ((G:real->real^N->real^N^N) t)
                          (lnabla_iter 4 m (G t) (lrm4 (G t))) z v +
                        sum(0..m) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t)
                                         (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                         (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) z v)`;
                 `t:real`; `y:real^N`; `u:num->real^N`] RFA_LNABLA_DT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "tt" (MP_TAC o SPECL [`s:real`; `m:num`]) THEN ASM_SIMP_TAC[];
      GEN_TAC THEN MATCH_MP_TAC RFA_LSMOOTH_LRM_DERIV THEN
      ASM_SIMP_TAC[RFA_LRICCI_FLOW_LSMOOTH];
      REPEAT STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  BINOP_TAC THENL
   [ALL_TAC;
    USE_THEN "dg" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ttt" (fun th -> REWRITE_TAC[th])] THEN
  MP_TAC(ISPECL [`4 + m`; `(G:real->real^N->real^N^N) t`;
                 `ltlap (4 + m) ((G:real->real^N->real^N^N) t)
                    (lnabla_iter 4 m (G t) (lrm4 (G t)))`;
                 `\z v. sum(0..m) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i ((G:real->real^N->real^N^N) t)
                                        (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                        (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) z v)`;
                 `y:real^N`; `u:num->real^N`] LRG_LNABLA_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  BINOP_TAC THENL
   [USE_THEN "a5" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ttt" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4 + m`; `(G:real->real^N->real^N^N) t`;
                 `\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i ((G:real->real^N->real^N^N) t)
                        (lnabla_iter 4 i (G t) (lrm4 (G t)))
                        (lnabla_iter 4 (m - i) (G t) (lrm4 (G t)))`;
                 `y:real^N`; `u:num->real^N`; `m:num`] RFA_LNABLA_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ef" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    SIMP_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "lb" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "ttt" (fun th -> REWRITE_TAC[th]));;

(* The evolution of nabla^m Rm in class form, by induction on m.            *)

let RFA_LRM_DERIV_EVOLUTION_ON = prove
 (`!m. ?E. (!i. i <= m ==> lbilin_on (4 + m) (4 + i) (4 + (m - i)) (E i)) /\
           !U a b (G:real->real^N->real^N^N) t y u.
              lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
              ==> ((\s. lnabla_iter 4 m (G s) (lrm4 (G s)) y u) has_real_derivative
                   ltlap (4 + m) (G t) (lnabla_iter 4 m (G t) (lrm4 (G t))) y u +
                   sum(0..m) (\i. E i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                         (lnabla_iter 4 (m - i) (G t) (lrm4 (G t))) y u))
                  (atreal t)`,
  INDUCT_TAC THENL
   [X_CHOOSE_THEN `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a8"))
      RFA_LRM4_EVOLUTION THEN
    EXISTS_TAC `\i:num. (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[LE; ADD_CLAUSES; SUB_REFL; SUM_SING_NUMSEG; lnabla_iter] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ADD_CLAUSES; SUB_REFL] THEN ASM_SIMP_TAC[RFA_LBILIN_ON_LBILIN];
      REPEAT STRIP_TAC THEN USE_THEN "a8" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "cls") (LABEL_TAC "ih"))) THEN
  X_CHOOSE_THEN `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (X_CHOOSE_THEN `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a5"))))
    (SPEC `4 + m` RFA_LTLAP_COMMUTE_ON) THEN
  X_CHOOSE_THEN `Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dg"))
    (SPEC `4 + m` RFA_DGAMMA_TERM) THEN
  SUBGOAL_THEN
   `!i. ?ea eb.
      i <= m
      ==> lbilin_on ((4 + m) + 1) ((4 + i) + 1) (4 + (m - i)) (ea:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) /\
          lbilin_on ((4 + m) + 1) (4 + i) ((4 + (m - i)) + 1) (eb:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) /\
          (!U G tf tg y u.
             metric_field U G /\ y IN U /\
             ltensor_field (4 + i) U tf /\ ltensor_field (4 + (m - i)) U tg /\
             (!u. smooth_map_on U (\y. lift(tf y u))) /\
             (!u. smooth_map_on U (\y. lift(tg y u)))
             ==> lnabla (4 + m) G ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i G tf tg) y u =
                 ea G (lnabla (4 + i) G tf) tg y u +
                 eb G tf (lnabla (4 + (m - i)) G tg) y u)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num <= m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LBILIN_ON_NABLA THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "cls" (MATCH_ACCEPT_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`);
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (X_CHOOSE_THEN `Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (LABEL_TAC "lab"))) THEN
  EXISTS_TAC
   `\j (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
      (if j = 0 then (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y u else &0) +
      (if j = 1 then (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y u - (Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y u else &0) +
      (if 1 <= j then (Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (j - 1) G sf tf y u else &0) +
      (if j <= m then (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) j G sf tf y u else &0)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
                   `Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_A9_CLASS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "lab" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
      SIMP_TAC[];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT2 lnabla_iter] THEN
  MP_TAC(ISPECL [`m:num`; `E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
                 `Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`; `u:num->real^N`]
         RFA_A9_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "lab" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2 o CONJUNCT2);
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  MP_TAC(ISPECL
   [`m:num`;
    `\j. (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (y:real^N) (u:num->real^N)`;
    `\j. (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (y:real^N) (u:num->real^N) -
         (Eg:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (G t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y u`;
    `\j. (Ea:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (j - 1) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (y:real^N)
           (u:num->real^N)`;
    `\j. (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) j ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (y:real^N)
           (u:num->real^N)`] RFA_SUM_REGROUP) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `SUC m - 0 = SUC m`; ARITH_RULE `SUC m - 1 = m`;
              ARITH_RULE `!i. (i + 1) - 1 = i`;
              ARITH_RULE `!i. SUC m - (i + 1) = m - i`] THEN
  SUBGOAL_THEN
   `sum(0..m) (\j. (Eb:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) j ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (SUC m - j) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))
                     (y:real^N) (u:num->real^N)) =
    sum(0..m) (\i. Eb i (G t) (lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))
                     (lnabla (4 + (m - i)) (G t) (lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))) y u)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `SUC m - j = SUC(m - j)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[CONJUNCT2 lnabla_iter]];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 + SUC m = (4 + m) + 1`; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[CONJUNCT1 lnabla_iter; RFA_LNABLA_ITER_1; GSYM ADD1;
              CONJUNCT2 lnabla_iter] THEN
  REAL_ARITH_TAC);;

(* The evolution of nabla^m Rm with the operations in lbilin.               *)

let RFA_LRM_DERIV_EVOLUTION = prove
 (`!m. ?B. (!i. i <= m ==> lbilin (4 + m) (4 + i) (4 + (m - i)) (B i)) /\
           !U a b (G:real->real^N->real^N^N) t y u.
              lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
              ==> ((\s. lnabla_iter 4 m (G s) (lrm4 (G s)) y u)
                   has_real_derivative
                   ltlap (4 + m) (G t) (lnabla_iter 4 m (G t) (lrm4 (G t))) y u +
                   sum(0..m) (\i. B i (G t) (lnabla_iter 4 i (G t) (lrm4 (G t)))
                                          (lnabla_iter 4 (m - i) (G t) (lrm4 (G t)))
                                          y u)) (atreal t)`,
  GEN_TAC THEN
  X_CHOOSE_THEN `E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "ev"))
    (SPEC `m:num` RFA_LRM_DERIV_EVOLUTION_ON) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[lbilin_on; RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (LABEL_TAC "bb")) THEN
  EXISTS_TAC `B:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "bb" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "tt" o MATCH_MP RFA_A9_FIELDS) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  USE_THEN "ev" (MP_TAC o SPECL [`U:real^N->bool`; `a:real`; `b:real`;
    `G:real->real^N->real^N^N`; `t:real`; `y:real^N`; `u:num->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "bb" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  USE_THEN "tt" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The evolution inequality for |nabla^m Rm|^2 for every m                   *)
(* (RFA_LRM_DERIV_NORM2_EVOLUTION):                                          *)
(*   d/dt |D^m Rm|^2 <= Lap |D^m Rm|^2 - 2 |D^(m+1) Rm|^2                    *)
(*                      + C |D^m Rm| sum_(i+j=m) |D^i Rm| |D^j Rm|.          *)
(* ========================================================================= *)

(* The time derivative of the squared norm of a family of tensors under a    *)
(* local Ricci flow (the k-slot form of RFA_RMNORM2_DERIV).                  *)

let RFA_TNORM2_DERIV = prove
 (`!k U a b (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real)
    (Df:real^N->(num->real^N)->real) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
        (!u. ((\s. Tf s y u) has_real_derivative Df y u) (atreal t))
        ==> ((\s. ltnorm2 k (G s) (Tf s) y) has_real_derivative
             &2 * ltinner k (G t) (Tf t) Df y +
             ltinner k (G t) (Tf t)
               (\z u. sum(1..k) (\l. &2 * rfa_qact l (G t)
                                    (ltcontr (G t) (ltperm (swap(2,3)) (lrm4 (G t))))
                                    (Tf t) z u)) y) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  REWRITE_TAC[RFA_LTNORM2_LTC] THEN
  MP_TAC(ISPECL
   [`k:num`; `\s. matrix_inv((G:real->real^N->real^N^N) s y)`;
    `--(matrix_inv((G:real->real^N->real^N^N) t y) **
        (lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)) **
        matrix_inv(G t y))`;
    `\s. (Tf:real->real^N->(num->real^N)->real) s y`;
    `\ip. (Df:real^N->(num->real^N)->real) y (\m. basis(ip m))`;
    `\s. (Tf:real->real^N->(num->real^N)->real) s y`;
    `\ip. (Df:real^N->(num->real^N)->real) y (\m. basis(ip m))`;
    `t:real`] RFA_LTC_DERIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
      MATCH_MP_TAC LRG_VDERIV_MATRIX_ENTRY_REAL THEN BETA_TAC THEN
      MATCH_MP_TAC LRG_FLOW_DGINV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltinner k ((G:real->real^N->real^N^N) t) Df (Tf t) y +
                ltinner k (G t) ((Tf:real->real^N->(num->real^N)->real) t) Df y` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ltinner; GSYM(MATCH_MP RFA_SUM2_ADD
        (CONJ (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)
              (SPEC `k:num` LRG_INDEX_TUPLES_FINITE)))] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC(REAL_RING
       `p = q ==> (a * r + r' * a') * p = a * r * q + r' * a' * q`) THEN
      REFL_TAC;
      MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `Df:real^N->(num->real^N)->real`;
                     `(Tf:real->real^N->(num->real^N)->real) t`; `y:real^N`]
             RFA_LTINNER_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `--(matrix_inv((G:real->real^N->real^N^N) t y) **
       (lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)) **
       matrix_inv(G t y)) =
    matrix_inv(G t y) **
    (--((lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)):real^N^N)) **
    matrix_inv(G t y)`
  SUBST1_TAC THENL [REWRITE_TAC[MATRIX_MUL_LNEG; MATRIX_MUL_RNEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_LTQ_QACT] THEN REWRITE_TAC[RFA_LTINNER_LTC] THEN
  MATCH_MP_TAC RFA_LTC_RBASIS THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC RFA_QACTE_RIC THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[]);;

let RFA_QRIC_LBILIN = prove
 (`!k. 1 <= k
       ==> lbilin_on k 4 k
             (\(G:real^N->real^N^N) sf tf z u.
                sum(1..k) (\l. &2 * rfa_qact l G (ltcontr G (ltperm (swap(2,3)) sf))
                                                tf z u))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
               (tf:real^N->(num->real^N)->real).
                rfa_qact l G (ltcontr G (ltperm (swap(2,3)) sf)) tf` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_QACT_RIC_LBILIN THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[]]);;

(* Cauchy-Schwarz with a bilinear bound: <R, E> <= sqrt C |R| |S| |T| when   *)
(* |E|^2 <= C |S|^2 |T|^2.                                                   *)

let RFA_INNER_BIL_BOUND = prove
 (`!k p q U (G0:real^N->real^N^N) Rf Ef Sf Tf y C0.
        metric_field U G0 /\ ltensor_field k U Rf /\ ltensor_field k U Ef /\
        ltensor_field p U Sf /\ ltensor_field q U Tf /\ y IN U /\ &0 <= C0 /\
        ltnorm2 k G0 Ef y <= C0 * ltnorm2 p G0 Sf y * ltnorm2 q G0 Tf y
        ==> ltinner k G0 Rf Ef y <=
            sqrt C0 * sqrt(ltnorm2 k G0 Rf y) *
            (sqrt(ltnorm2 p G0 Sf y) * sqrt(ltnorm2 q G0 Tf y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 k (G0:real^N->real^N^N) Rf y /\ &0 <= ltnorm2 k G0 Ef y /\
    &0 <= ltnorm2 p G0 Sf y /\ &0 <= ltnorm2 q G0 Tf y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LTNORM2_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `Rf:real^N->(num->real^N)->real`; `Ef:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LTINNER_ABS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 k (G0:real^N->real^N^N) Ef y) <=
    sqrt C0 * sqrt(ltnorm2 p G0 Sf y) * sqrt(ltnorm2 q G0 Tf y)`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y)` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(ltnorm2 k (G0:real^N->real^N^N) Rf y)` THEN
  ABBREV_TAC `e = sqrt(ltnorm2 k (G0:real^N->real^N^N) Ef y)` THEN
  ABBREV_TAC `s = sqrt(ltnorm2 p (G0:real^N->real^N^N) Sf y)` THEN
  ABBREV_TAC `w = sqrt(ltnorm2 q (G0:real^N->real^N^N) Tf y)` THEN
  ABBREV_TAC `c = sqrt C0` THEN
  ABBREV_TAC `x = ltinner k (G0:real^N->real^N^N) Rf Ef y` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `r * e <= r * (c * s * w)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r * (c * s * w) = c * r * (s * w)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  UNDISCH_TAC `abs x <= r * e` THEN REAL_ARITH_TAC);;

(* The evolution inequality for |nabla^m Rm|^2.                               *)

let RFA_LRM_DERIV_NORM2_EVOLUTION = prove
 (`!m. ?C. &0 <= C /\
           !U a b (G:real->real^N->real^N^N) t y.
              lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
              ==> ?d. ((\s. lrm_deriv_norm2 m (G s) y) has_real_derivative d)
                        (atreal t) /\
                      d <= llap (G t) (lrm_deriv_norm2 m (G t)) y -
                           &2 * lrm_deriv_norm2 (m + 1) (G t) y +
                           C * sqrt(lrm_deriv_norm2 m (G t) y) *
                           sum(0..m) (\i. sqrt(lrm_deriv_norm2 i (G t) y) *
                                          sqrt(lrm_deriv_norm2 (m - i) (G t) y))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2 (LABEL_TAC "cls") (LABEL_TAC "ev"))
    (SPEC `m:num` RFA_LRM_DERIV_EVOLUTION_ON) THEN
  SUBGOAL_THEN
   `!i. ?c. i <= m
            ==> &0 <= c /\
                !U G tf tg y.
                   metric_field U G /\ y IN U /\
                   ltensor_field (4 + i) U tf /\ ltensor_field (4 + (m - i)) U tg
                   ==> ltnorm2 (4 + m) G ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i G tf tg) y <=
                       c * ltnorm2 (4 + i) G tf y * ltnorm2 (4 + (m - i)) G tg y`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num <= m` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cls" (MP_TAC o MATCH_MP RFA_LBILIN_ON_NORM o
                    C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cn:num->real` (LABEL_TAC "cn")) THEN
  MP_TAC(MATCH_MP RFA_LBILIN_ON_NORM
    (MATCH_MP (INST_TYPE [`:N`,`:N`] RFA_QRIC_LBILIN) (ARITH_RULE `1 <= 4 + m`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `CQ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cq"))) THEN
  SUBGOAL_THEN `!i. i <= m ==> &0 <= (Cn:num->real) i` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cn" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = sum(0..m) (\i. sqrt((Cn:num->real) i))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * K + sqrt CQ` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `a:real`; `b:real`;
                       `G:real->real^N->real^N^N`; `t:real`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "tt" o MATCH_MP RFA_A9_FIELDS) THEN
  SUBGOAL_THEN
   `!j. ltensor_field (4 + j) U (lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) /\ (!u. smooth_map_on U (\x. lift((lnabla_iter 4 (j) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) x u)))`
  (LABEL_TAC "ttt") THENL
   [GEN_TAC THEN USE_THEN "tt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(H:real^N->real^N^N). lrm_deriv_norm2 m H = ltnorm2 (4 + m) H (lnabla_iter 4 m H (lrm4 H))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; lrm_deriv_norm2]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`4 + m`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
    `\s. lnabla_iter 4 m ((G:real->real^N->real^N^N) s) (lrm4 (G s))`;
    `\z v. ltlap (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) z v +
           sum(0..m) (\i. (E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t) (lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) z v)`;
    `t:real`; `y:real^N`] RFA_TNORM2_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "ev" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> EXISTS_TAC(rand(rator(concl th))) THEN
                       CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  SUBGOAL_THEN
   `!i. i <= m ==> ltensor_field (4 + m) U ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t) (lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))))`
  (LABEL_TAC "ef") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cls" (MP_TAC o MATCH_MP RFA_LBILIN_ON_SMOOTH o
                    C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                               `(lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))`; `(lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))`]) THEN
    USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= m
        ==> ltinner (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))
              ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t) (lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))) y <=
            sqrt((Cn:num->real) i) * sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
    MATCH_MP_TAC RFA_INNER_BIL_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    USE_THEN "cn" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ttt" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [USE_THEN "ef" (ACCEPT_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`);
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ttt" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltinner (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (\z u. sum(1..4 + m) (\l. &2 * rfa_qact l ((G:real->real^N->real^N^N) t) (ltcontr (G t) (ltperm (swap(2,3)) (lrm4 (G t)))) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) z u)) y <=
    sqrt CQ * sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) *
    (sqrt(lrm_deriv_norm2 0 (G t) y) * sqrt(lrm_deriv_norm2 (m - 0) (G t) y))`
  ASSUME_TAC THENL
   [REWRITE_TAC[lrm_deriv_norm2; SUB_0; ADD_CLAUSES; CONJUNCT1 lnabla_iter] THEN
    MATCH_MP_TAC RFA_INNER_BIL_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] LRM4_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP RFA_LBILIN_ON_SMOOTH
      (MATCH_MP (INST_TYPE [`:N`,`:N`] RFA_QRIC_LBILIN) (ARITH_RULE `1 <= 4 + m`))) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                               `lrm4 ((G:real->real^N->real^N^N) t)`; `(lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))`]) THEN
    USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ttt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cq" (MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                                   `lrm4 ((G:real->real^N->real^N^N) t)`; `(lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))`;
                                   `y:real^N`]) THEN
    ANTS_TAC THENL [USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]); REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= m ==> &0 <= sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))`
  (LABEL_TAC "xpos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REWRITE_TAC[lrm_deriv_norm2] THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..m) (\i. sqrt((Cn:num->real) i) * sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))) <=
    K * (sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * sum(0..m) (\i. (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [EXPAND_TAC "K" THEN
      MP_TAC(ISPECL [`\i. sqrt((Cn:num->real) i)`;
                     `sum(0..m) (\i. sqrt((Cn:num->real) i))`; `0..m`]
             SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL; LE_0] THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ASM_SIMP_TAC[]];
      USE_THEN "xpos" (MP_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) *
    (sqrt(lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) t) y) *
     sqrt(lrm_deriv_norm2 (m - 0) (G t) y)) <=
    sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * sum(0..m) (\i. (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    MP_TAC(ISPECL [`\i. sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))`; `sum(0..m) (\i. sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y)))`; `0..m`]
           SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL; LE_0] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "xpos" (ACCEPT_TAC o C MP (ASSUME `(i:num) <= m`) o SPEC `i:num`);
      DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4 + m`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))`;
                 `y:real^N`] RFA_LLAP_LTNORM2) THEN
  ANTS_TAC THENL [USE_THEN "ttt" (fun th -> ASM_REWRITE_TAC[th]); DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RFA_LTINNER_RADD;
              MATCH_MP RFA_LTINNER_RSUM (SPECL [`0`; `m:num`] FINITE_NUMSEG); ETA_AX] THEN
  SUBGOAL_THEN
   `lrm_deriv_norm2 (m + 1) ((G:real->real^N->real^N^N) t) y =
    ltnorm2 ((4 + m) + 1) (G t) (lnabla (4 + m) (G t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[lrm_deriv_norm2; GSYM ADD1; ARITH_RULE `4 + SUC m = SUC(4 + m)`;
                CONJUNCT2 lnabla_iter];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..m) (\i. ltinner (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))
                    ((E:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) i (G t) (lnabla_iter 4 (i) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) (lnabla_iter 4 (m - i) ((G:real->real^N->real^N^N) t) (lrm4 (G t)))) y) <=
    sum(0..m) (\i. sqrt((Cn:num->real) i) * sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y)))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt CQ * sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) *
    (sqrt(lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) t) y) *
     sqrt(lrm_deriv_norm2 (m - 0) (G t) y)) <=
    sqrt CQ * (sqrt(ltnorm2 (4 + m) ((G:real->real^N->real^N^N) t) (lnabla_iter 4 (m) ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y) * sum(0..m) (\i. (sqrt(lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y) * sqrt(lrm_deriv_norm2 (m - i) (G t) y))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let c = concl th in is_binary "real_le" c)) THEN
  REAL_ARITH_TAC);;

