(* ========================================================================= *)
(* Unit pc_rfa_raylap: the Laplacian of the Rayleigh barrier                 *)
(* (RFA_BARRIER_LAP).  For a symmetric (0,2)-tensor field T with T(y0) e = 0 *)
(* and the vector field E(y) = e - Gamma(y0)(y - y0, e), covariantly         *)
(* constant at y0, the Laplacian of y -> T_y(E y, E y) at y0 is (Lap T)(e,e) *)
(* (ltlap 2).                                                                *)
(* ========================================================================= *)

needs "src/pc_rfa_pevol.ml";;
needs "src/pc_rfa_slcalc.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Slot lemmas for tensor fields and the Leibniz rule for a                  *)
(* tensor field evaluated on vector fields (RFA_LNABLA_EVAL).               *)
(* ========================================================================= *)

let RFA_TENSOR_LOCAL = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u u'.
     ltensor_field k U tf /\ y IN U /\ (!m. 1 <= m /\ m <= k ==> u m = u' m)
     ==> tf y u = tf y u'`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

let RFA_TENSOR_SLOT_ADD = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u m a b.
     ltensor_field k U tf /\ y IN U /\ 1 <= m /\ m <= k
     ==> tf y (\j. if j = m then a + b else u j) =
         tf y (\j. if j = m then a else u j) + tf y (\j. if j = m then b else u j)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `u:num->real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`] o MATCH_MP LINEAR_ADD) THEN
  REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ]);;

let RFA_TENSOR_SLOT_ZERO = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u m.
     ltensor_field k U tf /\ y IN U /\ 1 <= m /\ m <= k /\ u m = vec 0
     ==> tf y u = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:num->real^N) = (\j. if j = m then vec 0 else u j)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `u:num->real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]);;

(* lnabla with the derivative slot k+1 filled in, unfolded.               *)

let RFA_LNABLA_SLOT_LAST = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (u:num->real^N) h.
     open U /\ ltensor_field k U tf /\ y IN U
     ==> lnabla k G tf y (\j. if j = k + 1 then h else u j) =
         drop(frechet_derivative (\z. lift(tf z u)) (at y) h) -
         sum(1..k) (\m. tf y (\j. if j = m then christoffel G y h (u m) else u j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_TENSOR_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i = k + 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_TENSOR_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* The Leibniz rule for a tensor field evaluated on vector fields X(1..k):  *)
(* d/dh T(X) = (nabla_h T)(X) + sum_m T(.., nabla_h X_m, ..), with the       *)
(* covariant derivative nabla_h X_m = X_m' h + Gamma(h, X_m).                *)

let RFA_LNABLA_EVAL = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
    (X:real^N->num->real^N) (X':num->real^N->real^N) y.
     metric_field U G /\ ltensor_field k U tf /\
     (!u. smooth_map_on U (\z. lift(tf z u))) /\ y IN U /\
     (!m. 1 <= m /\ m <= k ==> ((\z. X z m) has_derivative X' m) (at y))
     ==> ((\z. lift(tf z (X z))) has_derivative
          (\h. lift(lnabla k G tf y (\j. if j = k + 1 then h else X y j) +
                    sum(1..k) (\m. tf y (\j. if j = m
                                             then X' m h + christoffel G y h (X y m)
                                             else X y j))))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tf:real^N->(num->real^N)->real`; `X:real^N->num->real^N`;
                 `X':num->real^N->real^N`; `k:num`; `U:real^N->bool`; `y:real^N`]
         LRG_HAS_DERIVATIVE_MULTIFAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num->real^N` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\z. lift((tf:real^N->(num->real^N)->real) z c)`;
                   `y:real^N`; `vec 0:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `(X:real^N->num->real^N) y`; `h:real^N`] RFA_LNABLA_SLOT_LAST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum(1..k) (\m. (tf:real^N->(num->real^N)->real) y
                     (\j. if j = m
                          then (X':num->real^N->real^N) m h +
                               christoffel G y h ((X:real^N->num->real^N) y m)
                          else X y j)) =
    sum(1..k) (\m. tf y (\j. if j = m then X' m h else X y j)) +
    sum(1..k) (\m. tf y (\j. if j = m then christoffel G y h (X y m) else X y j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ADD THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The extension field E, the first and second derivatives of                *)
(* T(E,E) at y0, and the identity llap (T(E,E)) (y0) = (Lap T)(e,e).        *)
(* ========================================================================= *)

(* The extension E(z) = e - Gamma(y0)(z - y0, e) of a vector e at y0: its  *)
(* derivative, E(y0) = e, and its covariant derivative                       *)
(* nabla_h E (z) = --Gamma(y0)(h,e) + Gamma(z)(h,E z), zero at y0.          *)

let RFA_EXT_HAS_DERIVATIVE = prove
 (`!U (G:real^N->real^N^N) y0 e z.
     metric_field U G /\ y0 IN U
     ==> ((\x. e - christoffel G y0 (x - y0) e) has_derivative
          (\h. --(christoffel G y0 h e))) (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
         CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[bilinear] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (\h. christoffel (G:real^N->real^N^N) y0 h e)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. e - christoffel (G:real^N->real^N^N) y0 (x - y0) e) =
    (\x. (e + christoffel G y0 y0 e) - christoffel G y0 x e)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB th)]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. --(christoffel (G:real^N->real^N^N) y0 h e)) =
    (\h. vec 0 - christoffel G y0 h e)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[]);;

let RFA_EXT_AT = prove
 (`!U (G:real^N->real^N^N) y0 e.
     metric_field U G /\ y0 IN U
     ==> e - christoffel G y0 (y0 - y0) e = e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
         CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP BILINEAR_LZERO) THEN
  REWRITE_TAC[VECTOR_SUB_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  VECTOR_ARITH_TAC);;

let RFA_VEXT_ZERO = prove
 (`!U (G:real^N->real^N^N) y0 e h.
     metric_field U G /\ y0 IN U
     ==> --(christoffel G y0 h e) +
         christoffel G y0 h (e - christoffel G y0 (y0 - y0) e) = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let RFA_VEXT_DIFF = prove
 (`!U (G:real^N->real^N^N) y0 e w z.
     metric_field U G /\ y0 IN U /\ z IN U
     ==> (\x. --(christoffel G y0 w e) +
              christoffel G x w (e - christoffel G y0 (x - y0) e)) differentiable at z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ADD THEN REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC
   `\u. christoffel (G:real^N->real^N^N) z w (--(christoffel G y0 u e)) +
        frechet_derivative
          (\x. christoffel G x w (e - christoffel G y0 (z - y0) e)) (at z) u` THEN
  MP_TAC(ISPECL
   [`\x:real^N. christoffel (G:real^N->real^N^N) x w`;
    `\x:real^N. e - christoffel (G:real^N->real^N^N) y0 (x - y0) e`;
    `\h:real^N. --(christoffel (G:real^N->real^N^N) y0 h e)`;
    `U:real^N->bool`; `z:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`]
           CHRISTOFFEL_BILINEAR) THEN
    ASM_SIMP_TAC[bilinear; ETA_AX];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* First derivative of N(z) = T_z(E z, E z), at any z.                       *)

let RFA_EXT_DN = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e z h.
     metric_field U G /\ ltensor_field 2 U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y0 IN U /\ z IN U
     ==> frechet_derivative
           (\x. lift(tf x (\m. e - christoffel G y0 (x - y0) e))) (at z) h =
         lift(lnabla 2 G tf z
                (\j. if j = 3 then h else e - christoffel G y0 (z - y0) e) +
              tf z (\j. if j = 1
                        then --(christoffel G y0 h e) +
                             christoffel G z h (e - christoffel G y0 (z - y0) e)
                        else e - christoffel G y0 (z - y0) e) +
              tf z (\j. if j = 2
                        then --(christoffel G y0 h e) +
                             christoffel G z h (e - christoffel G y0 (z - y0) e)
                        else e - christoffel G y0 (z - y0) e))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`;
                 `\x:real^N m:num. e - christoffel (G:real^N->real^N^N) y0 (x - y0) e`;
                 `\m:num h:real^N. --(christoffel (G:real^N->real^N^N) y0 h e)`;
                 `z:real^N`] RFA_LNABLA_EVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT (BETA_RULE th))]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUM_2] THEN
  REWRITE_TAC[REAL_ADD_ASSOC]);;

(* Second derivative pieces at y0 (E covariantly constant at y0).          *)

let RFA_EXT_D2_L1 = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e w.
     metric_field U G /\ ltensor_field 2 U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y0 IN U
     ==> ((\z. lift(lnabla 2 G tf z
                     (\j. if j = 3 then w else e - christoffel G y0 (z - y0) e)))
          has_derivative
          (\h. lift(lnabla 3 G (lnabla 2 G tf) y0
                      (\j. if j = 4 then h else if j = 3 then w else e) +
                    lnabla 2 G tf y0
                      (\j. if j = 3 then christoffel G y0 h w else e)))) (at y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) tf`;
                 `\z:real^N j:num. if j = 3 then w
                                   else e - christoffel (G:real^N->real^N^N) y0 (z - y0) e`;
                 `\m:num h:real^N. if m = 3 then vec 0
                                   else --(christoffel (G:real^N->real^N^N) y0 h e)`;
                 `y0:real^N`] RFA_LNABLA_EVAL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  REWRITE_TAC[SUM_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!m. 1 <= m /\ m <= 3
        ==> lnabla 2 (G:real^N->real^N^N) tf y0
              (\j. if j = m then --christoffel G y0 h e + christoffel G y0 h e
                   else if j = 3 then w else e) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`; `m:num`] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LINV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[VECTOR_ADD_LID; REAL_ADD_LID]);;

let RFA_EXT_D2_L2 = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e w.
     metric_field U G /\ ltensor_field 2 U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y0 IN U /\
     (!v. tf y0 (\m. if m = 1 then v else e) = &0)
     ==> ((\z. lift(tf z (\j. if j = 1
                              then --(christoffel G y0 w e) +
                                   christoffel G z w (e - christoffel G y0 (z - y0) e)
                              else e - christoffel G y0 (z - y0) e)))
          has_derivative (\h. vec 0)) (at y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
     `tf:real^N->(num->real^N)->real`;
     `\z:real^N j:num.
        if j = 1 then --(christoffel (G:real^N->real^N^N) y0 w e) +
                      christoffel G z w (e - christoffel G y0 (z - y0) e)
        else e - christoffel G y0 (z - y0) e`;
     `\m:num. if m = 1
              then frechet_derivative
                     (\z. --(christoffel (G:real^N->real^N^N) y0 w e) +
                          christoffel G z w (e - christoffel G y0 (z - y0) e)) (at y0)
              else (\h:real^N. --(christoffel G y0 h e))`;
     `y0:real^N`] RFA_LNABLA_EVAL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC RFA_VEXT_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  REWRITE_TAC[SUM_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LINV] THEN
  SUBGOAL_THEN `!u. u 1 = vec 0 ==> lnabla 2 (G:real^N->real^N^N) tf y0 u = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`; `1`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u 1 = vec 0 ==> (tf:real^N->(num->real^N)->real) y0 u = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`; `1`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[REAL_ADD_LID; LIFT_NUM]);;

let RFA_EXT_D2_L3 = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e w.
     metric_field U G /\ ltensor_field 2 U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y0 IN U /\
     (!z v1 v2. z IN U
                ==> tf z (\m. if m = 1 then v1 else v2) =
                    tf z (\m. if m = 1 then v2 else v1)) /\
     (!v. tf y0 (\m. if m = 1 then v else e) = &0)
     ==> ((\z. lift(tf z (\j. if j = 2
                              then --(christoffel G y0 w e) +
                                   christoffel G z w (e - christoffel G y0 (z - y0) e)
                              else e - christoffel G y0 (z - y0) e)))
          has_derivative (\h. vec 0)) (at y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
     `tf:real^N->(num->real^N)->real`;
     `\z:real^N j:num.
        if j = 2 then --(christoffel (G:real^N->real^N^N) y0 w e) +
                      christoffel G z w (e - christoffel G y0 (z - y0) e)
        else e - christoffel G y0 (z - y0) e`;
     `\m:num. if m = 2
              then frechet_derivative
                     (\z. --(christoffel (G:real^N->real^N^N) y0 w e) +
                          christoffel G z w (e - christoffel G y0 (z - y0) e)) (at y0)
              else (\h:real^N. --(christoffel G y0 h e))`;
     `y0:real^N`] RFA_LNABLA_EVAL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC RFA_VEXT_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  REWRITE_TAC[SUM_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LINV] THEN
  SUBGOAL_THEN `!u. u 2 = vec 0 ==> lnabla 2 (G:real^N->real^N^N) tf y0 u = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`; `2`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u 2 = vec 0 ==> (tf:real^N->(num->real^N)->real) y0 u = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`; `2`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (tf:real^N->(num->real^N)->real) y0 (\j. if j = 2 then s else e) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N` THEN
    SUBGOAL_THEN `(tf:real^N->(num->real^N)->real) y0 (\j. if j = 2 then s else e) =
                  tf y0 (\m. if m = 1 then e else s)` SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_TENSOR_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      (SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[ARITH];
      FIRST_ASSUM(MP_TAC o SPECL [`y0:real^N`; `e:real^N`; `s:real^N`]) THEN
      REWRITE_TAC[ASSUME `(y0:real^N) IN U`] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[REAL_ADD_LID; LIFT_NUM]);;

(* The Laplacian of the Rayleigh numerator: if T(y0) e = 0 then           *)
(* llap (T(E,E)) (y0) = (Lap T)(e,e) for E = e - Gamma(y0)(y - y0, e).      *)

let RFA_RAYLEIGH_LAP = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e.
     metric_field U G /\ ltensor_field 2 U tf /\
     (!u. smooth_map_on U (\z. lift(tf z u))) /\
     (!z v1 v2. z IN U
                ==> tf z (\m. if m = 1 then v1 else v2) =
                    tf z (\m. if m = 1 then v2 else v1)) /\
     y0 IN U /\ (!v. tf y0 (\m. if m = 1 then v else e) = &0)
     ==> llap G (\z. tf z (\m. e - christoffel G y0 (z - y0) e)) y0 =
         ltlap 2 G tf y0 (\m. e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j. frechet_derivative
            (\z. frechet_derivative
                   (\w. lift((tf:real^N->(num->real^N)->real) w
                               (\m. e - christoffel G y0 (w - y0) e))) (at z)
                   (basis j)) (at y0) (basis i) =
          lift(lnabla 3 G (lnabla 2 G tf) y0
                 (\j'. if j' = 4 then basis i else if j' = 3 then basis j else e) +
               lnabla 2 G tf y0
                 (\j'. if j' = 3 then christoffel G y0 (basis i) (basis j) else e))`
  (LABEL_TAC "d2") THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative
        (\z. frechet_derivative
               (\w. lift((tf:real^N->(num->real^N)->real) w
                           (\m. e - christoffel G y0 (w - y0) e))) (at z)
               (basis j)) (at y0) =
      frechet_derivative
        (\z. lift(lnabla 2 G tf z
                    (\j'. if j' = 3 then basis j else e - christoffel G y0 (z - y0) e)) +
             lift(tf z (\j'. if j' = 1
                             then --(christoffel G y0 (basis j) e) +
                                  christoffel G z (basis j)
                                    (e - christoffel G y0 (z - y0) e)
                             else e - christoffel G y0 (z - y0) e)) +
             lift(tf z (\j'. if j' = 2
                             then --(christoffel G y0 (basis j) e) +
                                  christoffel G z (basis j)
                                    (e - christoffel G y0 (z - y0) e)
                             else e - christoffel G y0 (z - y0) e))) (at y0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `tf:real^N->(num->real^N)->real`; `y0:real^N`; `e:real^N`;
                     `z:real^N`; `basis j:real^N`] RFA_EXT_DN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LIFT_ADD];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y0:real^N`; `e:real^N`;
                   `basis j:real^N`] RFA_EXT_D2_L1) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y0:real^N`; `e:real^N`;
                   `basis j:real^N`] RFA_EXT_D2_L2) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y0:real^N`; `e:real^N`;
                   `basis j:real^N`] RFA_EXT_D2_L3) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `((\z. lift(lnabla 2 (G:real^N->real^N^N) tf z
                   (\j'. if j' = 3 then basis j else e - christoffel G y0 (z - y0) e)) +
            lift((tf:real^N->(num->real^N)->real) z
                   (\j'. if j' = 1
                         then --(christoffel G y0 (basis j) e) +
                              christoffel G z (basis j)
                                (e - christoffel G y0 (z - y0) e)
                         else e - christoffel G y0 (z - y0) e)) +
            lift(tf z (\j'. if j' = 2
                            then --(christoffel G y0 (basis j) e) +
                                 christoffel G z (basis j)
                                   (e - christoffel G y0 (z - y0) e)
                            else e - christoffel G y0 (z - y0) e)))
       has_derivative
       (\h. lift(lnabla 3 G (lnabla 2 G tf) y0
                   (\j'. if j' = 4 then h else if j' = 3 then basis j else e) +
                 lnabla 2 G tf y0
                   (\j'. if j' = 3 then christoffel G y0 h (basis j) else e)) +
            (vec 0 + vec 0))) (at y0)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. frechet_derivative
          (\z. lift((tf:real^N->(num->real^N)->real) z
                      (\m. e - christoffel G y0 (z - y0) e))) (at y0) (basis k) =
        lift(lnabla 2 G tf y0 (\j'. if j' = 3 then basis k else e))`
  (LABEL_TAC "d1") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y0:real^N`; `e:real^N`;
                   `y0:real^N`; `basis k:real^N`] RFA_EXT_DN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ADD_LINV] THEN
    SUBGOAL_THEN `(!u. u 1 = vec 0 ==> (tf:real^N->(num->real^N)->real) y0 u = &0) /\
                  (!u. u 2 = vec 0 ==> tf y0 u = &0)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TENSOR_SLOT_ZERO THENL
       [MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`; `1`];
        MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`; `2`]] THEN
      ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. sum(1..dimindex(:N))
            (\k. (christoffel (G:real^N->real^N^N) y0 (basis i) (basis j))$k *
                 lnabla 2 G tf y0 (\j'. if j' = 3 then basis k else e)) =
          lnabla 2 G tf y0
            (\j'. if j' = 3 then christoffel G y0 (basis i) (basis j) else e)`
  (LABEL_TAC "ct") THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(BETA_RULE(ISPECL [`lnabla 2 (G:real^N->real^N^N) tf y0`; `3`;
                             `\j:num. e:real^N`;
                             `christoffel (G:real^N->real^N^N) y0 (basis i) (basis j)`]
                     LRG_SLOT_EXPAND)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ltensor_field 3 U (lnabla 2 (G:real^N->real^N^N) tf)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`3`; `\j:num. e:real^N`] o CONJUNCT2) THEN
    REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[llap] THEN
  USE_THEN "d2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "d1" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  USE_THEN "ct" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`] THEN
  REWRITE_TAC[ltlap; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN BINOP_TAC THENL
   [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[ARITH]]);;


(* ========================================================================= *)
(* Rough Laplacians of f g (g the metric) and of the 3D                      *)
(* curvature tensor P = (R/2) g - Ric (lpcurv), linearity of ltlap.         *)
(* ========================================================================= *)

(* The rough Laplacian of f g (g the metric tensor) is (llap f) g, and the *)
(* rough Laplacian of P = (R/2) g - Ric is (llap R / 2) g - Lap Ric.         *)

let RFA_TENSOR_FIELD_0 = prove
 (`!U (f:real^N->real). ltensor_field 0 U (\z u. f z)`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`]);;

let RFA_LTPROD_GF = prove
 (`!(G:real^N->real^N^N) (f:real^N->real).
     (\z u. lmetric2 G z u * f z) = ltprod 2 (lmetric2 G) (\z u. f z)`,
  REWRITE_TAC[ltprod; FUN_EQ_THM]);;

let RFA_LNABLA2_GF = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> lnabla 2 G (\z u. lmetric2 G z u * f z) y u =
         lmetric2 G y u * drop(frechet_derivative (\z. lift(f z)) (at y) (u 3))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LTPROD_GF] THEN
  MP_TAC(ISPECL [`2`; `0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`;
                 `\z:real^N u:num->real^N. (f:real^N->real) z`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA_LTPROD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LNABLA_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[lnabla; SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_SUB_RZERO]);;

let RFA_LNABLA3_GH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> lnabla 3 G
           (ltprod 2 (lmetric2 G)
              (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))) y u =
         lmetric2 G y u *
         lnabla 1 G (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1))) y
           (\m. u(m + 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`;
                 `\z:real^N u:num->real^N.
                    drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (u 1))`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LNABLA_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID]);;

let RFA_LTLAP2_GF = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltlap 2 G (\z u. lmetric2 G z u * f z) y u = lmetric2 G y u * llap G f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. lnabla 3 G (lnabla 2 G (\z u. lmetric2 G z u * (f:real^N->real) z)) y v =
        lmetric2 G y v *
        lnabla 1 G (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1))) y
          (\m. v(m + 2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `y:real^N`; `v:num->real^N`] RFA_LNABLA3_GH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `z:real^N`; `w:num->real^N`] RFA_LNABLA2_GF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ltprod] THEN CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ltlap; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
         LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lmetric2 (G:real^N->real^N^N) y
      (\m. if m = 3 then basis a else if m = 4 then basis b else u m) =
    lmetric2 G y u`
  SUBST1_TAC THENL [REWRITE_TAC[lmetric2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 1 (G:real^N->real^N^N)
      (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (u 1))) y
      (\m. if m + 2 = 3 then basis a else if m + 2 = 4 then basis b else u(m + 2)) =
    lnabla 1 G (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1))) y
      (\m. if m = 1 then basis a else basis b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `b:num`; `a:num`] LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_LTLAP_LINCOMB = prove
 (`!k U (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 a b y u.
     metric_field U G /\
     ltensor_field k U tf1 /\ (!u. smooth_map_on U (\y. lift(tf1 y u))) /\
     ltensor_field k U tf2 /\ (!u. smooth_map_on U (\y. lift(tf2 y u))) /\ y IN U
     ==> ltlap k G (\x u. a * tf1 x u + b * tf2 x u) y u =
         a * ltlap k G tf1 y u + b * ltlap k G tf2 y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
                 `a:real`; `b:real`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ltlap] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_LPCURV_LINCOMB = prove
 (`!G:real^N->real^N^N.
     lpcurv G =
     (\z u. &1 * (lmetric2 G z u * (lscalar G z / &2)) + --(&1) * lric2 G z u)`,
  REWRITE_TAC[FUN_EQ_THM; lpcurv] THEN REAL_ARITH_TAC);;

let RFA_HALF_SCALAR_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U (\y. lift(lscalar G y / &2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift(lscalar (G:real^N->real^N^N) y / &2)) =
                (\y. inv(&2) % lift(lscalar G y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[]);;

let RFA_GSCALAR_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (\z u. lmetric2 G z u * (lscalar G z / &2)) /\
         (!u. smooth_map_on U (\y. lift(lmetric2 G y u * (lscalar G y / &2))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `\z:real^N. lscalar (G:real^N->real^N^N) z / &2`]
         RFA_LTPROD_GF) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `0`; `U:real^N->bool`; `lmetric2 (G:real^N->real^N^N)`;
                   `\z:real^N u:num->real^N. lscalar (G:real^N->real^N^N) z / &2`]
           RFA_LTPROD_FIELD) THEN
    ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ADD_CLAUSES];
    GEN_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN
    ASM_SIMP_TAC[RFA_HALF_SCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field]]);;

let RFA_LPCURV_FIELD = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> ltensor_field 2 U (lpcurv G) /\
         (!u. smooth_map_on U (\y. lift(lpcurv G y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RFA_LPCURV_LINCOMB] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_TENSOR_FIELD_LINCOMB THEN
  ASM_SIMP_TAC[RFA_GSCALAR_FIELD; LRG_LRIC2_FIELD; ETA_AX]);;

(* The rough Laplacian of P = (R/2) g - Ric.                                *)

let RFA_LTLAP2_LPCURV = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U
     ==> ltlap 2 G (lpcurv G) y u =
         lmetric2 G y u * (llap G (lscalar G) y / &2) - ltlap 2 G (lric2 G) y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LPCURV_LINCOMB] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z:real^N u:num->real^N. lmetric2 (G:real^N->real^N^N) z u * (lscalar G z / &2)`;
                 `lric2 (G:real^N->real^N^N)`; `&1`; `--(&1)`; `y:real^N`; `u:num->real^N`]
         RFA_LTLAP_LINCOMB) THEN
  ASM_SIMP_TAC[RFA_GSCALAR_FIELD; LRG_LRIC2_FIELD] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z:real^N. lscalar (G:real^N->real^N^N) z / &2`; `y:real^N`; `u:num->real^N`]
         RFA_LTLAP2_GF) THEN
  ASM_SIMP_TAC[RFA_HALF_SCALAR_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(\z. lscalar (G:real^N->real^N^N) z / &2) = (\z. inv(&2) * lscalar G z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lscalar (G:real^N->real^N^N)`;
                 `inv(&2)`; `y:real^N`] RFA_LLAP_CMUL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Smoothness of T(E,E), the shifted tensor Z = P - p1 g, and                *)
(* the Laplacian of the Rayleigh barrier P(E,E)/g(E,E) at a critical point *)
(* (RFA_BARRIER_LAP).                                                        *)
(* ========================================================================= *)

let RFA_EXT_SMOOTH = prove
 (`!U (G:real^N->real^N^N) y0 e.
     metric_field U G /\ y0 IN U
     ==> smooth_map_on U (\y. e - christoffel G y0 (y - y0) e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
         CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[bilinear] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (\h. christoffel (G:real^N->real^N^N) y0 h e)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. e - christoffel (G:real^N->real^N^N) y0 (y - y0) e) =
    (\y. (e + christoffel G y0 y0 e) - christoffel G y0 y e)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB th)]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\x:real^N. x`;
                 `\h:real^N. christoffel (G:real^N->real^N^N) y0 h e`]
         SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF]);;

let RFA_TF2_EVAL_SMOOTH = prove
 (`!U (tf:real^N->(num->real^N)->real) (X:real^N->real^N) Y.
     open U /\ ltensor_field 2 U tf /\ (!u. smooth_map_on U (\y. lift(tf y u))) /\
     smooth_map_on U X /\ smooth_map_on U Y
     ==> smooth_map_on U (\y. lift(tf y (\m. if m = 1 then X y else Y y)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. lift(sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N))
                 (\q. ((Y:real^N->real^N) y)$p * ((X:real^N->real^N) y)$q *
                      (tf:real^N->(num->real^N)->real) y
                        (\m. if m = 1 then basis q else basis p))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_TENSOR2_EXPAND THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]);;

let RFA_TENSOR_FIELD_SUBSET = prove
 (`!k U V (tf:real^N->(num->real^N)->real).
     ltensor_field k U tf /\ V SUBSET U ==> ltensor_field k V tf`,
  REWRITE_TAC[ltensor_field; SUBSET] THEN MESON_TAC[]);;

let RFA_LTLAP2_METRIC = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U ==> ltlap 2 G (lmetric2 G) y u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltlap] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[num_CONV `2`] THEN ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_MUL_RZERO; SUM_0]);;

(* The shifted tensor Z = P - p1 g at an eigenvector e of P (P(v,e) =      *)
(* p1 g(v,e)): a smooth symmetric 2-tensor with Z(y0) e = 0, so            *)
(* llap (Z(E,E)) (y0) = (Lap P)(e,e).                                       *)

let RFA_ZSHIFT_LAP = prove
 (`!U (G:real^N->real^N^N) y0 e p1.
     metric_field U G /\ y0 IN U /\
     (!v. lpcurv G y0 (\m. if m = 1 then v else e) = p1 * (v dot (G y0 ** e)))
     ==> llap G (\z. &1 * lpcurv G z (\m. e - christoffel G y0 (z - y0) e) +
                     --p1 * lmetric2 G z (\m. e - christoffel G y0 (z - y0) e)) y0 =
         ltlap 2 G (lpcurv G) y0 (\m. e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 2 U (\z u. &1 * lpcurv (G:real^N->real^N^N) z u +
                             --p1 * lmetric2 G z u) /\
    (!u. smooth_map_on U (\y. lift(&1 * lpcurv G y u + --p1 * lmetric2 G y u)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_LINCOMB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z u. &1 * lpcurv (G:real^N->real^N^N) z u + --p1 * lmetric2 G z u`;
                 `y0:real^N`; `e:real^N`] RFA_RAYLEIGH_LAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^N`; `v1:real^N`; `v2:real^N`] THEN DISCH_TAC THEN
      REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                     `v1:real^N`; `v2:real^N`] LRICCI_SYM) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                     `v1:real^N`; `v2:real^N`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^N` THEN ASM_REWRITE_TAC[lmetric2] THEN
      REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lpcurv (G:real^N->real^N^N)`; `lmetric2 (G:real^N->real^N^N)`;
                 `&1`; `--p1:real`; `y0:real^N`; `\m:num. e:real^N`]
         RFA_LTLAP_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`;
                 `\m:num. e:real^N`] RFA_LTLAP2_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_EXT_EVAL_SMOOTH = prove
 (`!U W (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y0 e.
     metric_field U G /\ y0 IN U /\ open W /\ W SUBSET U /\
     ltensor_field 2 U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> smooth_map_on W (\y. lift(tf y (\m. e - christoffel G y0 (y - y0) e)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                 `\y. e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`;
                 `\y. e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`]
         RFA_TF2_EVAL_SMOOTH) THEN
  REWRITE_TAC[COND_ID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_TENSOR_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXT_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* The Rayleigh barrier phi = P(E,E) / g(E,E) at a critical point y0 where *)
(* e is a g-unit eigenvector of P = lpcurv G with eigenvalue p1:            *)
(* llap phi (y0) = (Lap P)(e,e).                                            *)

let RFA_BARRIER_LAP = prove
 (`!U (G:real^N->real^N^N) W y0 e p1 (phi:real^N->real).
     metric_field U G /\ y0 IN U /\ open W /\ y0 IN W /\ W SUBSET U /\
     e dot (G y0 ** e) = &1 /\
     (!v. lpcurv G y0 (\m. if m = 1 then v else e) = p1 * (v dot (G y0 ** e))) /\
     (!y. y IN W ==> ~(e - christoffel G y0 (y - y0) e = vec 0)) /\
     (!y. y IN W
          ==> phi y = lpcurv G y (\m. e - christoffel G y0 (y - y0) e) /
                      lmetric2 G y (\m. e - christoffel G y0 (y - y0) e)) /\
     ((\y. lift(phi y)) has_derivative (\v. vec 0)) (at y0)
     ==> llap G phi y0 = ltlap 2 G (lpcurv G) y0 (\m. e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (G:real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`;
                 `p1:real`] RFA_ZSHIFT_LAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lpcurv (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN W
        ==> &0 < lmetric2 (G:real^N->real^N^N) y
                   (\m. e - christoffel G y0 (y - y0) e)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\y. lift((phi:real^N->real) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\y. lift(drop(lift(lpcurv (G:real^N->real^N^N) y
                           (\m. e - christoffel G y0 (y - y0) e))) /
               drop(lift(lmetric2 G y (\m. e - christoffel G y0 (y - y0) e))))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real) y0 = p1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `e:real^N` (ASSUME
     `!v. lpcurv (G:real^N->real^N^N) y0 (\m. if m = 1 then v else e) =
          p1 * (v dot (G y0 ** e))`)) THEN
    REWRITE_TAC[COND_ID; lmetric2] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `llap (G:real^N->real^N^N)
                (\z. ((phi:real^N->real) z - p1) *
                     lmetric2 G z (\m. e - christoffel G y0 (z - y0) e)) y0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `&0 < lmetric2 (G:real^N->real^N^N) z (\m. e - christoffel G y0 (z - y0) e)`
    MP_TAC THENL [ASM_SIMP_TAC[]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`W:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. (phi:real^N->real) z - p1`;
     `\z. lmetric2 (G:real^N->real^N^N) z (\m. e - christoffel G y0 (z - y0) e)`;
     `y0:real^N`] RFA_LLAP_MUL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `frechet_derivative (\z. lift((phi:real^N->real) z - p1)) (at y0) =
                (\v. vec 0)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_SUB] THEN
    SUBGOAL_THEN `(\v:real^N. vec 0:real^1) = (\v. vec 0 - vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfa_lginner; rfa_d1; DROP_VEC; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  SUM_0; REAL_ADD_RID] THEN
  REWRITE_TAC[lmetric2] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  MP_TAC(BETA_RULE(ISPECL [`W:real^N->bool`; `G:real^N->real^N^N`; `phi:real^N->real`;
                           `\z:real^N. p1:real`; `y0:real^N`] RFA_LLAP_SUB)) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST; REAL_SUB_RZERO]);;

