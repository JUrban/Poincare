(* ========================================================================= *)
(* Unit pc_p2c_cdiff (Part 2C): the covariant perturbation calculus used by  *)
(* pc_p2c_cderiv, on a closure that contains no pc_p3_iface, pc_p2c_iface or *)
(* Part 2B unit, so that the geometry units can load it.                     *)
(*                                                                           *)
(* Contents: lbilin_on operations and their covariant derivatives; the       *)
(* difference tensors p2c_hd (metric), p2c_af (connections, lowered),        *)
(* p2c_bh, the insertion operation p2c_ins; the connection difference        *)
(* P2C_CONN_DIFF; iterated insertions p2c_kt, P2C_KT_ITER, P2C_KT_NORM;      *)
(* bounds for af with two derivatives by absorption, P2C_AF_BOUNDS; the      *)
(* split Rm(G) - Rm(G0) = P + Q + H and its bounds with two derivatives,     *)
(* P2C_RMD_SPLIT, P2C_RMD_BOUNDS; nabla_G Rm(G) and nabla_G^2 Rm(G) for      *)
(* parallel Rm(G0), P2C_DRM_BOUNDS; norms of the gradient and Hessian of the *)
(* scalar curvature by traces, P2C_LGRAD2_LTNORM2, P2C_DSCALAR, P2C_HSCALAR, *)
(* P2C_SCALAR_DERIV_TRACE; metric comparison and the Ricci bounds            *)
(* P2C_RIC_DIFF_NORM, P2C_RIC_NORM_BOUND.  Built on the S . T calculus of    *)
(* pc_rfa_talg and pc_rfa_ricid and on pc_lrg_stab.                          *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_rfa_talg.ml";;
needs "src/pc_rfa_ricid.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/ns_smooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic consequences of the class lbilin_on of pc_rfa_ricid               *)
(* (bilinear contraction operations S * T): smoothness, the Leibniz rule and *)
(* norm bounds for first and second covariant derivatives.                   *)
(* ------------------------------------------------------------------------- *)

let P2C_LTENSOR_FIELD_EQ = prove
 (`!k U (tf:real^N->(num->real^N)->real) tg.
     ltensor_field k U tg /\ (!y u. y IN U ==> tf y u = tg y u)
     ==> ltensor_field k U tf`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltensor_field] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(tf:real^N->(num->real^N)->real) y = tg y` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ASM_MESON_TAC[]]);;

let P2C_LBILIN_ON_SMOOTH = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q E
     ==> !U G tf tg. metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
                     (!u. smooth_map_on U (\y. lift(tf y u))) /\
                     (!u. smooth_map_on U (\y. lift(tg y u)))
                     ==> ltensor_field k U (E G tf tg) /\
                         !u. smooth_map_on U (\y. lift(E G tf tg y u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` STRIP_ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_LTENSOR_FIELD_EQ THEN EXISTS_TAC `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`; `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`] RFA_LBILIN_TENSOR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. lift((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg y u)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`; `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`] RFA_LBILIN_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let P2C_LBILIN_ON_NABLA = prove
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
  DISCH_THEN(X_CHOOSE_THEN `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
             STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `p:num`; `q:num`;
                 `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                    (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
                RFA_LBILIN_NABLA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
     STRIP_ASSUME_TAC)) THEN
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
  TRANS_TAC EQ_TRANS
   `lnabla k (G:real^N->real^N^N)
      ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[metric_field];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 6)) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P2C_ARITH_2SUM = prove
 (`!x y a b C1 C2. x <= C1 * a /\ y <= C2 * b /\ &0 <= C1 /\ &0 <= C2 /\ &0 <= a /\ &0 <= b
                   ==> &2 * x + &2 * y <= (&2 * (C1 + C2)) * (a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C1 * b /\ &0 <= C2 * a` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_LBILIN_ON_DNORM = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q E
     ==> ?C. &0 <= C /\
           !U G tf tg y.
              metric_field U G /\ y IN U /\
              ltensor_field p U tf /\ ltensor_field q U tg /\
              (!u. smooth_map_on U (\y. lift(tf y u))) /\
              (!u. smooth_map_on U (\y. lift(tg y u)))
              ==> ltnorm2 (k + 1) G (lnabla k G (E G tf tg)) y <=
                  C * (ltnorm2 (p + 1) G (lnabla p G tf) y * ltnorm2 q G tg y +
                       ltnorm2 p G tf y * ltnorm2 (q + 1) G (lnabla q G tg) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2C_LBILIN_ON_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "l1") (CONJUNCTS_THEN2 (LABEL_TAC "l2") ASSUME_TAC)))) THEN
  USE_THEN "l1" (X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC o MATCH_MP RFA_LBILIN_ON_NORM) THEN
  USE_THEN "l2" (X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC o MATCH_MP RFA_LBILIN_ON_NORM) THEN
  EXISTS_TAC `&2 * (C1 + C2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tg:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 (k + 1) (G:real^N->real^N^N)
      (lnabla k G ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                     (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg)) y =
    ltnorm2 (k + 1) G
      (\z u. (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                 (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
               G (lnabla p G tf) tg z u +
             (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                 (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
               G tf (lnabla q G tg) z u) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 6)) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * ltnorm2 (k + 1) (G:real^N->real^N^N)
           ((E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
              G (lnabla p G tf) tg) y +
    &2 * ltnorm2 (k + 1) G
           ((E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
              G tf (lnabla q G tg)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "l1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `lnabla p (G:real^N->real^N^N) tf`; `tg:real^N->(num->real^N)->real`] o
        MATCH_MP P2C_LBILIN_ON_SMOOTH);
      USE_THEN "l2" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                     `tf:real^N->(num->real^N)->real`; `lnabla q (G:real^N->real^N^N) tg`] o
        MATCH_MP P2C_LBILIN_ON_SMOOTH)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_ARITH_2SUM THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 5)) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 5)) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The algebra of the second-derivative bound. *)

let P2C_ARITH_3SUM = prove
 (`!X1 X2 x1 x2 x3 D1 D2.
     X1 <= D1 * (x1 + x2) /\ X2 <= D2 * (x2 + x3) /\ &0 <= D1 /\ &0 <= D2 /\
     &0 <= x1 /\ &0 <= x2 /\ &0 <= x3
     ==> &2 * X1 + &2 * X2 <= (&2 * (D1 + D2)) * (x1 + x2 + x3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= D1 * x3 /\ &0 <= D2 * x1` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_LBILIN_ON_D2NORM = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q E
     ==> ?C. &0 <= C /\
           !U G tf tg y.
              metric_field U G /\ y IN U /\
              ltensor_field p U tf /\ ltensor_field q U tg /\
              (!u. smooth_map_on U (\y. lift(tf y u))) /\
              (!u. smooth_map_on U (\y. lift(tg y u)))
              ==> ltnorm2 (k + 2) G (lnabla (k + 1) G (lnabla k G (E G tf tg))) y <=
                  C * (ltnorm2 (p + 2) G (lnabla (p + 1) G (lnabla p G tf)) y *
                       ltnorm2 q G tg y +
                       ltnorm2 (p + 1) G (lnabla p G tf) y *
                       ltnorm2 (q + 1) G (lnabla q G tg) y +
                       ltnorm2 p G tf y *
                       ltnorm2 (q + 2) G (lnabla (q + 1) G (lnabla q G tg)) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2C_LBILIN_ON_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "l1") (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "id"))))) THEN
  USE_THEN "l1" (X_CHOOSE_THEN `D1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1")) o
                 MATCH_MP P2C_LBILIN_ON_DNORM) THEN
  USE_THEN "l2" (X_CHOOSE_THEN `D2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2")) o
                 MATCH_MP P2C_LBILIN_ON_DNORM) THEN
  EXISTS_TAC `&2 * (D1 + D2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`;
                       `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tg:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla p (G:real^N->real^N^N) tf`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(p + 1) + 1 = p + 2`] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`q + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla q (G:real^N->real^N^N) tg`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(q + 1) + 1 = q + 2`] THEN STRIP_TAC] THEN
  USE_THEN "l1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                    `lnabla p (G:real^N->real^N^N) tf`; `tg:real^N->(num->real^N)->real`] o
                 MATCH_MP P2C_LBILIN_ON_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "l2" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                    `tf:real^N->(num->real^N)->real`; `lnabla q (G:real^N->real^N^N) tg`] o
                 MATCH_MP P2C_LBILIN_ON_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `(E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `(E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg)`] LNABLA_TENSOR_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!z u. z IN U
          ==> lnabla k G ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg) z u =
              (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg z u + (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "id" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. lnabla (k + 1) G (lnabla k G ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg)) y u =
        lnabla (k + 1) G ((E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg) y u +
        lnabla (k + 1) G ((E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg)) y u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num->real^N` THEN
    TRANS_TAC EQ_TRANS
     `lnabla (k + 1) (G:real^N->real^N^N)
        (\z w. (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg z w + (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg) z w) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LRG_LNABLA_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 (k + 2) (G:real^N->real^N^N) (lnabla (k + 1) G (lnabla k G ((E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg))) y =
    ltnorm2 (k + 2) G
      (\z w. lnabla (k + 1) G ((E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg) z w +
             lnabla (k + 1) G ((E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg)) z w) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ltnorm2 (k + 2) (G:real^N->real^N^N)
                     (lnabla (k + 1) G ((E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G (lnabla p G tf) tg)) y +
              &2 * ltnorm2 (k + 2) G (lnabla (k + 1) G ((E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf (lnabla q G tg))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_ARITH_3SUM THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "d1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                   `lnabla p (G:real^N->real^N^N) tf`;
                                   `tg:real^N->(num->real^N)->real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`]];
    USE_THEN "d2" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                   `tf:real^N->(num->real^N)->real`;
                                   `lnabla q (G:real^N->real^N^N) tg`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`]];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The difference tensors of two metrics G0, G (h = G - G0 and               *)
(* the difference of the connections lowered by G0) and the contraction     *)
(* operations used below, as members of lbilin_on (built from ltprod,       *)
(* contractions of two slots, rfa_ins, and slot permutations).              *)
(* ------------------------------------------------------------------------- *)

let p2c_hd = new_definition
 `p2c_hd (G0:real^N->real^N^N) (G:real^N->real^N^N) =
    (\z u. lmetric2 G z u - lmetric2 G0 z u)`;;

let p2c_af = new_definition
 `p2c_af (G0:real^N->real^N^N) (G:real^N->real^N^N) =
    (\z u. u 3 dot (G0 z ** (christoffel G z (u 1) (u 2) - christoffel G0 z (u 1) (u 2))))`;;

(* sum_ab g^ab tf(u3,e_a) tg(u1,u2,e_b): for tf = h, tg = af, G = G0 this is *)
(* h(u3, A(u1,u2)), A the difference of the connections.                     *)

let p2c_bh = new_definition
 `p2c_bh (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
         (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 3 else basis a) *
            tg y (\m. if m = 1 then u 1 else if m = 2 then u 2 else basis b)))`;;

let P2C_TF_ARGS = prove
 (`!k U (tf:real^N->(num->real^N)->real) y w w'.
     ltensor_field k U tf /\ y IN U /\ (!m. 1 <= m /\ m <= k ==> w m = w' m)
     ==> tf y w = tf y w'`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

let P2C_PERM_312 = prove
 (`(\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m) permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 3 then 1 else if m = 1 then 2 else if m = 2 then 3 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_NUM_EVAL_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT(CHANGED_TAC(CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]));;

let P2C_BH_LBILIN = prove
 (`lbilin_on 3 2 3
     (p2c_bh:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(ISPECL [`3`; `2`; `3`; `2`; `5`;
                 `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real). ltprod 2 tf tg`]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`2`; `3`] (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ P2C_PERM_312) THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_bh; ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_TF_ARGS THENL
   [MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`];
    MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[rfa_ins] THEN P2C_NUM_EVAL_TAC);;

(* sum_ab g^ab tf(u1,u4,e_a) tg(u2,u3,e_b) (= A(u1,u4).G0 A(u2,u3) for      *)
(* tf = tg = af), sum_ab g^ab tf(u3,e_a) tg(u1,u2,e_b,u4) (= h(u3, Rm0(u1,u2)u4) *)
(* for tf = h, tg = lrm4 G0) and the double contraction                    *)
(* h(A(u1,u4), A(u2,u3)) for tf = h, tg = ltprod 3 af af.                    *)

let p2c_bq0 = new_definition
 `p2c_bq0 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 1 else if m = 2 then u 4 else basis a) *
            tg y (\m. if m = 1 then u 2 else if m = 2 then u 3 else basis b)))`;;

let p2c_bh4 = new_definition
 `p2c_bh4 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            tf y (\m. if m = 1 then u 3 else basis a) *
            tg y (\m. if m = 1 then u 1 else if m = 2 then u 2 else if m = 3 then basis b
                      else u 4)))`;;

let p2c_bq1 = new_definition
 `p2c_bq1 (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv(G y)$a$b *
            sum(1..dimindex(:N))
             (\c. sum(1..dimindex(:N))
               (\d. matrix_inv(G y)$c$d *
                    tf y (\m. if m = 1 then basis c else basis a) *
                    tg y (\m. if m = 1 then u 1 else if m = 2 then u 4 else if m = 3 then basis d
                              else if m = 4 then u 2 else if m = 5 then u 3 else basis b)))))`;;

let P2C_PERM_1423 = prove
 (`(\m. if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 4 then 2 else if m = 2 then 3 else if m = 3 then 4 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_PERM_3124 = prove
 (`(\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 3 then 1 else if m = 1 then 2 else if m = 2 then 3 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_SLOT_CASES_TAC n =
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (if n = 2 then `m = 1 \/ m = 2`
                else if n = 3 then `m = 1 \/ m = 2 \/ m = 3`
                else if n = 4 then `m = 1 \/ m = 2 \/ m = 3 \/ m = 4`
                else `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6`)
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[rfa_ins] THEN P2C_NUM_EVAL_TAC;;

let P2C_BQ0_LBILIN = prove
 (`lbilin_on 4 3 3
     (p2c_bq0:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(ISPECL [`4`; `3`; `3`; `3`; `6`;
                 `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real). ltprod 3 tf tg`]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`3`; `3`] (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ P2C_PERM_1423) THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_bq0; ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_TF_ARGS THEN MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN P2C_SLOT_CASES_TAC 3);;

let P2C_BH4_LBILIN = prove
 (`lbilin_on 4 2 4
     (p2c_bh4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(ISPECL [`4`; `2`; `4`; `2`; `5`;
                 `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real). ltprod 2 tf tg`]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`2`; `4`] (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ P2C_PERM_3124) THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_bh4; ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_TF_ARGS THENL
   [MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    P2C_SLOT_CASES_TAC 2;
    MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    P2C_SLOT_CASES_TAC 4]);;

let P2C_BQ1_LBILIN = prove
 (`lbilin_on 4 2 6
     (p2c_bq1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(ISPECL [`6`; `2`; `6`; `1`; `5`;
                 `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real). ltprod 2 tf tg`]
                RFA_LBILIN_ON_CTR_AT) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`2`; `6`] (INST_TYPE [`:N`,`:N`] RFA_LBILIN_ON_PROD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th0 -> let th = BETA_RULE th0 in
             MP_TAC(ISPECL [`4`; `2`; `6`; `1`; `6`; rand(concl th)]
                           RFA_LBILIN_ON_CTR_AT) THEN ASSUME_TAC th) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ P2C_PERM_1423) THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_bq1; ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2C_TF_ARGS THENL
   [MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    P2C_SLOT_CASES_TAC 2;
    MAP_EVERY EXISTS_TAC [`6`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    P2C_SLOT_CASES_TAC 6]);;

(* The insertion of the difference tensor A into the slots of a k-tensor:   *)
(* for tf = X, tg = af, G = G0 this is sum_i X(.., A(u(k+1), u i), ..).     *)

let p2c_ins = new_definition
 `p2c_ins k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..k)
     (\i. sum(1..dimindex(:N))
       (\a. sum(1..dimindex(:N))
         (\b. matrix_inv(G y)$a$b *
              tf y (\m. if m = i then basis a else u m) *
              tg y (\m. if m = 1 then u(k + 1) else if m = 2 then u i else basis b))))`;;

let P2C_INS_PERMUTES = prove
 (`!i k. 1 <= i /\ i <= k
         ==> (\m. if m < i then m else if m < k then m + 1 else if m = k then k + 1
                  else if m = k + 1 then i else m) permutes 1..(k + 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m < i then m else if m = i then k + 1 else if m <= k then m - 1
                  else if m = k + 1 then k else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let P2C_INS_LBILIN = prove
 (`!k. 1 <= k
       ==> lbilin_on (k + 1) k 3
             (p2c_ins k:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= k
        ==> lbilin_on (k + 1) k 3
              (\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                (tg:real^N->(num->real^N)->real) y u.
                 sum(1..dimindex(:N))
                  (\a. sum(1..dimindex(:N))
                    (\b. matrix_inv(G y)$a$b *
                         tf y (\m. if m = i then basis a else u m) *
                         tg y (\m. if m = 1 then u(k + 1) else if m = 2 then u i
                                   else basis b))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k + 1`; `k:num`; `3`; `i:num`; `k + 3`;
                   `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                     (tg:real^N->(num->real^N)->real). ltprod k tf tg`]
                  RFA_LBILIN_ON_CTR_AT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(k + 1) + 2 = k + 3`] THEN
      REWRITE_TAC[REWRITE_RULE[] (ISPECL [`k:num`; `3`] (INST_TYPE [`:N`,`:N`]
                                  RFA_LBILIN_ON_PROD))] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_PERM o C CONJ
      (MATCH_MP P2C_INS_PERMUTES (CONJ (ASSUME `1 <= i`) (ASSUME `i <= k:num`)))) THEN
    DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                         `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`;
                         `y:real^N`; `u:num->real^N`] THEN
    STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2C_TF_ARGS THENL
     [MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`]] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[rfa_ins] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST [AP_TERM_TAC THEN ASM_ARITH_TAC;
           MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`k + 1`; `k:num`; `3`; `k:num`;
    `\i (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
       (tg:real^N->(num->real^N)->real) y u.
        sum(1..dimindex(:N))
         (\a. sum(1..dimindex(:N))
           (\b. matrix_inv(G y)$a$b *
                tf y (\m. if m = i then basis a else u m) *
                tg y (\m. if m = 1 then u(k + 1) else if m = 2 then u i else basis b)))`]
    RFA_LBILIN_ON_SUM)) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; p2c_ins]);;

(* ------------------------------------------------------------------------- *)
(* The basic identities.  af is a smooth tensor field; the                  *)
(* difference A of the connections is G0^-1 af; the G-lowered difference K *)
(* (LRG_CHRISTOFFEL_DIFF_K) is af + h(., A); the connection of G is that of  *)
(* G0 minus the insertion of A.                                              *)
(* ------------------------------------------------------------------------- *)

let P2C_HD_FIELD = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> ltensor_field 2 s (p2c_hd G0 G) /\
         (!u. smooth_map_on s (\y. lift(p2c_hd G0 G y u)))`,
  REWRITE_TAC[p2c_hd] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LMETRIC2_DIFF_FIELD) THEN REWRITE_TAC[]);;

let P2C_AF_FIELD = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> ltensor_field 3 s (p2c_af G0 G) /\
         (!u. smooth_map_on s (\y. lift(p2c_af G0 G y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool) /\
                smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o G0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN
    REWRITE_TAC[metric_field] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[p2c_af] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST] THEN MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ltensor_field; p2c_af] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a0") (LABEL_TAC "b0")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "b1")) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2 /\ u 3 = u' 3`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
   [SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot ((G0:real^N->real^N^N) y **
              (christoffel (G:real^N->real^N^N) y v (u 2) - christoffel G0 y v (u 2))))) =
      (\v. (\x. lift(u 3 dot (G0 y ** x)))
             ((\v. christoffel G y v (u 2) - christoffel G0 y v (u 2)) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    USE_THEN "b1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "b0" (fun th -> REWRITE_TAC[th]);
    SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot ((G0:real^N->real^N^N) y **
              (christoffel (G:real^N->real^N^N) y (u 1) v - christoffel G0 y (u 1) v)))) =
      (\v. (\x. lift(u 3 dot (G0 y ** x)))
             ((\v. christoffel G y (u 1) v - christoffel G0 y (u 1) v) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "a1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "a0" (fun th -> REWRITE_TAC[th]);
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT]]);;

let P2C_AF_RAISE = prove
 (`!s (G0:real^N->real^N^N) G z v w.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> christoffel G z v w - christoffel G0 z v w =
         matrix_inv(G0 z) **
         (lambda c. p2c_af G0 G z (\m. if m = 1 then v else if m = 2 then w else basis c))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_af] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((lambda c. basis c dot ((G0:real^N->real^N^N) z **
        (christoffel (G:real^N->real^N^N) z v w - christoffel G0 z v w))):real^N) =
    G0 z ** (christoffel G z v w - christoffel G0 z v w)`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; DOT_BASIS]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `invertible((G0:real^N->real^N^N) z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID]]);;

(* The G-lowered difference K = af + h(u3, A(u1,u2)). *)

let P2C_K_RELATION = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> u 3 dot (G z ** (christoffel G z (u 1) (u 2) - christoffel G0 z (u 1) (u 2))) =
         p2c_af G0 G z u + p2c_bh G0 (p2c_hd G0 G) (p2c_af G0 G) z u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `X:real^N = christoffel G z (u 1) (u 2) - christoffel G0 z (u 1) (u 2)` THEN
  SUBGOAL_THEN `(u:num->real^N) 3 dot ((G:real^N->real^N^N) z ** X) =
                u 3 dot ((G0:real^N->real^N^N) z ** X) +
                p2c_hd G0 G z (\m. if m = 1 then u 3 else X)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2c_hd; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`; `p2c_hd G0 (G:real^N->real^N^N)`;
                 `z:real^N`; `2`; `\m. if m = 1 then (u:num->real^N) 3 else X`; `X:real^N`]
                RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(\m. if m = 2 then X else if m = 1 then (u:num->real^N) 3 else X) =
                (\m. if m = 1 then u 3 else X)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p2c_af G0 G z u = (u:num->real^N) 3 dot ((G0:real^N->real^N^N) z ** X)`
  SUBST1_TAC THENL [EXPAND_TAC "X" THEN REWRITE_TAC[p2c_af]; ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[p2c_bh] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `matrix_inv((G0:real^N->real^N^N) z)$b$a = matrix_inv(G0 z)$a$b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `basis b dot ((G0:real^N->real^N^N) z ** X) =
    p2c_af G0 G z (\m. if m = 1 then (u:num->real^N) 1 else if m = 2 then u 2 else basis b)`
  SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[p2c_af] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_hd G0 (G:real^N->real^N^N) z (\m. if m = 2 then basis a else if m = 1 then u 3 else X) =
    p2c_hd G0 G z (\m. if m = 1 then (u:num->real^N) 3 else basis a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2C_TF_ARGS THEN MAP_EVERY EXISTS_TAC [`2`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    TRY ASM_ARITH_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* nabla_G X = nabla_G0 X - (A inserted into the slots of X). *)

let P2C_CONN_DIFF = prove
 (`!k s (G0:real^N->real^N^N) G X z u.
     metric_field s G0 /\ metric_field s G /\ ltensor_field k s X /\ z IN s
     ==> lnabla k G X z u = lnabla k G0 X z u - p2c_ins k G0 X (p2c_af G0 G) z u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; p2c_ins] THEN
  MATCH_MP_TAC(REAL_ARITH `sg - s0 = t ==> d - sg = (d - s0) - t`) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `linear (\v. lift((X:real^N->(num->real^N)->real) z
                       (\j. if j = i then v else (u:num->real^N) j)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ltensor_field k s (X:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_SUB) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`christoffel (G:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i)`;
    `christoffel (G0:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i)`]) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM LIFT_SUB; LIFT_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `z:real^N`; `i:num`; `u:num->real^N`;
                 `christoffel (G:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i) -
                  christoffel (G0:real^N->real^N^N) z (u(k + 1)) (u i)`]
                RFA_METRIC_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `matrix_inv((G0:real^N->real^N^N) z)$b$a = matrix_inv(G0 z)$a$b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `basis b dot ((G0:real^N->real^N^N) z **
      (christoffel (G:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i) -
       christoffel G0 z (u(k + 1)) (u i))) =
    p2c_af G0 G z (\m. if m = 1 then (u:num->real^N)(k + 1) else if m = 2 then u i
                       else basis b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2c_af] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The G-lowered difference tensor K of LRG_CHRISTOFFEL_DIFF_K,              *)
(* its iterated covariant derivatives (permutations of those of h) and their *)
(* norms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p2c_kt = new_definition
 `p2c_kt (G0:real^N->real^N^N) (G:real^N->real^N^N) =
    (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) - christoffel G0 z (u 1) (u 2))))`;;

let P2C_SWAPS_PERMUTE = prove
 (`!n. 3 <= n
       ==> (swap(1,2) o swap(2,3)) permutes 1..n /\ swap(2,3) permutes 1..n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..3 /\ (swap(1,2) o swap(2,3)) permutes 1..3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC PERMUTES_COMPOSE THEN CONJ_TAC] THEN
    MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC `1..3` THEN
  ASM_REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let P2C_KT_ITER = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> !j z u. z IN s
           ==> lnabla_iter 3 j G0 (p2c_kt G0 G) z u =
               inv(&2) *
               (lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z (\m. u((swap(1,2) o swap(2,3)) m)) +
                lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z (\m. u(swap(2,3) m)) -
                lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it") THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; LRG_LNABLA_ITER_12] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; LRG_LNABLA_ITER_12] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_kt; p2c_hd] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF_K THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Y = lnabla_iter 2 (j + 1) (G0:real^N->real^N^N) (p2c_hd G0 G)` THEN
  SUBGOAL_THEN `!u. smooth_map_on s (\x. lift((Y:real^N->(num->real^N)->real) x u))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN USE_THEN "it" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `j + 1` th)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!u x. x IN s ==> (\x. lift((Y:real^N->(num->real^N)->real) x u))
                                  differentiable at x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(swap(1,2) o swap(2,3)) permutes 1..(3 + j) /\ swap(2,3) permutes 1..(3 + j)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_SWAPS_PERMUTE THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lnabla_iter] THEN
  TRANS_TAC EQ_TRANS
   `lnabla (3 + j) (G0:real^N->real^N^N)
      (\z u. inv(&2) * ((Y:real^N->(num->real^N)->real) z (\m. u((swap(1,2) o swap(2,3)) m)) +
                        Y z (\m. u(swap(2,3) m)) - Y z u)) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lnabla_iter 2 (SUC j + 1) (G0:real^N->real^N^N) (p2c_hd G0 G) =
                lnabla (3 + j) G0 (Y:real^N->(num->real^N)->real)`
  SUBST1_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[ARITH_RULE `SUC j + 1 = SUC(j + 1)`; lnabla_iter] THEN
    REWRITE_TAC[ARITH_RULE `2 + j + 1 = 3 + j`];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`3 + j`; `G0:real^N->real^N^N`;
    `\z u. ((Y:real^N->(num->real^N)->real) z (\m. u((swap(1,2) o swap(2,3)) m)) +
            Y z (\m. u(swap(2,3) m)) - Y z u)`; `inv(&2)`; `z:real^N`; `u:num->real^N`]
    LRG_LNABLA_CMUL)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_ADD] THEN MATCH_MP_TAC DIFFERENTIABLE_ADD THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC DIFFERENTIABLE_SUB THEN CONJ_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`3 + j`; `G0:real^N->real^N^N`;
    `\z u. (Y:real^N->(num->real^N)->real) z (\m. u((swap(1,2) o swap(2,3)) m))`;
    `\z u. (Y:real^N->(num->real^N)->real) z (\m. u(swap(2,3) m)) - Y z u`;
    `z:real^N`; `u:num->real^N`] LRG_LNABLA_ADD)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC DIFFERENTIABLE_SUB THEN CONJ_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`3 + j`; `G0:real^N->real^N^N`;
    `\z u. (Y:real^N->(num->real^N)->real) z (\m. u(swap(2,3) m))`;
    `Y:real^N->(num->real^N)->real`; `z:real^N`; `u:num->real^N`] LRG_LNABLA_SUB)) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`3 + j`; `G0:real^N->real^N^N`; `Y:real^N->(num->real^N)->real`;
                 `swap(1,2) o swap(2,3)`; `z:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  MP_TAC(ISPECL [`3 + j`; `G0:real^N->real^N^N`; `Y:real^N->(num->real^N)->real`;
                 `swap(2,3)`; `z:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

(* A real linear combination bound for norms of permuted copies. *)

let P2C_LTNORM2_KCOMB = prove
 (`!k U (G:real^N->real^N^N) (Y:real^N->(num->real^N)->real) s1 s2 y.
     metric_field U G /\ ltensor_field k U Y /\ y IN U /\
     s1 permutes 1..k /\ s2 permutes 1..k
     ==> ltnorm2 k G (\z u. inv(&2) * (Y z (\m. u((s1:num->num) m)) + Y z (\m. u((s2:num->num) m)) - Y z u)) y
         <= &3 * ltnorm2 k G Y y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field k U (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m))) /\
                ltensor_field k U (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s2:num->num) m))) /\
                ltensor_field k U (\z u. --(&1) * (Y:real^N->(num->real^N)->real) z u)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_TENSOR_FIELD_PERMUTE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_TENSOR_FIELD_PERMUTE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 k (G:real^N->real^N^N)
      (\z u. inv(&2) * ((Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m)) +
                        Y z (\m. u((s2:num->num) m)) - Y z u)) y =
    inv(&2) pow 2 *
    ltnorm2 k G (\z u. (\z u. Y z (\m. u((s1:num->num) m))) z u +
                       (\z u. (\z u. Y z (\m. u((s2:num->num) m))) z u +
                              (\z u. --(&1) * Y z u) z u) z u) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LRG_LTNORM2_CMUL] THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 k (G:real^N->real^N^N) (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m))) y =
    ltnorm2 k G Y y /\
    ltnorm2 k G (\z u. Y z (\m. u((s2:num->num) m))) y = ltnorm2 k G Y y /\
    ltnorm2 k G (\z u. --(&1) * Y z u) y = ltnorm2 k G Y y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `s1:num->num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `Y:real^N->(num->real^N)->real`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
      ASM_REWRITE_TAC[ltperm];
      MP_TAC(ISPECL [`k:num`; `s2:num->num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `Y:real^N->(num->real^N)->real`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
      ASM_REWRITE_TAC[ltperm];
      REWRITE_TAC[LRG_LTNORM2_CMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s2:num->num) m))`;
                 `\z u. --(&1) * (Y:real^N->(num->real^N)->real) z u`; `y:real^N`]
                RFA_LTNORM2_ADD_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m))`;
                 `\z u. (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s2:num->num) m))) z u +
                        (\z u. --(&1) * Y z u) z u`; `y:real^N`]
                RFA_LTNORM2_ADD_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 k (G:real^N->real^N^N) Y y` MP_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nY = ltnorm2 k (G:real^N->real^N^N) Y y` THEN
  ABBREV_TAC `n23 = ltnorm2 k (G:real^N->real^N^N)
                      (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s2:num->num) m)) +
                             --(&1) * Y z u) y` THEN
  ABBREV_TAC `nall = ltnorm2 k (G:real^N->real^N^N)
                      (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m)) +
                             Y z (\m. u((s2:num->num) m)) + --(&1) * Y z u) y` THEN
  REWRITE_TAC[REAL_INV_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2C_KT_NORM = prove
 (`!s (G0:real^N->real^N^N) G j y.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> ltnorm2 (3 + j) G0 (lnabla_iter 3 j G0 (p2c_kt G0 G)) y <=
         &3 * ltnorm2 (3 + j) G0 (lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G)) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_ITER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j + 1`) THEN
  REWRITE_TAC[ARITH_RULE `2 + j + 1 = 3 + j`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `3 + j` P2C_SWAPS_PERMUTE) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ltnorm2 (3 + j) (G0:real^N->real^N^N)
      (\z u. inv(&2) *
             (lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z (\m. u((swap(1,2) o swap(2,3)) m)) +
              lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z (\m. u(swap(2,3) m)) -
              lnabla_iter 2 (j + 1) G0 (p2c_hd G0 G) z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2C_LTNORM2_KCOMB THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* af, nabla af and nabla^2 af are bounded by the C^3 distance               *)
(* of G from G0 (from af = K - h(., A) by absorption, K being permutations of *)
(* nabla h).                                                                 *)
(* ------------------------------------------------------------------------- *)

let P2C_LTNORM2_SUB_LE = prove
 (`!k U (G:real^N->real^N^N) (f:real^N->(num->real^N)->real) g y.
     metric_field U G /\ ltensor_field k U f /\ ltensor_field k U g /\ y IN U
     ==> ltnorm2 k G (\y u. f y u - g y u) y <=
         &2 * ltnorm2 k G f y + &2 * ltnorm2 k G g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `f:real^N->(num->real^N)->real`;
                 `\y u. --(&1) * (g:real^N->(num->real^N)->real) y u`; `y:real^N`]
                RFA_LTNORM2_ADD_LE) THEN
  ASM_SIMP_TAC[RFA_TENSOR_FIELD_CMUL; LRG_LTNORM2_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let P2C_KT_FIELD = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> ltensor_field 3 s (p2c_kt G0 G) /\
         (!u. smooth_map_on s (\y. lift(p2c_kt G0 G y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BH_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y u. y IN s
                      ==> p2c_kt (G0:real^N->real^N^N) G y u =
                          p2c_af G0 G y u + p2c_bh G0 (p2c_hd G0 G) (p2c_af G0 G) y u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_kt] THEN MATCH_MP_TAC P2C_K_RELATION THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2C_LTENSOR_FIELD_EQ THEN
    EXISTS_TAC `\y u. p2c_af G0 (G:real^N->real^N^N) y u +
                      p2c_bh G0 (p2c_hd G0 G) (p2c_af G0 G) y u` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. lift(p2c_af G0 (G:real^N->real^N^N) y u) +
                    lift(p2c_bh G0 (p2c_hd G0 G) (p2c_af G0 G) y u)` THEN
    ASM_SIMP_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN
    SIMP_TAC[metric_field]]);;

(* Products of nonnegative quantities under bounds. *)

let P2C_PROD_LE = prove
 (`!a b x y. &0 <= a /\ &0 <= b /\ a <= x /\ b <= y ==> a * b <= x * y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let P2C_ABSORB = prove
 (`!A K c. &0 <= A /\ &0 <= c /\ c <= &1 / &2 /\ A <= K + c * A ==> A <= &2 * K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * A <= &1 / &2 * A` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

let P2C_LNABLA_ITER_3 = prove
 (`!k (G:real^N->real^N^N) tf.
     lnabla_iter k 3 G tf = lnabla (k + 2) G (lnabla (k + 1) G (lnabla k G tf))`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; lnabla_iter; ADD_CLAUSES]);;

(* The arithmetic of the absorption. *)

let P2C_AF_ARITH = prove
 (`!A0 A1 A2 d Cb Db Eb H0 H1 H2 H3 K0 K1 K2 B0 B1 B2.
     &0 <= Cb /\ &0 <= Db /\ &0 <= Eb /\
     (&4 * (Cb + Db + Eb) + &1) * d <= &1 /\
     &0 <= H0 /\ &0 <= H1 /\ &0 <= H2 /\ &0 <= A0 /\ &0 <= A1 /\ &0 <= A2 /\
     H0 <= d /\ H1 <= d /\ H2 <= d /\ H3 <= d /\
     K0 <= &3 * H1 /\ K1 <= &3 * H2 /\ K2 <= &3 * H3 /\
     B0 <= Cb * H0 * A0 /\
     B1 <= Db * (H1 * A0 + H0 * A1) /\
     B2 <= Eb * (H2 * A0 + H1 * A1 + H0 * A2) /\
     A0 <= &2 * K0 + &2 * B0 /\ A1 <= &2 * K1 + &2 * B1 /\ A2 <= &2 * K2 + &2 * B2
     ==> A0 <= &12 * d /\ A1 <= &24 * d /\ A2 <= &48 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cb * d /\ &0 <= Db * d /\ &0 <= Eb * d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `Cb * d <= &1 / &4 /\ Db * d <= &1 / &4 /\ Eb * d <= &1 / &4`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A0 <= &12 * d` ASSUME_TAC THENL
   [SUBGOAL_THEN `Cb * H0 * A0 <= (Cb * d) * A0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `A <= &2 * (&6 * d) ==> A <= &12 * d`) THEN
    MATCH_MP_TAC P2C_ABSORB THEN EXISTS_TAC `&2 * Cb * d` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A1 <= &24 * d` ASSUME_TAC THENL
   [SUBGOAL_THEN `Db * (H1 * A0 + H0 * A1) <= Db * (d * (&12 * d) + d * A1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Db * d) * d <= &1 / &4 * d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `A <= &2 * (&12 * d) ==> A <= &24 * d`) THEN
    MATCH_MP_TAC P2C_ABSORB THEN EXISTS_TAC `&2 * Db * d` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A2 <= &48 * d` ASSUME_TAC THENL
   [SUBGOAL_THEN `Eb * (H2 * A0 + H1 * A1 + H0 * A2) <=
                  Eb * (d * (&12 * d) + d * (&24 * d) + d * A2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Eb * d) * d <= &1 / &4 * d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `A <= &2 * (&24 * d) ==> A <= &48 * d`) THEN
    MATCH_MP_TAC P2C_ABSORB THEN EXISTS_TAC `&2 * Eb * d` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The af bounds. *)

let P2C_AF_BOUNDS = prove
 (`?C. &0 < C /\
       !s (G0:real^N->real^N^N) G y d.
         metric_field s G0 /\ metric_field s G /\ y IN s /\ C * d <= &1 /\
         (!l. l <= 3 ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d)
         ==> ltnorm2 3 G0 (p2c_af G0 G) y <= &12 * d /\
             ltnorm2 4 G0 (lnabla 3 G0 (p2c_af G0 G)) y <= &24 * d /\
             ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_af G0 G))) y <= &48 * d`,
  X_CHOOSE_THEN `Cb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_BH_LBILIN)) THEN
  X_CHOOSE_THEN `Db:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "db"))
   (CONV_RULE NUM_REDUCE_CONV (MATCH_MP P2C_LBILIN_ON_DNORM (INST_TYPE [`:N`,`:N`] P2C_BH_LBILIN))) THEN
  X_CHOOSE_THEN `Eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eb"))
   (CONV_RULE NUM_REDUCE_CONV (MATCH_MP P2C_LBILIN_ON_D2NORM (INST_TYPE [`:N`,`:N`] P2C_BH_LBILIN))) THEN
  EXISTS_TAC `&4 * (Cb + Db + Eb) + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`; `d:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z u. z IN s ==> p2c_af (G0:real^N->real^N^N) G z u =
                     p2c_kt G0 G z u - p2c_bh G0 (p2c_hd G0 G) (p2c_af G0 G) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_kt] THEN BETA_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `z:real^N`; `u:num->real^N`] P2C_K_RELATION) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = p2c_hd (G0:real^N->real^N^N) G` THEN
  ABBREV_TAC `af = p2c_af (G0:real^N->real^N^N) G` THEN
  ABBREV_TAC `kt = p2c_kt (G0:real^N->real^N^N) G` THEN
  ABBREV_TAC `bh = p2c_bh (G0:real^N->real^N^N) h af` THEN
  (* tensor fields along the way *)
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `h:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "hit") THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `af:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ait") THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `kt:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "kit") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `h:real^N->(num->real^N)->real`; `af:real^N->(num->real^N)->real`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BH_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `bh:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bit") THEN
  USE_THEN "hit" (MP_TAC o SPEC `1`) THEN USE_THEN "hit" (MP_TAC o SPEC `2`) THEN
  USE_THEN "ait" (MP_TAC o SPEC `1`) THEN USE_THEN "ait" (MP_TAC o SPEC `2`) THEN
  USE_THEN "kit" (MP_TAC o SPEC `1`) THEN USE_THEN "kit" (MP_TAC o SPEC `2`) THEN
  USE_THEN "bit" (MP_TAC o SPEC `1`) THEN USE_THEN "bit" (MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC)) THEN
  (* the C^3 distance terms *)
  UNDISCH_TAC `!l. l <= 3 ==> ltnorm2 (2 + l) (G0:real^N->real^N^N)
                                 (lnabla_iter 2 l G0 h) y <= d` THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                       MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  (* the K terms *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`0`; `y:real^N`] th) THEN
                       MP_TAC(SPECL [`1`; `y:real^N`] th) THEN
                       MP_TAC(SPECL [`2`; `y:real^N`] th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  (* the identities af = kt - bh and their derivatives *)
  SUBGOAL_THEN `!z u. z IN s ==> lnabla 3 (G0:real^N->real^N^N) af z u =
                                 lnabla 3 G0 kt z u - lnabla 3 G0 bh z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla 3 (G0:real^N->real^N^N) (\z u. kt z u - bh z u) z u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LRG_LNABLA_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. lnabla 4 (G0:real^N->real^N^N) (lnabla 3 G0 af) y u =
                    lnabla 4 G0 (lnabla 3 G0 kt) y u - lnabla 4 G0 (lnabla 3 G0 bh) y u`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla 4 (G0:real^N->real^N^N)
                  (\z u. lnabla 3 G0 kt z u - lnabla 3 G0 bh z u) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LRG_LNABLA_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the difference bounds *)
  SUBGOAL_THEN `ltnorm2 3 (G0:real^N->real^N^N) af y <=
                &2 * ltnorm2 3 G0 kt y + &2 * ltnorm2 3 G0 bh y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 3 (G0:real^N->real^N^N) (\z u. kt z u - bh z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 af) y <=
                &2 * ltnorm2 4 G0 (lnabla 3 G0 kt) y +
                &2 * ltnorm2 4 G0 (lnabla 3 G0 bh) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 4 (G0:real^N->real^N^N)
                  (\z u. lnabla 3 G0 kt z u - lnabla 3 G0 bh z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 af)) y <=
                &2 * ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 kt)) y +
                &2 * ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 bh)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 5 (G0:real^N->real^N^N)
                  (\z u. lnabla 4 G0 (lnabla 3 G0 kt) z u -
                         lnabla 4 G0 (lnabla 3 G0 bh) z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the bilinear bounds *)
  USE_THEN "nb" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `h:real^N->(num->real^N)->real`; `af:real^N->(num->real^N)->real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `p2c_bh (G0:real^N->real^N^N) h af = bh`] THEN DISCH_TAC THEN
  USE_THEN "db" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `h:real^N->(num->real^N)->real`; `af:real^N->(num->real^N)->real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `p2c_bh (G0:real^N->real^N^N) h af = bh`] THEN DISCH_TAC THEN
  USE_THEN "eb" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `h:real^N->(num->real^N)->real`; `af:real^N->(num->real^N)->real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `p2c_bh (G0:real^N->real^N^N) h af = bh`] THEN DISCH_TAC THEN
  (* nonnegativity *)
  SUBGOAL_THEN `&0 <= ltnorm2 2 (G0:real^N->real^N^N) h y /\
                &0 <= ltnorm2 3 G0 (lnabla 2 G0 h) y /\
                &0 <= ltnorm2 4 G0 (lnabla 3 G0 (lnabla 2 G0 h)) y /\
                &0 <= ltnorm2 3 G0 af y /\
                &0 <= ltnorm2 4 G0 (lnabla 3 G0 af) y /\
                &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 af)) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_AF_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`Cb:real`; `Db:real`; `Eb:real`;
    `ltnorm2 2 (G0:real^N->real^N^N) h y`;
    `ltnorm2 3 (G0:real^N->real^N^N) (lnabla 2 G0 h) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (lnabla 2 G0 h)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 (lnabla 2 G0 h))) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) kt y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 kt) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 kt)) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) bh y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 bh) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 bh)) y`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The difference E = Rm(G) - Rm(G0) of the curvature 4-tensors              *)
(* (lrm4) as P + Q + H on the common domain: P from nabla kt                 *)
(* (LRG_RIEMANN_DIFF_Q), Q = A.G A in terms of af and kt, H =               *)
(* h(u3, Rm0(u1,u2)u4).                                                      *)
(* ------------------------------------------------------------------------- *)

let p2c_bqq = new_definition
 `p2c_bqq (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    p2c_bq0 G tf tg y u - p2c_bq0 G tf tg y (\m. u(swap(1,2) m))`;;

let p2c_pkt = new_definition
 `p2c_pkt (X:real^N->(num->real^N)->real) =
    (\z u. ltperm (swap(1,2) o swap(2,4)) X z u - ltperm (swap(2,4)) X z u)`;;

let P2C_SWAP124_PERMUTES = prove
 (`!n. 4 <= n ==> (swap(1,2) o swap(2,4)) permutes 1..n /\ swap(2,4) permutes 1..n`,
  REPEAT STRIP_TAC THEN TRY(MATCH_MP_TAC PERMUTES_COMPOSE THEN CONJ_TAC) THEN
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

(* A(v1,v2).G A(w1,w2) as a contraction of af and kt. *)

let P2C_AGA = prove
 (`!s (G0:real^N->real^N^N) G z v1 v2 w1 w2.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> (christoffel G z v1 v2 - christoffel G0 z v1 v2) dot
         (G z ** (christoffel G z w1 w2 - christoffel G0 z w1 w2)) =
         p2c_bq0 G0 (p2c_af G0 G) (p2c_kt G0 G) z
           (\m. if m = 1 then v1 else if m = 2 then w1 else if m = 3 then w2 else v2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_kt G0 (G:real^N->real^N^N)`; `z:real^N`; `3`;
                 `\m:num. if m = 1 then (w1:real^N) else w2`;
                 `christoffel G z v1 v2 - christoffel (G0:real^N->real^N^N) z v1 v2`]
                RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN
  REWRITE_TAC[p2c_kt; p2c_bq0; p2c_af] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* h(u3, Rm0(u1,u2)u4) as a contraction of h and Rm0. *)

let P2C_HRM = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> p2c_hd G0 G z (\m. if m = 1 then u 3 else lriemann G0 z (u 1) (u 2) (u 4)) =
         p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0) z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2c_hd G0 (G:real^N->real^N^N) z
      (\m. if m = 1 then (u:num->real^N) 3 else lriemann G0 z (u 1) (u 2) (u 4)) =
    p2c_hd G0 G z (\m. if m = 2 then lriemann G0 z (u 1) (u 2) (u 4)
                       else (\m:num. u 3) m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2c_hd; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`; `z:real^N`; `2`;
                 `\m:num. (u:num->real^N) 3`;
                 `lriemann (G0:real^N->real^N^N) z (u 1) (u 2) (u 4)`]
                RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2c_bh4] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[lrm4; p2c_hd; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`; `a:num`; `b:num`]
                LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* The decomposition E = P + Q + H. *)

let P2C_RMD_SPLIT = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> lrm4 G z u - lrm4 G0 z u =
         p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)) z u +
         p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G) z u +
         p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0) z u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lrm4 G z u - lrm4 G0 z u =
    (u:num->real^N) 3 dot ((G:real^N->real^N^N) z **
      (lriemann G z (u 1) (u 2) (u 4) - lriemann G0 z (u 1) (u 2) (u 4))) +
    p2c_hd G0 G z (\m. if m = 1 then u 3 else lriemann G0 z (u 1) (u 2) (u 4))`
  SUBST1_TAC THENL
   [REWRITE_TAC[lrm4; p2c_hd; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `z:real^N`;
                 `u:num->real^N`] P2C_HRM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`;
                 `(u:num->real^N) 3`] LRG_RIEMANN_DIFF_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM p2c_kt] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 4`; `(u:num->real^N) 2`;
                 `(u:num->real^N) 3`] P2C_AGA) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 2`; `(u:num->real^N) 4`; `(u:num->real^N) 1`;
                 `(u:num->real^N) 3`] P2C_AGA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a = p /\ b = q ==> (a + b) + c = p + q + c`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                  P2C_KT_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `p2c_kt G0 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    REWRITE_TAC[p2c_pkt; ltperm] THEN
    BINOP_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
    MAP_EVERY EXISTS_TAC [`4`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4`
      (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC[swap; o_THM] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[p2c_bqq; p2c_bq0; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers: sums and differences of smooth tensor fields, their derivatives *)
(* and norms; the slot-permutation difference p2c_pkt.                       *)
(* ------------------------------------------------------------------------- *)

let P2C_BQQ_LBILIN = prove
 (`lbilin_on 4 3 3
     (p2c_bqq:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(ISPECL [`4`; `3`; `3`; `swap(1,2)`;
                 `p2c_bq0:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`]
                RFA_LBILIN_ON_PERM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2C_BQ0_LBILIN] THEN MATCH_MP_TAC PERMUTES_SWAP THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`4`; `3`; `3`;
                 `p2c_bq0:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`;
                 `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real).
                   ltperm (swap(1,2)) (p2c_bq0 G tf tg)`]
                RFA_LBILIN_ON_SUB) THEN
  ASM_REWRITE_TAC[P2C_BQ0_LBILIN] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_bqq; ltperm]);;

let P2C_FIELD_ADD_SUB = prove
 (`!k U (f:real^N->(num->real^N)->real) g.
     open U /\ ltensor_field k U f /\ (!u. smooth_map_on U (\y. lift(f y u))) /\
     ltensor_field k U g /\ (!u. smooth_map_on U (\y. lift(g y u)))
     ==> (ltensor_field k U (\y u. f y u + g y u) /\
          (!u. smooth_map_on U (\y. lift(f y u + g y u)))) /\
         (ltensor_field k U (\y u. f y u - g y u) /\
          (!u. smooth_map_on U (\y. lift(f y u - g y u))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `f:real^N->(num->real^N)->real`;
                 `g:real^N->(num->real^N)->real`; `&1`; `&1`]
                LRG_TENSOR_FIELD_LINCOMB) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `f:real^N->(num->real^N)->real`;
                 `g:real^N->(num->real^N)->real`; `&1`; `--(&1)`]
                LRG_TENSOR_FIELD_LINCOMB) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; GSYM real_sub] THEN SIMP_TAC[]);;

let P2C_LNABLA_ADD3 = prove
 (`!k U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B C y u.
     open U /\ y IN U /\
     (!u. smooth_map_on U (\z. lift(A z u))) /\
     (!u. smooth_map_on U (\z. lift(B z u))) /\
     (!u. smooth_map_on U (\z. lift(C z u)))
     ==> lnabla k G (\y u. A y u + B y u + C y u) y u =
         lnabla k G A y u + lnabla k G B y u + lnabla k G C y u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla k (G:real^N->real^N^N) A y u +
              lnabla k G (\y u. (B:real^N->(num->real^N)->real) y u + C y u) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_ADD THEN BETA_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[];
    AP_TERM_TAC THEN MATCH_MP_TAC LRG_LNABLA_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P2C_LTNORM2_ADD3_LE = prove
 (`!k U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B C y.
     metric_field U G /\ ltensor_field k U A /\ ltensor_field k U B /\
     ltensor_field k U C /\ y IN U
     ==> ltnorm2 k G (\y u. A y u + B y u + C y u) y <=
         &2 * ltnorm2 k G A y + &4 * ltnorm2 k G B y + &4 * ltnorm2 k G C y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`;
                 `\y u. (B:real^N->(num->real^N)->real) y u + C y u`; `y:real^N`]
                RFA_LTNORM2_ADD_LE) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `B:real^N->(num->real^N)->real`; `C:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LTNORM2_ADD_LE) THEN
  ASM_SIMP_TAC[RFA_TENSOR_FIELD_ADD] THEN REAL_ARITH_TAC);;

let P2C_PERM_DIFF_NORM = prove
 (`!k U (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) s1 s2 y.
     metric_field U G /\ ltensor_field k U X /\ y IN U /\
     s1 permutes 1..k /\ s2 permutes 1..k
     ==> ltnorm2 k G (\y u. ltperm s1 X y u - ltperm s2 X y u) y <=
         &4 * ltnorm2 k G X y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s1:num->num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  MP_TAC(ISPECL [`k:num`; `s2:num->num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm s1 (X:real^N->(num->real^N)->real)`;
                 `ltperm s2 (X:real^N->(num->real^N)->real)`; `y:real^N`]
                P2C_LTNORM2_SUB_LE) THEN
  ASM_SIMP_TAC[RFA_LTPERM_FIELD] THEN REAL_ARITH_TAC);;

let P2C_PERM_DIFF_NABLA = prove
 (`!k U (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) s1 s2 y u.
     open U /\ (!u. smooth_map_on U (\y. lift(X y u))) /\ y IN U /\
     s1 permutes 1..k /\ s2 permutes 1..k
     ==> lnabla k G (\y u. ltperm s1 X y u - ltperm s2 X y u) y u =
         ltperm s1 (lnabla k G X) y u - ltperm s2 (lnabla k G X) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `G:real^N->real^N^N`; `ltperm s1 (X:real^N->(num->real^N)->real)`;
                 `ltperm s2 (X:real^N->(num->real^N)->real)`; `y:real^N`;
                 `u:num->real^N`] LRG_LNABLA_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[RFA_LTPERM_SMOOTH];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RFA_LNABLA_LTPERM]]);;

(* ------------------------------------------------------------------------- *)
(* The G0-derivatives of E split as those of P, Q and H.                     *)
(* ------------------------------------------------------------------------- *)

let P2C_PKT_FIELD = prove
 (`!U (X:real^N->(num->real^N)->real).
     open U /\ ltensor_field 4 U X /\ (!u. smooth_map_on U (\y. lift(X y u)))
     ==> ltensor_field 4 U (p2c_pkt X) /\
         (!u. smooth_map_on U (\y. lift(p2c_pkt X y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2c_pkt] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`;
                 `ltperm (swap(1,2) o swap(2,4)) (X:real^N->(num->real^N)->real)`;
                 `ltperm (swap(2,4)) (X:real^N->(num->real^N)->real)`]
                P2C_FIELD_ADD_SUB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_FIELD; RFA_LTPERM_SMOOTH; P2C_SWAP124_PERMUTES; LE_REFL];
    SIMP_TAC[]]);;

let P2C_RMD_DERIVS = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> (!z u. z IN s ==>
            lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u =
            lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))) z u +
            lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) z u +
            lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)) z u) /\
         (!z u. z IN s ==>
            lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) z u =
            lnabla 5 G0 (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)))) z u +
            lnabla 5 G0 (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G))) z u +
            lnabla 5 G0 (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0))) z u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_kt G0 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `X = lnabla 3 (G0:real^N->real^N^N) (p2c_kt G0 G)` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `X:real^N->(num->real^N)->real`] P2C_PKT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_af G0 (G:real^N->real^N^N)`; `p2c_kt G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BQQ_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`; `lrm4 (G0:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BH4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z u. z IN s ==>
       lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u =
       lnabla 4 G0 (p2c_pkt X) z u +
       lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) z u +
       lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 (G0:real^N->real^N^N))) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla 4 (G0:real^N->real^N^N)
        (\y u. p2c_pkt X y u + p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G) y u +
               p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0) y u) z u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN EXPAND_TAC "X" THEN
      MATCH_MP_TAC P2C_RMD_SPLIT THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LNABLA_ADD3 THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_pkt (X:real^N->(num->real^N)->real)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 (G:real^N->real^N^N))`]
                LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_bh4 G0 (p2c_hd G0 G) (lrm4 (G0:real^N->real^N^N))`]
                LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z u. z IN s ==>
       lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) z u =
       lnabla 5 G0 (lnabla 4 G0 (p2c_pkt X)) z u +
       lnabla 5 G0 (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G))) z u +
       lnabla 5 G0 (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G)
                                   (lrm4 (G0:real^N->real^N^N)))) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla 5 (G0:real^N->real^N^N)
        (\y u. lnabla 4 G0 (p2c_pkt X) y u +
               lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) y u +
               lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)) y u) z u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2C_LNABLA_ADD3 THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Norms of P and of its first two derivatives. *)

let P2C_PKT_NORMS = prove
 (`!U (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) y.
     metric_field U G /\ ltensor_field 4 U X /\
     (!u. smooth_map_on U (\y. lift(X y u))) /\ y IN U
     ==> ltnorm2 4 G (p2c_pkt X) y <= &4 * ltnorm2 4 G X y /\
         ltnorm2 5 G (lnabla 4 G (p2c_pkt X)) y <= &4 * ltnorm2 5 G (lnabla 4 G X) y /\
         ltnorm2 6 G (lnabla 5 G (lnabla 4 G (p2c_pkt X))) y <=
         &4 * ltnorm2 6 G (lnabla 5 G (lnabla 4 G X)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(SPEC `4` P2C_SWAP124_PERMUTES) THEN
  MP_TAC(SPEC `5` P2C_SWAP124_PERMUTES) THEN
  MP_TAC(SPEC `6` P2C_SWAP124_PERMUTES) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2c_pkt] THEN MATCH_MP_TAC P2C_PERM_DIFF_NORM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z u. z IN U
          ==> lnabla 4 G (p2c_pkt X) z u =
              ltperm (swap(1,2) o swap(2,4)) (lnabla 4 (G:real^N->real^N^N) X) z u -
              ltperm (swap(2,4)) (lnabla 4 G X) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_pkt] THEN
    MATCH_MP_TAC P2C_PERM_DIFF_NABLA THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 5 (G:real^N->real^N^N)
        (\y u. ltperm (swap(1,2) o swap(2,4)) (lnabla 4 G X) y u -
               ltperm (swap(2,4)) (lnabla 4 G X) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2C_PERM_DIFF_NORM THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`5`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 4 (G:real^N->real^N^N) X`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. lnabla 5 G (lnabla 4 G (p2c_pkt X)) y u =
        ltperm (swap(1,2) o swap(2,4)) (lnabla 5 (G:real^N->real^N^N) (lnabla 4 G X)) y u -
        ltperm (swap(2,4)) (lnabla 5 G (lnabla 4 G X)) y u`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla 5 (G:real^N->real^N^N)
        (\y u. ltperm (swap(1,2) o swap(2,4)) (lnabla 4 G X) y u -
               ltperm (swap(2,4)) (lnabla 4 G X) y u) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2C_PERM_DIFF_NABLA THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ltnorm2 6 (G:real^N->real^N^N)
      (\y u. ltperm (swap(1,2) o swap(2,4)) (lnabla 5 G (lnabla 4 G X)) y u -
             ltperm (swap(2,4)) (lnabla 5 G (lnabla 4 G X)) y u) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2C_PERM_DIFF_NORM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* Iterates of order 4, and the arithmetic of the E bounds. *)

let P2C_LNABLA_ITER_4 = prove
 (`!k (G:real^N->real^N^N) tf.
     lnabla_iter k 4 G tf =
     lnabla (k + 3) G (lnabla (k + 2) G (lnabla (k + 1) G (lnabla k G tf)))`,
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; lnabla_iter;
              ADD_CLAUSES]);;

let P2C_RMD_ARITH = prove
 (`!E0 E1 E2 d K Caf Cq Dq Eqq Ch Dh Ehh A0 A1 A2 K0 K1 K2 K3 H0 H1 H2 R0 R1 R2
    P0 P1 P2 Q0 Q1 Q2 W0 W1 W2.
     &0 <= Caf /\ &0 <= Cq /\ &0 <= Dq /\ &0 <= Eqq /\ &0 <= Ch /\ &0 <= Dh /\
     &0 <= Ehh /\ &0 <= d /\ d <= &1 /\ &0 <= K /\
     &0 <= A0 /\ &0 <= A1 /\ &0 <= A2 /\ &0 <= K0 /\ &0 <= K1 /\ &0 <= K2 /\
     &0 <= H0 /\ &0 <= H1 /\ &0 <= H2 /\ &0 <= R0 /\ &0 <= R1 /\ &0 <= R2 /\
     A0 <= &12 * d /\ A1 <= &24 * d /\ A2 <= &48 * d /\
     K0 <= &3 * d /\ K1 <= &3 * d /\ K2 <= &3 * d /\ K3 <= &3 * d /\
     H0 <= d /\ H1 <= d /\ H2 <= d /\ R0 <= K /\ R1 <= K /\ R2 <= K /\
     P0 <= &4 * K1 /\ P1 <= &4 * K2 /\ P2 <= &4 * K3 /\
     Q0 <= Cq * A0 * K0 /\ Q1 <= Dq * (A1 * K0 + A0 * K1) /\
     Q2 <= Eqq * (A2 * K0 + A1 * K1 + A0 * K2) /\
     W0 <= Ch * H0 * R0 /\ W1 <= Dh * (H1 * R0 + H0 * R1) /\
     W2 <= Ehh * (H2 * R0 + H1 * R1 + H0 * R2) /\
     E0 <= &2 * P0 + &4 * Q0 + &4 * W0 /\ E1 <= &2 * P1 + &4 * Q1 + &4 * W1 /\
     E2 <= &2 * P2 + &4 * Q2 + &4 * W2
     ==> E0 <= (Caf + &1 + (&24 + &1008 * (Cq + Dq + Eqq) +
                           &12 * K * (Ch + Dh + Ehh))) * d /\
         E1 <= (Caf + &1 + (&24 + &1008 * (Cq + Dq + Eqq) +
                           &12 * K * (Ch + Dh + Ehh))) * d /\
         E2 <= (Caf + &1 + (&24 + &1008 * (Cq + Dq + Eqq) +
                           &12 * K * (Ch + Dh + Ehh))) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d * d <= d` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= Caf * d /\ &0 <= Cq * d /\ &0 <= Dq * d /\ &0 <= Eqq * d /\
    &0 <= Ch * K * d /\ &0 <= Dh * K * d /\ &0 <= Ehh * K * d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cq * (d * d) <= Cq * d /\ Dq * (d * d) <= Dq * d /\ Eqq * (d * d) <= Eqq * d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cq * A0 * K0 <= Cq * ((&12 * d) * (&3 * d)) /\
    Dq * (A1 * K0 + A0 * K1) <= Dq * ((&24 * d) * (&3 * d) + (&12 * d) * (&3 * d)) /\
    Eqq * (A2 * K0 + A1 * K1 + A0 * K2) <=
    Eqq * ((&48 * d) * (&3 * d) + (&24 * d) * (&3 * d) + (&12 * d) * (&3 * d)) /\
    Ch * H0 * R0 <= Ch * (d * K) /\
    Dh * (H1 * R0 + H0 * R1) <= Dh * (d * K + d * K) /\
    Ehh * (H2 * R0 + H1 * R1 + H0 * R2) <= Ehh * (d * K + d * K + d * K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Fields of the first two derivatives of a smooth tensor field. *)

let P2C_FIELD_D2 = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field (k + 1) U (lnabla k G tf) /\
         (!u. smooth_map_on U (\y. lift(lnabla k G tf y u))) /\
         ltensor_field (k + 2) U (lnabla (k + 1) G (lnabla k G tf)) /\
         (!u. smooth_map_on U (\y. lift(lnabla (k + 1) G (lnabla k G tf) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla k (G:real^N->real^N^N) tf`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`]);;

(* The bounds: E, nabla E and nabla^2 E are O(d) when the C^4 distance is d. *)

let P2C_RMD_BOUNDS = prove
 (`!K. ?C. &0 < C /\
     !s (G0:real^N->real^N^N) G y d.
       metric_field s G0 /\ metric_field s G /\ y IN s /\ C * d <= &1 /\
       (!l. l <= 4 ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d) /\
       ltnorm2 4 G0 (lrm4 G0) y <= K /\
       ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y <= K /\
       ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y <= K
       ==> ltnorm2 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y <= C * d /\
           ltnorm2 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y <= C * d /\
           ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y
           <= C * d`,
  GEN_TAC THEN
  X_CHOOSE_THEN `Caf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "af"))
   (INST_TYPE [`:N`,`:N`] P2C_AF_BOUNDS) THEN
  X_CHOOSE_THEN `Cq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nq"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_BQQ_LBILIN)) THEN
  X_CHOOSE_THEN `Dq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dq"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_DNORM (INST_TYPE [`:N`,`:N`] P2C_BQQ_LBILIN))) THEN
  X_CHOOSE_THEN `Eqq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_D2NORM (INST_TYPE [`:N`,`:N`] P2C_BQQ_LBILIN))) THEN
  X_CHOOSE_THEN `Ch:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_BH4_LBILIN)) THEN
  X_CHOOSE_THEN `Dh:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dh"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_DNORM (INST_TYPE [`:N`,`:N`] P2C_BH4_LBILIN))) THEN
  X_CHOOSE_THEN `Ehh:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eh"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_D2NORM (INST_TYPE [`:N`,`:N`] P2C_BH4_LBILIN))) THEN
  EXISTS_TAC `Caf + &1 + (&24 + &1008 * (Cq + Dq + Eqq) +
                          &12 * abs K * (Ch + Dh + Ehh))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + &1 + b`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= &24 + &1008 * x + &12 * y`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`; `d:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  (* fields *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_kt G0 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  (* the identities at y *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "d2")) THEN
  (* norm facts; then abbreviations *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 3 G0 (p2c_kt G0 (G:real^N->real^N^N))`; `y:real^N`]
                P2C_PKT_NORMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "nq" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_af G0 (G:real^N->real^N^N)`; `p2c_kt G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "dq" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_af G0 (G:real^N->real^N^N)`; `p2c_kt G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "eq" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_af G0 (G:real^N->real^N^N)`; `p2c_kt G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "nh" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_hd G0 (G:real^N->real^N^N)`; `lrm4 (G0:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "dh" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_hd G0 (G:real^N->real^N^N)`; `lrm4 (G0:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "eh" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `p2c_hd G0 (G:real^N->real^N^N)`; `lrm4 (G0:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the distance terms *)
  UNDISCH_TAC `!l. l <= 4 ==> ltnorm2 (2 + l) (G0:real^N->real^N^N)
                                 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d` THEN
  DISCH_THEN(LABEL_TAC "dist") THEN
  USE_THEN "dist" (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                             MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
                             MP_TAC(SPEC `4` th)) THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3; P2C_LNABLA_ITER_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  (* nonnegativity *)
  SUBGOAL_THEN
   `&0 <= ltnorm2 2 (G0:real^N->real^N^N) (p2c_hd G0 G) y /\
    &0 <= ltnorm2 3 G0 (lnabla 2 G0 (p2c_hd G0 G)) y /\
    &0 <= ltnorm2 4 G0 (lnabla 3 G0 (lnabla 2 G0 (p2c_hd G0 G))) y /\
    &0 <= ltnorm2 3 G0 (p2c_af G0 G) y /\
    &0 <= ltnorm2 4 G0 (lnabla 3 G0 (p2c_af G0 G)) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_af G0 G))) y /\
    &0 <= ltnorm2 3 G0 (p2c_kt G0 G) y /\
    &0 <= ltnorm2 4 G0 (lnabla 3 G0 (p2c_kt G0 G)) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_kt G0 G))) y /\
    &0 <= ltnorm2 4 G0 (lrm4 G0) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y /\
    &0 <= ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `p2c_hd G0 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `p2c_af G0 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `p2c_kt G0 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* scalar facts *)
  SUBGOAL_THEN `&0 <= d /\ &0 <= K` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs K = K` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < Caf`)) THEN
  SUBGOAL_THEN `&0 <= (&24 + &1008 * (Cq + Dq + Eqq) + &12 * K * (Ch + Dh + Ehh)) * d /\
                &0 <= Caf * d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= &24 + &1008 * x + &12 * y`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1 /\ Caf * d <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Caf + &1 + &24 + &1008 * (Cq + Dq + Eqq) + &12 * K * (Ch + Dh + Ehh)) *
                 d <= &1` THEN
    UNDISCH_TAC `&0 <= (&24 + &1008 * (Cq + Dq + Eqq) + &12 * K * (Ch + Dh + Ehh)) * d` THEN
    UNDISCH_TAC `&0 <= Caf * d` THEN UNDISCH_TAC `&0 <= d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the af bounds *)
  USE_THEN "af" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                 `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  (* the kt bounds *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_KT_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`0`; `y:real^N`] th) THEN
                       MP_TAC(SPECL [`1`; `y:real^N`] th) THEN
                       MP_TAC(SPECL [`2`; `y:real^N`] th) THEN
                       MP_TAC(SPECL [`3`; `y:real^N`] th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3; P2C_LNABLA_ITER_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 3 (G0:real^N->real^N^N) (p2c_kt G0 G) y <= &3 * d /\
    ltnorm2 4 G0 (lnabla 3 G0 (p2c_kt G0 G)) y <= &3 * d /\
    ltnorm2 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_kt G0 G))) y <= &3 * d /\
    ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_kt G0 G)))) y <= &3 * d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC(MATCH_MP
      (REAL_ARITH `a <= &3 * b ==> b <= d ==> a <= &3 * d`) th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* fields of P, Q, H and their derivatives *)
  MP_TAC(ISPECL [`s:real^N->bool`; `lnabla 3 G0 (p2c_kt G0 (G:real^N->real^N^N))`]
                P2C_PKT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_af G0 (G:real^N->real^N^N)`; `p2c_kt G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BQQ_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_hd G0 (G:real^N->real^N^N)`; `lrm4 (G0:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_BH4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_pkt (lnabla 3 G0 (p2c_kt G0 (G:real^N->real^N^N)))`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 (G:real^N->real^N^N))`]
                P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_bh4 G0 (p2c_hd G0 G) (lrm4 (G0:real^N->real^N^N))`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  (* the E bounds by the splits *)
  SUBGOAL_THEN
   `ltnorm2 4 (G0:real^N->real^N^N) (\z u. lrm4 G z u - lrm4 G0 z u) y <=
    &2 * ltnorm2 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))) y +
    &4 * ltnorm2 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) y +
    &4 * ltnorm2 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 4 (G0:real^N->real^N^N)
        (\y u. p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)) y u +
               p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G) y u +
               p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC P2C_RMD_SPLIT THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_ADD3_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y <=
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)))) y +
    &4 * ltnorm2 5 G0 (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G))) y +
    &4 * ltnorm2 5 G0 (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0))) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 5 (G0:real^N->real^N^N)
        (\y u. lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))) y u +
               lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) y u +
               lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "d1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_ADD3_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 6 (G0:real^N->real^N^N)
      (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y <=
    &2 * ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))))) y +
    &4 * ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0
                         (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)))) y +
    &4 * ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0
                         (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)))) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 6 (G0:real^N->real^N^N)
        (\y u. lnabla 5 G0 (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)))) y u +
               lnabla 5 G0 (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G))) y u +
               lnabla 5 G0 (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0))) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "d2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_ADD3_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the arithmetic *)
  MATCH_MP_TAC P2C_RMD_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`ltnorm2 3 (G0:real^N->real^N^N) (p2c_af G0 G) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (p2c_af G0 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 (p2c_af G0 G))) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) (p2c_kt G0 G) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (p2c_kt G0 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lnabla 3 G0 (p2c_kt G0 G))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (lnabla 3 G0 (p2c_kt G0 G)))) y`;
    `ltnorm2 2 (G0:real^N->real^N^N) (p2c_hd G0 G) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) (lnabla 2 G0 (p2c_hd G0 G)) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (lnabla 2 G0 (p2c_hd G0 G))) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G0) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G0)) y`;
    `ltnorm2 6 (G0:real^N->real^N^N) (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G)))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (p2c_pkt (lnabla 3 G0 (p2c_kt G0 G))))) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N)
       (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (p2c_bqq G0 (p2c_af G0 G) (p2c_kt G0 G)))) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (p2c_bh4 G0 (p2c_hd G0 G) (lrm4 G0)))) y`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The first two G-covariant derivatives of the curvature                    *)
(* tensor of G, D1 = nabla_G Rm(G) and D2 = nabla_G D1, are O(d) in G0-norm *)
(* when G0 has parallel curvature (nabla_G0 Rm(G0) = 0, true for the round   *)
(* cylinder and the round sphere): D1 = nabla_G0 E - Ins(Rm(G), af) and      *)
(* D2 = nabla_G0 D1 - Ins(D1, af) (P2C_CONN_DIFF).                          *)
(* ------------------------------------------------------------------------- *)

let P2C_LTNORM2_ZERO = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y.
     (!u. tf y u = &0) ==> ltnorm2 k G tf y = &0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ltnorm2; REAL_MUL_LZERO; SUM_0]);;

let P2C_RMD_FIELD = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> ltensor_field 4 s (\z u. lrm4 G z u - lrm4 G0 z u) /\
         (!u. smooth_map_on s (\y. lift(lrm4 G y u - lrm4 G0 y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `lrm4 (G:real^N->real^N^N)`;
                 `lrm4 (G0:real^N->real^N^N)`] P2C_FIELD_ADD_SUB) THEN
  ASM_SIMP_TAC[]);;

(* nabla_G0 Rm(G) = nabla_G0 E + nabla_G0 Rm(G0). *)

let P2C_NABLA_T_SPLIT = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> lnabla 4 G0 (lrm4 G) z u =
         lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u + lnabla 4 G0 (lrm4 G0) z u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lrm4 (G:real^N->real^N^N) =
    (\z u. (\z u. lrm4 G z u - lrm4 G0 z u) z u + lrm4 (G0:real^N->real^N^N) z u)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [th])
  THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LRG_LNABLA_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The identities for D1 and D2 when Rm(G0) is parallel on the domain. *)

let P2C_INS4_LBILIN = prove
 (`lbilin_on 5 4 3
     (p2c_ins 4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(SPEC `4` (INST_TYPE [`:N`,`:N`] P2C_INS_LBILIN)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2C_INS5_LBILIN = prove
 (`lbilin_on 6 5 3
     (p2c_ins 5:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`,
  MP_TAC(SPEC `5` (INST_TYPE [`:N`,`:N`] P2C_INS_LBILIN)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2C_DRM_IDS = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G /\
     (!z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0)
     ==> (!z u. z IN s ==>
            lnabla 4 G (lrm4 G) z u =
            lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u -
            p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) z u) /\
         (!z u. z IN s ==>
            lnabla 5 G (lnabla 4 G (lrm4 G)) z u =
            (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) z u -
             lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) z u) -
            p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G) z u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u`]
                LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z u. z IN s ==>
       lnabla 4 G (lrm4 G) z u =
       lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u -
       p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) (z:real^N) u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`; `z:real^N`; `u:num->real^N`]
                  P2C_CONN_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `z:real^N`; `u:num->real^N`] P2C_NABLA_T_SPLIT) THEN
    ASM_SIMP_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `z:real^N`; `u:num->real^N`]
                P2C_CONN_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 5 (G0:real^N->real^N^N)
      (\y u. lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y u -
             p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) y u) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC LRG_LNABLA_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* The arithmetic of the D bounds. *)

let P2C_DRM_ARITH = prove
 (`!D1 D2 d K Caf CE Ci4 Di4 Ci5 E0 E1 E2 A0 A1 R0 TT NT I4 DI4 I5.
     &0 <= Caf /\ &0 <= CE /\ &0 <= Ci4 /\ &0 <= Di4 /\ &0 <= Ci5 /\
     &0 <= d /\ d <= &1 /\ &0 <= K /\
     &0 <= A0 /\ &0 <= A1 /\ &0 <= TT /\ &0 <= NT /\ &0 <= D1 /\
     E0 <= CE * d /\ E1 <= CE * d /\ E2 <= CE * d /\
     A0 <= &12 * d /\ A1 <= &24 * d /\ R0 <= K /\
     TT <= &2 * E0 + &2 * R0 /\ NT = E1 /\
     I4 <= Ci4 * TT * A0 /\ D1 <= &2 * E1 + &2 * I4 /\
     DI4 <= Di4 * (NT * A0 + TT * A1) /\ I5 <= Ci5 * D1 * A0 /\
     D2 <= &2 * (&2 * E2 + &2 * DI4) + &2 * I5
     ==> D1 <= (Caf + CE + &1 +
                ((&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) + &4 * CE +
                 &4 * Di4 * (&12 * CE + &24 * (&2 * CE + &2 * K)) +
                 &24 * Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)))) * d /\
         D2 <= (Caf + CE + &1 +
                ((&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) + &4 * CE +
                 &4 * Di4 * (&12 * CE + &24 * (&2 * CE + &2 * K)) +
                 &24 * Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)))) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = &2 * CE + &2 * K` THEN
  ABBREV_TAC `M1 = &2 * CE + &24 * Ci4 * B` THEN
  SUBGOAL_THEN `&0 <= B /\ &0 <= M1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M1"; "B"] THEN
    SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * K)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * d <= d` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CE * d <= CE` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `TT <= B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `I4 <= Ci4 * (B * (&12 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ci4 * TT * A0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `D1 <= M1 * d` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DI4 <= Di4 * ((CE * d) * (&12 * d) + B * (&24 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Di4 * (NT * A0 + TT * A1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Di4 * (CE * (d * d)) <= Di4 * (CE * d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `I5 <= Ci5 * ((M1 * d) * (&12 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ci5 * D1 * A0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ci5 * (M1 * (d * d)) <= Ci5 * (M1 * d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= Caf * d /\ &0 <= CE * d /\ &0 <= Di4 * CE * d /\ &0 <= Di4 * B * d /\
    &0 <= Ci5 * M1 * d /\ &0 <= M1 * d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* The D bounds. *)

let P2C_DRM_BOUNDS = prove
 (`!K. ?C. &0 < C /\
     !s (G0:real^N->real^N^N) G y d.
       metric_field s G0 /\ metric_field s G /\ y IN s /\ C * d <= &1 /\
       (!l. l <= 4 ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d) /\
       ltnorm2 4 G0 (lrm4 G0) y <= K /\
       (!z u. z IN s ==> lnabla 4 G0 (lrm4 G0) z u = &0)
       ==> ltnorm2 5 G0 (lnabla 4 G (lrm4 G)) y <= C * d /\
           ltnorm2 6 G0 (lnabla 5 G (lnabla 4 G (lrm4 G))) y <= C * d`,
  GEN_TAC THEN
  X_CHOOSE_THEN `Caf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "af"))
   (INST_TYPE [`:N`,`:N`] P2C_AF_BOUNDS) THEN
  X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd"))
   (SPEC `K:real` (INST_TYPE [`:N`,`:N`] P2C_RMD_BOUNDS)) THEN
  X_CHOOSE_THEN `Ci4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ni4"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_INS4_LBILIN)) THEN
  X_CHOOSE_THEN `Di4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "di4"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_DNORM (INST_TYPE [`:N`,`:N`] P2C_INS4_LBILIN))) THEN
  X_CHOOSE_THEN `Ci5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ni5"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_INS5_LBILIN)) THEN
  EXISTS_TAC
   `Caf + CE + &1 +
    ((&2 * CE + &24 * Ci4 * (&2 * CE + &2 * abs K)) + &4 * CE +
     &4 * Di4 * (&12 * CE + &24 * (&2 * CE + &2 * abs K)) +
     &24 * Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * abs K)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * abs K) /\
                  &0 <= Di4 * (&12 * CE + &24 * (&2 * CE + &2 * abs K)) /\
                  &0 <= Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * abs K))`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `K:real` REAL_ABS_POS) THEN
      TRY(SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * abs K)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `K:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`; `d:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  UNDISCH_TAC `!l. l <= 4 ==> ltnorm2 (2 + l) (G0:real^N->real^N^N)
                                 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d` THEN
  DISCH_THEN(LABEL_TAC "dist") THEN
  UNDISCH_TAC `!z u. z IN s ==> lnabla 4 (G0:real^N->real^N^N) (lrm4 G0) z u = &0` THEN
  DISCH_THEN(LABEL_TAC "par") THEN
  (* fields *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_ins 4 G0 (lrm4 G) (p2c_af G0 (G:real^N->real^N^N))`]
                LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_af G0 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS5_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the identities *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_DRM_IDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1") (LABEL_TAC "i2")) THEN
  (* distance terms *)
  USE_THEN "dist" (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                             MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
                             MP_TAC(SPEC `4` th)) THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3; P2C_LNABLA_ITER_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  (* nonnegativity *)
  SUBGOAL_THEN
   `&0 <= ltnorm2 2 (G0:real^N->real^N^N) (p2c_hd G0 G) y /\
    &0 <= ltnorm2 4 G0 (lrm4 G0) y /\
    &0 <= ltnorm2 3 G0 (p2c_af G0 G) y /\
    &0 <= ltnorm2 4 G0 (lnabla 3 G0 (p2c_af G0 G)) y /\
    &0 <= ltnorm2 4 G0 (lrm4 G) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G)) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G (lrm4 G)) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d /\ &0 <= K` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs K = K` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  ABBREV_TAC
   `Mt = (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) + &4 * CE +
         &4 * Di4 * (&12 * CE + &24 * (&2 * CE + &2 * K)) +
         &24 * Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K))` THEN
  SUBGOAL_THEN `&0 <= Mt` ASSUME_TAC THENL
   [EXPAND_TAC "Mt" THEN
    SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * K)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Di4 * (&12 * CE + &24 * (&2 * CE + &2 * K)) /\
                  &0 <= Ci5 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K))`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1 /\ Caf * d <= &1 /\ CE * d <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Caf * d /\ &0 <= CE * d /\ &0 <= Mt * d` MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(Caf + CE + &1 + Mt) * d <= &1` THEN UNDISCH_TAC `&0 <= d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* parallel model: the derivative terms of Rm(G0) vanish *)
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G0)) y = &0 /\
    ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_LTNORM2_ZERO THEN GEN_TAC THENL
     [USE_THEN "par" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla 5 (G0:real^N->real^N^N) (\x u. &0) y u` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[LRG_LNABLA_ZERO]] THEN
    MATCH_MP_TAC LRG_LNABLA_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* E bounds *)
  USE_THEN "rmd" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                  `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "dist" ACCEPT_TAC;
    STRIP_TAC] THEN
  (* af bounds *)
  USE_THEN "af" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                 `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  (* |Rm(G)|^2 <= 2|E|^2 + 2|Rm(G0)|^2 and nabla_G0 Rm(G) = nabla_G0 E *)
  SUBGOAL_THEN
   `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G) y <=
    &2 * ltnorm2 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y + &2 * ltnorm2 4 G0 (lrm4 G0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 4 (G0:real^N->real^N^N)
                  (\y u. (\z u. lrm4 G z u - lrm4 G0 z u) y u + lrm4 G0 y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G)) y =
    ltnorm2 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `y:real^N`; `u:num->real^N`] P2C_NABLA_T_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "par" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN s`)]) THEN
    REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  (* Ins bounds *)
  USE_THEN "ni4" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "di4" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "ni5" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `p2c_af G0 (G:real^N->real^N^N)`;
     `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* D1 and D2 by the identities *)
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G (lrm4 G)) y <=
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y +
    &2 * ltnorm2 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 5 (G0:real^N->real^N^N)
        (\y u. lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y u -
               p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "i1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`6`; `s:real^N->bool`;
                 `lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 (G:real^N->real^N^N) z u -
                                                   lrm4 G0 z u))`;
                 `lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 (G:real^N->real^N^N)))`]
                P2C_FIELD_ADD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 6 (G0:real^N->real^N^N) (lnabla 5 G (lnabla 4 G (lrm4 G))) y <=
    &2 * (&2 * ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y +
          &2 * ltnorm2 6 G0 (lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G))) y) +
    &2 * ltnorm2 6 G0 (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 6 (G0:real^N->real^N^N)
        (\y u. (\y u. lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y u -
                      lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y u) y u -
               p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "i2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `&2 * ltnorm2 6 (G0:real^N->real^N^N)
               (\y u. lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y u -
                      lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y u) y +
        &2 * ltnorm2 6 G0 (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> &2 * a + c <= &2 * b + c`) THEN
        MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* arithmetic *)
  EXPAND_TAC "Mt" THEN MATCH_MP_TAC P2C_DRM_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`ltnorm2 4 (G0:real^N->real^N^N) (\z u. lrm4 G z u - lrm4 G0 z u) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) (p2c_af G0 G) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (p2c_af G0 G)) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G0) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y`;
    `ltnorm2 6 (G0:real^N->real^N^N) (lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N) (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* |grad R|^2 and (Lap R)^2 are bounded by n^2 |nabla Rm|^2 and              *)
(* n^3 |nabla^2 Rm|^2 (all for one metric G): R and Ric are contractions of  *)
(* Rm, and nabla commutes with contractions and slot permutations           *)
(* (RFA_LNABLA_LTCONTR, RFA_LNABLA_LTPERM).                                   *)
(* ------------------------------------------------------------------------- *)

let P2C_INDEX_TUPLES_0 = prove
 (`index_tuples 0 (:N) = {(\m:num. 0)}`,
  REWRITE_TAC[EXTENSION; IN_SING] THEN
  REWRITE_TAC[index_tuples; IN_ELIM_THM; FUN_EQ_THM] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [X_GEN_TAC `m:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let P2C_LTNORM2_0 = prove
 (`!(G:real^N->real^N^N) tf y. ltnorm2 0 G tf y = (tf y (\m. basis 0)) pow 2`,
  REWRITE_TAC[ltnorm2; P2C_INDEX_TUPLES_0; SUM_SING; PRODUCT_CLAUSES_NUMSEG; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_POW_2]);;

let P2C_INDEX_TUPLES_1 = prove
 (`index_tuples 1 (:N) = IMAGE (\a m. if m = 1 then a else 0) (1..dimindex(:N))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  REWRITE_TAC[index_tuples; IN_ELIM_THM; FUN_EQ_THM] THEN
  X_GEN_TAC `x:num->num` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(x:num->num) 1` THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let P2C_SUM_TUPLES_1 = prove
 (`!f:(num->num)->real.
     sum (index_tuples 1 (:N)) f =
     sum(1..dimindex(:N)) (\a. f (\m. if m = 1 then a else 0))`,
  GEN_TAC THEN REWRITE_TAC[P2C_INDEX_TUPLES_1] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) SUM_IMAGE (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let P2C_LTNORM2_1 = prove
 (`!(G:real^N->real^N^N) sf y.
     ltnorm2 1 G sf y =
     sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
        matrix_inv(G y)$a$b * sf y (\m. if m = 1 then basis a else basis 0) *
                              sf y (\m. if m = 1 then basis b else basis 0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltnorm2; P2C_SUM_TUPLES_1] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG; COND_RAND] THEN REAL_ARITH_TAC);;

let P2C_LGRAD2_LTNORM2 = prove
 (`!(G:real^N->real^N^N) f y.
     lgrad2 G f y = ltnorm2 1 G (lnabla 0 G (\z u. f z)) y`,
  REWRITE_TAC[P2C_LTNORM2_1; lgrad2; lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

(* Ric and R as contractions of Rm; their fields. *)

let P2C_RIC_CONTR = prove
 (`!s (G:real^N->real^N^N) z u.
     metric_field s G /\ z IN s
     ==> lric2 G z u = ltcontr G (ltperm (swap(2,3)) (lrm4 G)) z u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lric2] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`] LRG_LRM4_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ltcontr; ltperm] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
  MAP_EVERY EXISTS_TAC [`4`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4`
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[swap] THEN CONV_TAC NUM_REDUCE_CONV);;

let P2C_SCALAR_CONTR = prove
 (`!(G:real^N->real^N^N) z u. lscalar G z = ltcontr G (lric2 G) z u`,
  REWRITE_TAC[lscalar; ltcontr; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2C_RIC_FIELD = prove
 (`!s (G:real^N->real^N^N).
     metric_field s G
     ==> ltensor_field 2 s (lric2 G) /\ (!u. smooth_map_on s (\y. lift(lric2 G y u))) /\
         smooth_map_on s (\y. lift(lscalar G y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 4 s (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))) /\
    (!u. smooth_map_on s (\y. lift(ltperm (swap(2,3)) (lrm4 G) y u)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_SMOOTH] THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERMUTES_SWAP THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. smooth_map_on s (\y. lift(lric2 (G:real^N->real^N^N) y u))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. lift(ltcontr G (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))) y u)` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2C_RIC_CONTR THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`;
                     `ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))`] RFA_LTCONTR_SMOOTH) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_LTENSOR_FIELD_EQ THEN
    EXISTS_TAC `ltcontr G (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_RIC_CONTR THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. lift(ltcontr G (lric2 (G:real^N->real^N^N)) y (\m. basis 0))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM P2C_SCALAR_CONTR];
      MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`;
                     `lric2 (G:real^N->real^N^N)`] RFA_LTCONTR_SMOOTH) THEN
      ASM_SIMP_TAC[]]]);;

(* dR and Hess R as double contractions of nabla Rm and nabla^2 Rm. *)

let P2C_LTCONTR_CONG = prove
 (`!(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) tg y u.
     (!w. tf y w = tg y w) ==> ltcontr G tf y u = ltcontr G tg y u`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ltcontr]);;

let P2C_SW23_PERMUTES = prove
 (`!n. 3 <= n ==> swap(2,3) permutes 1..n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

let P2C_DSCALAR = prove
 (`!s (G:real^N->real^N^N) z u.
     metric_field s G /\ z IN s
     ==> lnabla 0 G (\z u. lscalar G z) z u =
         ltcontr G (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G)))) z u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z u. lscalar G z) = ltcontr G (lric2 (G:real^N->real^N^N))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; GSYM P2C_SCALAR_CONTR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `z:real^N`; `u:num->real^N`]
                RFA_LNABLA_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2C_LTCONTR_CONG THEN X_GEN_TAC `w:num->real^N` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 2 G (ltcontr G (ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N)))) z w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_RIC_CONTR THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (swap(2,3)) (lrm4 (G:real^N->real^N^N))`; `z:real^N`;
                 `w:num->real^N`] RFA_LNABLA_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_SMOOTH] THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN
    ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2C_LTCONTR_CONG THEN GEN_TAC THEN MATCH_MP_TAC RFA_LNABLA_LTPERM THEN
  SIMP_TAC[P2C_SW23_PERMUTES; ARITH]);;

let P2C_HSCALAR = prove
 (`!s (G:real^N->real^N^N) y u.
     metric_field s G /\ y IN s
     ==> lnabla 1 G (lnabla 0 G (\z u. lscalar G z)) y u =
         ltcontr G (ltcontr G (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 G))))) y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 5 s (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))) /\
    (!u. smooth_map_on s (\y. lift(ltperm (swap(2,3)) (lnabla 4 G (lrm4 G)) y u)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_SMOOTH] THEN
    MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `Y = ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))` THEN
  SUBGOAL_THEN `ltensor_field 3 s (ltcontr G (Y:real^N->(num->real^N)->real)) /\
                (!u. smooth_map_on s (\y. lift(ltcontr G Y y u)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_LTCONTR_SMOOTH] THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 1 G (ltcontr G (ltcontr G (Y:real^N->(num->real^N)->real))) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "Y" THEN
    MATCH_MP_TAC P2C_DSCALAR THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (Y:real^N->(num->real^N)->real)`; `y:real^N`; `u:num->real^N`]
                RFA_LNABLA_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2C_LTCONTR_CONG THEN X_GEN_TAC `w:num->real^N` THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `Y:real^N->(num->real^N)->real`; `y:real^N`; `w:num->real^N`]
                RFA_LNABLA_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2C_LTCONTR_CONG THEN GEN_TAC THEN EXPAND_TAC "Y" THEN
  MATCH_MP_TAC RFA_LNABLA_LTPERM THEN SIMP_TAC[P2C_SW23_PERMUTES; ARITH]);;

(* The trace bounds. *)

let P2C_LLAP_CONTR = prove
 (`!s (G:real^N->real^N^N) (H:real^N->(num->real^N)->real) y.
     ltensor_field 2 s H /\ y IN s
     ==> sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
            (\j. matrix_inv(G y)$i$j * H y (\m. if m = 1 then basis j else basis i))) =
         ltcontr G (ltperm (swap(1,2)) H) y (\m. basis 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltcontr; ltperm] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC P2C_TF_ARGS THEN
  MAP_EVERY EXISTS_TAC [`2`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[swap] THEN CONV_TAC NUM_REDUCE_CONV);;

let P2C_SCALAR_DERIV_TRACE = prove
 (`!s (G:real^N->real^N^N) y.
     metric_field s G /\ y IN s
     ==> lgrad2 G (lscalar G) y <=
         &(dimindex(:N)) pow 2 * ltnorm2 5 G (lnabla 4 G (lrm4 G)) y /\
         llap G (lscalar G) y pow 2 <=
         &(dimindex(:N)) pow 3 * ltnorm2 6 G (lnabla 5 G (lnabla 4 G (lrm4 G))) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N))` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 5 s (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))) /\
    ltensor_field 6 s (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 G))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN
    ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[P2C_LGRAD2_LTNORM2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 1 G (ltcontr G (ltcontr G (ltperm (swap(2,3))
                  (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC P2C_DSCALAR THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`1`; `s:real^N->bool`; `G:real^N->real^N^N`;
                   `ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`;
                   `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G:real^N->real^N^N`;
                   `ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`;
                   `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
    MP_TAC(ISPECL [`5`; `swap(2,3)`; `s:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `y:real^N`]
                  RFA_LTNORM2_LTPERM) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH; RFA_LTCONTR_FIELD] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) *
                ltnorm2 3 G (ltcontr G (ltperm (swap(2,3))
                  (lnabla 4 G (lrm4 (G:real^N->real^N^N))))) y` THEN
    ASM_REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the Laplacian *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `lscalar (G:real^N->real^N^N)`;
                 `y:real^N`] LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(\z u. drop(frechet_derivative (\w. lift(lscalar G w)) (at z) (u 1))) =
    lnabla 0 G (\z u. lscalar (G:real^N->real^N^N) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2C_HSCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `ltensor_field 4 s (ltcontr G (ltperm (swap(2,3))
       (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))) /\
    ltensor_field 2 s (ltcontr G (ltcontr G (ltperm (swap(2,3))
       (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (ltcontr G (ltperm (swap(2,3))
                    (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))))`;
                 `y:real^N`] P2C_LLAP_CONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM P2C_LTNORM2_0] THEN
  SUBGOAL_THEN `swap(1,2) permutes 1..2` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 2 s (ltperm (swap(1,2)) (ltcontr G (ltcontr G (ltperm (swap(2,3))
       (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))))))`
  ASSUME_TAC THENL [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (swap(1,2)) (ltcontr G (ltcontr G (ltperm (swap(2,3))
                    (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))))`;
                 `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
  MP_TAC(ISPECL [`2`; `swap(1,2)`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (ltcontr G (ltperm (swap(2,3))
                    (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))))`;
                 `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (ltperm (swap(2,3))
                    (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))`;
                 `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`;
                 `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
  MP_TAC(ISPECL [`6`; `swap(2,3)`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`; `y:real^N`]
                RFA_LTNORM2_LTPERM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH] THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  ABBREV_TAC `x3 = ltnorm2 6 G (ltperm (swap(2,3))
                     (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))) y` THEN
  ABBREV_TAC `x2 = ltnorm2 4 G (ltcontr G (ltperm (swap(2,3))
                     (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))) y` THEN
  ABBREV_TAC `x1 = ltnorm2 2 G (ltcontr G (ltcontr G (ltperm (swap(2,3))
                     (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))))) y` THEN
  ABBREV_TAC `x1' = ltnorm2 2 G (ltperm (swap(1,2)) (ltcontr G (ltcontr G
                      (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G
                         (lrm4 (G:real^N->real^N^N)))))))) y` THEN
  ABBREV_TAC `x0 = ltnorm2 0 G (ltcontr G (ltperm (swap(1,2)) (ltcontr G (ltcontr G
                     (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G
                        (lrm4 (G:real^N->real^N^N))))))))) y` THEN
  SUBGOAL_THEN `n * x1 <= n * (n * x2) /\ n * (n * x2) <= n * (n * (n * x3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `ltnorm2 6 G (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))) y = x3`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `x0 <= n * x1` THEN
  UNDISCH_TAC `n * x1 <= n * (n * x2)` THEN
  UNDISCH_TAC `n * (n * x2) <= n * (n * (n * x3))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nearby metrics.  Frame bounds from the C^2 distance (as in                *)
(* the proof of LCK_CURVATURE_STABILITY), the comparison of the two metrics,*)
(* and the bound of |Ric(G)|_G by |Ric(G0)|_G0 plus O(distance), via        *)
(* LRG_PERT_RICCI and the frame expansion LRG_LTNORM2_SQUARES.              *)
(* ------------------------------------------------------------------------- *)

let P2C_FRAME_SETUP = prove
 (`!s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> ?M:real^N^N. invertible M /\ G0 y = transp M ** M /\
             (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
                    sqrt(lck_dist2 2 G0 G y) * norm(M ** a) * norm(M ** b)) /\
             (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
                  sqrt(lck_dist2 2 G0 G y) *
                  norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
             (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                        y u) <=
                  sqrt(lck_dist2 2 G0 G y) *
                  norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real^N^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 2 (G0:real^N->real^N^N)
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 2 (G0:real^N->real^N^N)
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;

let P2C_LCK_DIST2_POS = prove
 (`!k s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s ==> &0 <= lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* x.G0 x <= x.G x / (1 - delta). *)

let P2C_METRIC_LAM = prove
 (`!s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ sqrt(lck_dist2 2 G0 G y) < &1
     ==> !x. x dot (G0 y ** x) <=
             inv(&1 - sqrt(lck_dist2 2 G0 G y)) * (x dot (G y ** x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_FRAME_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  MP_TAC(ISPECL [`(G0:real^N->real^N^N) y`; `M:real^N^N`; `x:real^N`; `x:real^N`]
                LRG_FRAME_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 - dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* |Ric(G) - Ric(G0)|^2 in G0-norm is O(distance^2). *)

let P2C_SQ_LE = prove
 (`!x y. abs x <= y ==> x pow 2 <= y pow 2`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let P2C_RIC_DIFF_NORM = prove
 (`!s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     sqrt(lck_dist2 2 G0 G y) <= &1 / &10
     ==> ltnorm2 2 G0 (\z u. lric2 G z u - lric2 G0 z u) y <=
         &(CARD(index_tuples 2 (:N))) *
         (&(dimindex(:N)) * (&5 * sqrt(lck_dist2 2 G0 G y))) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_FRAME_SETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `dl:real`] LRG_PERT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `lric2 (G:real^N->real^N^N)`;
                 `lric2 (G0:real^N->real^N^N)`] P2C_FIELD_ADD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lric2 (G:real^N->real^N^N) z u - lric2 G0 z u`; `y:real^N`;
                 `transp(matrix_inv(M:real^N^N))`] LRG_LTNORM2_SQUARES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TRANSP_TRANSP] THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[TRANSP_TRANSP; lric2] THEN
  MATCH_MP_TAC P2C_SQ_LE THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`matrix_inv(M:real^N^N) ** basis(p 1)`;
                                `matrix_inv(M:real^N^N) ** basis(p 2)`] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci"))
                         (concl th) && is_forall(concl th))) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `norm(basis(p 1):real^N) = &1 /\ norm(basis(p 2):real^N) = &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC NORM_BASIS THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `dimindex(:N)`)) (concl th))) THEN
    REWRITE_TAC[ARITH] THEN SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* |Ric(G)|_G <= (|Ric(G0)|_G0 + c delta) / (1 - delta). *)

let P2C_RIC_NORM_BOUND = prove
 (`!s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     sqrt(lck_dist2 2 G0 G y) <= &1 / &10
     ==> sqrt(ltnorm2 2 G (lric2 G) y) <=
         inv(&1 - sqrt(lck_dist2 2 G0 G y)) *
         (sqrt(ltnorm2 2 G0 (lric2 G0) y) +
          sqrt(&(CARD(index_tuples 2 (:N)))) * &(dimindex(:N)) * &5 *
          sqrt(lck_dist2 2 G0 G y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_RIC_DIFF_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_METRIC_LAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_LCK_DIST2_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `lric2 (G:real^N->real^N^N)`;
                 `lric2 (G0:real^N->real^N^N)`] P2C_FIELD_ADD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `dl = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&1 - dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G:real^N->real^N^N`; `G0:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`; `inv(&1 - dl)`]
                LRG_LTNORM2_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lric2 (G0:real^N->real^N^N)`;
                 `\z u. lric2 (G:real^N->real^N^N) z u - lric2 G0 z u`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 2 (G0:real^N->real^N^N) (\z u. lric2 G z u - lric2 G0 z u) y) <=
    sqrt(&(CARD(index_tuples 2 (:N)))) * &(dimindex(:N)) * &5 * dl`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&(CARD(index_tuples 2 (:N))) *
                     (&(dimindex(:N)) * (&5 * dl)) pow 2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL; REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `sqrt((&(dimindex(:N)) * (&5 * dl)) pow 2) = &(dimindex(:N)) * (&5 * dl)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(inv(&1 - dl) pow 2 * ltnorm2 2 (G0:real^N->real^N^N) (lric2 G) y)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL; REAL_LE_POW_2] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

