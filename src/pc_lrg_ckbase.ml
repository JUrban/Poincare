(* ========================================================================= *)
(* LRG_CK_BASE_CHANGE (local Riemannian geometry), the body of               *)
(* P2B_REQ_LRG_BASE_STATEMENT of pc_p2b_defs section S9, proved as a closed  *)
(* theorem (pc_p2b_defs is not loaded): if G1 is within 1/2 of G0 in C^k at  *)
(* y, then the C^k size of G2 - G1 measured with G0 is at most M(k) times    *)
(* the one measured with G1.  Route:                                         *)
(*   nabla_G0 X = nabla_G1 X + (G1-contraction of X with the difference      *)
(*   tensor K of the connections, K = 1/2 x permutations of                  *)
(*   nabla_G0 (G1 - G0));                                                    *)
(* a Leibniz rule of every order for the bilinear operations lbilin_on of    *)
(* pc_rfa_ricid; two triangular inductions over all tensor fields            *)
(* (G1-derivatives by G0-derivatives, which bounds those of K, and           *)
(* conversely); comparison of the norms of G0 and G1.                        *)
(* ========================================================================= *)

needs "src/pc_lrg_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The connection difference of two metrics G0, G1.  geob_ins contracts      *)
(* (with G) a 3-tensor into the slots of a k-tensor; geob_kt G0 G1 is the    *)
(* G1-lowered difference Gamma(G1) - Gamma(G0) (the tensor of                *)
(* LRG_CHRISTOFFEL_DIFF_K).  Then nabla_G0 X = nabla_G1 X + geob_ins G1 X K  *)
(* (GEOB_CONN_DIFF).  geob_ins and geob_kt coincide with p2c_ins and p2c_kt  *)
(* of pc_p2c_cderiv, which is not loaded here (it depends on pc_p3_iface);   *)
(* the proofs follow P2C_INS_LBILIN, P2C_AF_FIELD and P2C_CONN_DIFF with the *)
(* roles of the metrics exchanged.                                           *)
(* ========================================================================= *)

let GEOB_TF_ARGS = prove
 (`!k U (tf:real^N->(num->real^N)->real) y w w'.
     ltensor_field k U tf /\ y IN U /\ (!m. 1 <= m /\ m <= k ==> w m = w' m)
     ==> tf y w = tf y w'`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

let geob_ins = new_definition
 `geob_ins k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
          (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N) =
    sum(1..k)
     (\i. sum(1..dimindex(:N))
       (\a. sum(1..dimindex(:N))
         (\b. matrix_inv(G y)$a$b *
              tf y (\m. if m = i then basis a else u m) *
              tg y (\m. if m = 1 then u(k + 1) else if m = 2 then u i else basis b))))`;;

let GEOB_INS_PERMUTES = prove
 (`!i k. 1 <= i /\ i <= k
         ==> (\m. if m < i then m else if m < k then m + 1 else if m = k then k + 1
                  else if m = k + 1 then i else m) permutes 1..(k + 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m < i then m else if m = i then k + 1 else if m <= k then m - 1
                  else if m = k + 1 then k else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let GEOB_INS_LBILIN = prove
 (`!k. 1 <= k
       ==> lbilin_on (k + 1) k 3
             (geob_ins k:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
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
      (MATCH_MP GEOB_INS_PERMUTES (CONJ (ASSUME `1 <= i`) (ASSUME `i <= k:num`)))) THEN
    DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                         `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`;
                         `y:real^N`; `u:num->real^N`] THEN
    STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
    MATCH_MP_TAC GEOB_TF_ARGS THENL
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
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; geob_ins]);;

let geob_kt = new_definition
 `geob_kt (G0:real^N->real^N^N) (G1:real^N->real^N^N) =
    (\z u. u 3 dot (G1 z ** (christoffel G1 z (u 1) (u 2) - christoffel G0 z (u 1) (u 2))))`;;

let GEOB_KT_FIELD = prove
 (`!s (G0:real^N->real^N^N) G1.
     metric_field s G0 /\ metric_field s G1
     ==> ltensor_field 3 s (geob_kt G0 G1) /\
         (!u. smooth_map_on s (\y. lift(geob_kt G0 G1 y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool) /\
                smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o G1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G1:real^N->real^N^N)` THEN
    REWRITE_TAC[metric_field] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[geob_kt] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST] THEN MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ltensor_field; geob_kt] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`]
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
     `(\v. lift((u:num->real^N) 3 dot ((G1:real^N->real^N^N) y **
              (christoffel G1 y v (u 2) - christoffel (G0:real^N->real^N^N) y v (u 2))))) =
      (\v. (\x. lift(u 3 dot (G1 y ** x)))
             ((\v. christoffel G1 y v (u 2) - christoffel G0 y v (u 2)) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    USE_THEN "b1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "b0" (fun th -> REWRITE_TAC[th]);
    SUBGOAL_THEN
     `(\v. lift((u:num->real^N) 3 dot ((G1:real^N->real^N^N) y **
              (christoffel G1 y (u 1) v - christoffel (G0:real^N->real^N^N) y (u 1) v)))) =
      (\v. (\x. lift(u 3 dot (G1 y ** x)))
             ((\v. christoffel G1 y (u 1) v - christoffel G0 y (u 1) v) v))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN REWRITE_TAC[LRG_LINEAR_DOT_MATVEC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "a1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "a0" (fun th -> REWRITE_TAC[th]);
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT]]);;

(* nabla_G0 X = nabla_G1 X + (the G1-lowered difference inserted into X). *)

let GEOB_CONN_DIFF = prove
 (`!k s (G0:real^N->real^N^N) G1 X z u.
     metric_field s G0 /\ metric_field s G1 /\ ltensor_field k s X /\ z IN s
     ==> lnabla k G0 X z u = lnabla k G1 X z u + geob_ins k G1 X (geob_kt G0 G1) z u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; geob_ins] THEN
  MATCH_MP_TAC(REAL_ARITH `s1 - s0 = t ==> d - s0 = (d - s1) + t`) THEN
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
   [`christoffel (G1:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i)`;
    `christoffel (G0:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i)`]) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM LIFT_SUB; LIFT_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `z:real^N`; `i:num`; `u:num->real^N`;
                 `christoffel (G1:real^N->real^N^N) z ((u:num->real^N)(k + 1)) (u i) -
                  christoffel (G0:real^N->real^N^N) z (u(k + 1)) (u i)`]
                RFA_METRIC_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `matrix_inv((G1:real^N->real^N^N) z)$b$a = matrix_inv(G1 z)$a$b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `basis b dot ((G1:real^N->real^N^N) z **
      (christoffel G1 z ((u:num->real^N)(k + 1)) (u i) -
       christoffel (G0:real^N->real^N^N) z (u(k + 1)) (u i))) =
    geob_kt G0 G1 z (\m. if m = 1 then (u:num->real^N)(k + 1) else if m = 2 then u i
                         else basis b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[geob_kt] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* h = G1 - G0 as a tensor field (geob_hd), the iterated G0-derivatives of K *)
(* = geob_kt G0 G1 are permutations of those of nabla h (GEOB_KT_ITER),      *)
(* hence |nabla_G0^j K| <= 3 |nabla_G0^(j+1) h| in G0 norms (GEOB_KT_NORM).  *)
(* As P2C_KT_ITER and P2C_KT_NORM of pc_p2c_cderiv.                          *)
(* ========================================================================= *)

let geob_hd = new_definition
 `geob_hd (G0:real^N->real^N^N) (G1:real^N->real^N^N) =
    (\z u. lmetric2 G1 z u - lmetric2 G0 z u)`;;

let GEOB_HD_FIELD = prove
 (`!s (G0:real^N->real^N^N) G1.
     metric_field s G0 /\ metric_field s G1
     ==> ltensor_field 2 s (geob_hd G0 G1) /\
         (!u. smooth_map_on s (\y. lift(geob_hd G0 G1 y u)))`,
  REWRITE_TAC[geob_hd] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LMETRIC2_DIFF_FIELD) THEN REWRITE_TAC[]);;

let GEOB_SWAPS_PERMUTE = prove
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

let GEOB_KT_ITER = prove
 (`!s (G0:real^N->real^N^N) G1.
     metric_field s G0 /\ metric_field s G1
     ==> !j z u. z IN s
           ==> lnabla_iter 3 j G0 (geob_kt G0 G1) z u =
               inv(&2) *
               (lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z
                  (\m. u((swap(1,2) o swap(2,3)) m)) +
                lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z (\m. u(swap(2,3) m)) -
                lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
                GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it") THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; LRG_LNABLA_ITER_12] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; LRG_LNABLA_ITER_12] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[geob_kt; geob_hd] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF_K THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Y = lnabla_iter 2 (j + 1) (G0:real^N->real^N^N) (geob_hd G0 G1)` THEN
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
   [MATCH_MP_TAC GEOB_SWAPS_PERMUTE THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lnabla_iter] THEN
  TRANS_TAC EQ_TRANS
   `lnabla (3 + j) (G0:real^N->real^N^N)
      (\z u. inv(&2) * ((Y:real^N->(num->real^N)->real) z (\m. u((swap(1,2) o swap(2,3)) m)) +
                        Y z (\m. u(swap(2,3) m)) - Y z u)) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lnabla_iter 2 (SUC j + 1) (G0:real^N->real^N^N) (geob_hd G0 G1) =
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

let GEOB_LTNORM2_KCOMB = prove
 (`!k U (G:real^N->real^N^N) (Y:real^N->(num->real^N)->real) s1 s2 y.
     metric_field U G /\ ltensor_field k U Y /\ y IN U /\
     s1 permutes 1..k /\ s2 permutes 1..k
     ==> ltnorm2 k G (\z u. inv(&2) * (Y z (\m. u((s1:num->num) m)) +
                                       Y z (\m. u((s2:num->num) m)) - Y z u)) y
         <= &3 * ltnorm2 k G Y y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field k U (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m))) /\
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
   `ltnorm2 k (G:real^N->real^N^N)
      (\z u. (Y:real^N->(num->real^N)->real) z (\m. u((s1:num->num) m))) y =
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

let GEOB_KT_NORM = prove
 (`!s (G0:real^N->real^N^N) G1 j y.
     metric_field s G0 /\ metric_field s G1 /\ y IN s
     ==> ltnorm2 (3 + j) G0 (lnabla_iter 3 j G0 (geob_kt G0 G1)) y <=
         &3 * ltnorm2 (3 + j) G0 (lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1)) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
                GEOB_KT_ITER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
                GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j + 1`) THEN
  REWRITE_TAC[ARITH_RULE `2 + j + 1 = 3 + j`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `3 + j` GEOB_SWAPS_PERMUTE) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ltnorm2 (3 + j) (G0:real^N->real^N^N)
      (\z u. inv(&2) *
             (lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z (\m. u((swap(1,2) o swap(2,3)) m)) +
              lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z (\m. u(swap(2,3) m)) -
              lnabla_iter 2 (j + 1) G0 (geob_hd G0 G1) z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC GEOB_LTNORM2_KCOMB THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The Leibniz rule of every order for the bilinear operations lbilin_on of  *)
(* pc_rfa_ricid: nabla^i E(tf, tg) is a sum over a = 0..i of members of      *)
(* lbilin_on applied to (nabla^a tf, nabla^(i-a) tg).  By induction from     *)
(* RFA_LBILIN_ON_NABLA (first order), RFA_LNABLA_SUM and locality of nabla   *)
(* (LRG_LNABLA_LOCAL).                                                       *)
(* ========================================================================= *)

let GEOB_LBILIN_ON_COND2 = prove
 (`!k p q (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) E2 P Q.
     (P ==> lbilin_on k p q E1) /\ (Q ==> lbilin_on k p q E2) /\ (P \/ Q)
     ==> lbilin_on k p q
           (\G sf tf y u. (if P then E1 G sf tf y u else &0) +
                          (if Q then E2 G sf tf y u else &0))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `P:bool` THEN ASM_CASES_TAC `Q:bool` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ADD_RID; ETA_AX] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ADD_LID; ETA_AX] THEN ASM_REWRITE_TAC[]]);;

let GEOB_SUM_REGROUP2 = prove
 (`!i (x:num->real) (w:num->real).
     sum(0..SUC i) (\b. (if 1 <= b then x(b - 1) else &0) +
                        (if b <= i then w b else &0)) =
     sum(0..i) x + sum(0..i) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
      [MATCH_MP SUM_CLAUSES_LEFT (ARITH_RULE `0 <= SUC i`)] THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= 0)`; REAL_ADD_LID; ADD_CLAUSES] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1..SUC i) (\b. (x:num->real)(b - 1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
      REWRITE_TAC[ADD1] THEN
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o LAND_CONV)
        [ARITH_RULE `1 = 0 + 1`] THEN
      REWRITE_TAC[SUM_OFFSET; ADD_SUB; ETA_AX]];
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC i <= i)`; REAL_ADD_RID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[]]);;

let GEOB_LBILIN_ON_NABLA_ITER = prove
 (`!k p q (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q E
     ==> !i. ?Ls. (!a. a <= i ==> lbilin_on (k + i) (p + a) (q + (i - a)) (Ls a)) /\
                  !U G tf tg y u.
                     metric_field U G /\ y IN U /\
                     ltensor_field p U tf /\ ltensor_field q U tg /\
                     (!u. smooth_map_on U (\y. lift(tf y u))) /\
                     (!u. smooth_map_on U (\y. lift(tg y u)))
                     ==> lnabla_iter k i G (E G tf tg) y u =
                         sum(0..i) (\a. Ls a G (lnabla_iter p a G tf)
                                              (lnabla_iter q (i - a) G tg) y u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `\a:num. (E:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a <= 0 <=> a = 0`] THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_REFL];
      REWRITE_TAC[SUM_SING_NUMSEG; lnabla_iter; SUB_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN
    `Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "cls") (LABEL_TAC "eq"))) THEN
  SUBGOAL_THEN
   `!a. ?E1 E2. a <= i
                ==> lbilin_on ((k + i) + 1) ((p + a) + 1) (q + (i - a)) E1 /\
                    lbilin_on ((k + i) + 1) (p + a) ((q + (i - a)) + 1) E2 /\
                    !U (G:real^N->real^N^N) tf tg y u.
                       metric_field U G /\ y IN U /\
                       ltensor_field (p + a) U tf /\ ltensor_field (q + (i - a)) U tg /\
                       (!u. smooth_map_on U (\y. lift(tf y u))) /\
                       (!u. smooth_map_on U (\y. lift(tg y u)))
                       ==> lnabla (k + i) G
                             ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                                  (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                                a G tf tg) y u =
                           E1 G (lnabla (p + a) G tf) tg y u +
                           E2 G tf (lnabla (q + (i - a)) G tg) y u`
  MP_TAC THENL
   [X_GEN_TAC `a:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`k + i:num`; `p + a:num`; `q + (i - a):num`;
      `(Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) a`]
     RFA_LBILIN_ON_NABLA) THEN
    USE_THEN "cls" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `E1:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN
    `E2:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (LABEL_TAC "e12"))) THEN
  EXISTS_TAC
   `\b (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
      (tf:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N).
      (if 1 <= b then
         (E1:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (b - 1) G sf tf y u
       else &0) +
      (if b <= i then
         (E2:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) b G sf tf y u
       else &0)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `b:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC GEOB_LBILIN_ON_COND2 THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_IDX THEN
      MAP_EVERY EXISTS_TAC [`(k + i) + 1:num`; `(p + (b - 1)) + 1:num`; `q + (i - (b - 1)):num`] THEN
      CONJ_TAC THENL
       [USE_THEN "e12" (MP_TAC o SPEC `b - 1`) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[ETA_AX]];
        ASM_ARITH_TAC];
      DISCH_TAC THEN MATCH_MP_TAC RFA_LBILIN_ON_IDX THEN
      MAP_EVERY EXISTS_TAC [`(k + i) + 1:num`; `p + b:num`; `(q + (i - b)) + 1:num`] THEN
      CONJ_TAC THENL
       [USE_THEN "e12" (MP_TAC o SPEC `b:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN REWRITE_TAC[ETA_AX]];
        ASM_ARITH_TAC];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itf") THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tg:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itg") THEN
  REWRITE_TAC[lnabla_iter] THEN
  TRANS_TAC EQ_TRANS
   `lnabla (k + i) (G:real^N->real^N^N)
      (\z u. sum(0..i) (\a. (Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                              a G (lnabla_iter p a G tf) (lnabla_iter q (i - a) G tg) z u))
      y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "eq" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a <= i
        ==> ltensor_field (k + i) U
              ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                   (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                 a G (lnabla_iter p a G tf) (lnabla_iter q (i - a) G tg)) /\
            (!u. smooth_map_on U
                   (\y. lift(Ls a G (lnabla_iter p a G tf) (lnabla_iter q (i - a) G tg) y u)))`
  (LABEL_TAC "fld") THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    USE_THEN "cls" (MP_TAC o C MATCH_MP (ASSUME `a:num <= i`) o SPEC `a:num`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SMOOTH) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "itf" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "itg" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + i:num`; `G:real^N->real^N^N`;
    `\a. (Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
            (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
           a G (lnabla_iter p a G tf) (lnabla_iter q (i - a) G tg)`;
    `y:real^N`; `u:num->real^N`; `i:num`] RFA_LNABLA_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "fld" (MP_TAC o C MATCH_MP (ASSUME `a:num <= i`) o SPEC `a:num`) THEN
    SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!a. a <= i
        ==> lnabla (k + i) G
              ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                   (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                 a G (lnabla_iter p a G tf) (lnabla_iter q (i - a) G tg)) y u =
            (E1:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
              a G (lnabla_iter p (SUC a) G tf) (lnabla_iter q (i - a) G tg) y u +
            (E2:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
              a G (lnabla_iter p a G tf) (lnabla_iter q (SUC(i - a)) G tg) y u`
  (LABEL_TAC "term") THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN REWRITE_TAC[lnabla_iter] THEN
    USE_THEN "e12" (MP_TAC o C MATCH_MP (ASSUME `a:num <= i`) o SPEC `a:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "itf" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "itg" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(0..i) (\a. (E1:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                     a G (lnabla_iter p (SUC a) G tf) (lnabla_iter q (i - a) G tg) y u) +
    sum(0..i) (\a. (E2:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                      (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                     a G (lnabla_iter p a G tf) (lnabla_iter q (SUC(i - a)) G tg) y u)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "term" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`;
    `\a. (E1:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
           a G (lnabla_iter p (SUC a) G tf) (lnabla_iter q (i - a) G tg) y u`;
    `\a. (E2:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
           a G (lnabla_iter p a G tf) (lnabla_iter q (SUC(i - a)) G tg) y u`]
    GEOB_SUM_REGROUP2) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= b ==> SUC(b - 1) = b`;
               ARITH_RULE `1 <= b ==> i - (b - 1) = SUC i - b`;
               ARITH_RULE `b <= i ==> SUC(i - b) = SUC i - b`]);;

(* ========================================================================= *)
(* Partial sums, the norm of a difference and of a finite sum of tensors,    *)
(* comparison of the norms of G0 and G1 (G0/2 <= G1 <= 3 G0/2 when |G1 - G0| *)
(* <= 1/2), the bound |nabla_G0^j K| <= 2^(3+j) in G1 norms, and the norm of *)
(* nabla^j of geob_ins (Leibniz rule plus RFA_LBILIN_ON_NORM).               *)
(* ========================================================================= *)

let GEOB_SUM_MONO_LE = prove
 (`!(f:num->real) m n.
     m <= n /\ (!i. i <= n ==> &0 <= f i) ==> sum(0..m) f <= sum(0..n) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let GEOB_SUM_SHIFT_LE = prove
 (`!(f:num->real) n.
     (!i. i <= SUC n ==> &0 <= f i)
     ==> sum(0..n) (\i. f(i + 1)) <= sum(0..SUC n) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..SUC n) (f:num->real) = f 0 + sum(0..n) (\i. f(i + 1))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [MATCH_MP SUM_CLAUSES_LEFT (ARITH_RULE `0 <= SUC n`)] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`f:num->real`; `1`; `SUC n`] SUM_OFFSET_0) THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`; ARITH_RULE `SUC n - 1 = n`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let GEOB_LTNORM2_SUB_LE = prove
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

let GEOB_TENSOR_FIELD_SUM0 = prove
 (`!r U (Z:num->real^N->(num->real^N)->real) n.
     (!a. a <= n ==> ltensor_field r U (Z a))
     ==> ltensor_field r U (\z u. sum(0..n) (\a. Z a z u))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ARITH_RULE `a <= 0 <=> a = 0`; ETA_AX] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  MP_TAC(ISPECL [`r:num`; `U:real^N->bool`;
                 `\z u. sum(0..n) (\a. (Z:num->real^N->(num->real^N)->real) a z u)`;
                 `(Z:num->real^N->(num->real^N)->real) (SUC n)`] RFA_TENSOR_FIELD_ADD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let GEOB_LTNORM2_SUM_LE = prove
 (`!r U (G:real^N->real^N^N) (Z:num->real^N->(num->real^N)->real) y n.
     metric_field U G /\ y IN U /\ (!a. a <= n ==> ltensor_field r U (Z a))
     ==> ltnorm2 r G (\z u. sum(0..n) (\a. Z a z u)) y <=
         &2 pow n * sum(0..n) (\a. ltnorm2 r G (Z a) y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; real_pow; REAL_MUL_LID; ETA_AX; REAL_LE_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!a. a <= n ==> ltensor_field r U ((Z:num->real^N->(num->real^N)->real) a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ltensor_field r U ((Z:num->real^N->(num->real^N)->real) (SUC n))`
  ASSUME_TAC THENL [FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ARITH_TAC); ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 r (G:real^N->real^N^N)
      (\z u. sum(0..n) (\a. (Z:num->real^N->(num->real^N)->real) a z u) + Z (SUC n) z u) y <=
    &2 * ltnorm2 r G (\z u. sum(0..n) (\a. Z a z u)) y + &2 * ltnorm2 r G (Z (SUC n)) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z u. sum(0..n) (\a. (Z:num->real^N->(num->real^N)->real) a z u)`;
                   `(Z:num->real^N->(num->real^N)->real) (SUC n)`; `y:real^N`]
                  RFA_LTNORM2_ADD_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:num`; `U:real^N->bool`; `Z:num->real^N->(num->real^N)->real`;
                     `n:num`] GEOB_TENSOR_FIELD_SUM0) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; real_pow] THEN
  SUBGOAL_THEN `&1 <= &2 pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 r (G:real^N->real^N^N) ((Z:num->real^N->(num->real^N)->real) (SUC n)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&2 pow n - &1) *
          ltnorm2 r (G:real^N->real^N^N) ((Z:num->real^N->(num->real^N)->real) (SUC n)) y`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* G0 and G1 are comparable when lck_dist2 k G0 G1 y <= 1/4. *)

let GEOB_METRIC_COMPARE = prove
 (`!k s (G0:real^N->real^N^N) G1 y.
     metric_field s G0 /\ metric_field s G1 /\ y IN s /\ lck_dist2 k G0 G1 y <= &1 / &4
     ==> (!x. x dot (G0 y ** x) <= &2 * (x dot (G1 y ** x))) /\
         (!x. x dot (G1 y ** x) <= &3 / &2 * (x dot (G0 y ** x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 / &4) = &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. abs(a dot ((G1:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          &1 / &2 * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `&1 / &4`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 k (G0:real^N->real^N^N) G1 y` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:num`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G1:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G1:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `&1 / &2`] LRG_PERT_G) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  SUBGOAL_THEN `!x. x dot ((G0:real^N->real^N^N) y ** x) = norm((M:real^N^N) ** x) pow 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_FRAME_DOT THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^N` THENL
   [USE_THEN "G1" (MP_TAC o SPEC `x:real^N`) THEN REAL_ARITH_TAC;
    USE_THEN "G2" (MP_TAC o SPECL [`x:real^N`; `x:real^N`]) THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN REAL_ARITH_TAC]);;

let GEOB_NORM_COMPARE = prove
 (`!k s (G0:real^N->real^N^N) G1 y r Z.
     metric_field s G0 /\ metric_field s G1 /\ y IN s /\ lck_dist2 k G0 G1 y <= &1 / &4 /\
     ltensor_field r s Z
     ==> ltnorm2 r G1 Z y <= &2 pow r * ltnorm2 r G0 Z y /\
         ltnorm2 r G0 Z y <= (&3 / &2) pow r * ltnorm2 r G1 Z y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                 `y:real^N`] GEOB_METRIC_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The G0-derivatives of K, measured with G1. *)

let GEOB_KT_BOUND = prove
 (`!k s (G0:real^N->real^N^N) G1 y j.
     metric_field s G0 /\ metric_field s G1 /\ y IN s /\ lck_dist2 k G0 G1 y <= &1 / &4 /\
     j + 1 <= k
     ==> ltnorm2 (3 + j) G1 (lnabla_iter 3 j G0 (geob_kt G0 G1)) y <= &2 pow (3 + j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         GEOB_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_kt G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                 `y:real^N`; `3 + j`;
                 `lnabla_iter 3 j G0 (geob_kt G0 (G1:real^N->real^N^N))`]
         GEOB_NORM_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                 `j:num`; `y:real^N`] GEOB_KT_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `j + 1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `G1:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 + j + 1 = 3 + j`; GSYM geob_hd] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow (3 + j)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow (3 + j) *
              ltnorm2 (3 + j) G0 (lnabla_iter 3 j G0 (geob_kt G0 (G1:real^N->real^N^N))) y` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The norm of nabla^j of the insertion operator, by the Leibniz rule. *)

let GEOB_INS_ITER_BOUND = prove
 (`!m j. 1 <= m
     ==> ?cn. (!a. &0 <= cn a) /\
              !U (G:real^N->real^N^N) X K y.
                 metric_field U G /\ y IN U /\
                 ltensor_field m U X /\ (!u. smooth_map_on U (\z. lift(X z u))) /\
                 ltensor_field 3 U K /\ (!u. smooth_map_on U (\z. lift(K z u)))
                 ==> ltnorm2 ((m + 1) + j) G (lnabla_iter (m + 1) j G (geob_ins m G X K)) y <=
                     &2 pow j *
                     sum(0..j) (\a. cn a * ltnorm2 (m + a) G (lnabla_iter m a G X) y *
                                    ltnorm2 (3 + (j - a)) G (lnabla_iter 3 (j - a) G K) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `j:num` (MATCH_MP GEOB_LBILIN_ON_NABLA_ITER
    (MATCH_MP (INST_TYPE [`:N`,`:N`] GEOB_INS_LBILIN) (ASSUME `1 <= m`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN
    `Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "cls") (LABEL_TAC "eq"))) THEN
  SUBGOAL_THEN
   `!a. ?c. &0 <= c /\
            (a <= j
             ==> !U (G:real^N->real^N^N) tf tg y.
                   metric_field U G /\ y IN U /\
                   ltensor_field (m + a) U tf /\ ltensor_field (3 + (j - a)) U tg
                   ==> ltnorm2 ((m + 1) + j) G
                         ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                            a G tf tg) y <=
                       c * ltnorm2 (m + a) G tf y * ltnorm2 (3 + (j - a)) G tg y)`
  MP_TAC THENL
   [X_GEN_TAC `a:num` THEN ASM_CASES_TAC `a:num <= j` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(ISPECL
       [`(m + 1) + j`; `m + a:num`; `3 + (j - a):num`;
        `(Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) a`]
       RFA_LBILIN_ON_NORM) THEN
      USE_THEN "cls" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `cn:num->real` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itx") THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `K:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itk") THEN
  SUBGOAL_THEN
   `!a. a <= j
        ==> ltensor_field ((m + 1) + j) U
              ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                   (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                 a G (lnabla_iter m a G X) (lnabla_iter 3 (j - a) G K))`
  (LABEL_TAC "fld") THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    USE_THEN "cls" (MP_TAC o C MATCH_MP (ASSUME `a:num <= j`) o SPEC `a:num`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_SMOOTH) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                               `lnabla_iter m a G (X:real^N->(num->real^N)->real)`;
                               `lnabla_iter 3 (j - a) G (K:real^N->(num->real^N)->real)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "itx" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "itk" (fun th -> REWRITE_TAC[th]);
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ltnorm2 ((m + 1) + j) (G:real^N->real^N^N)
      (\z u. sum(0..j) (\a. (Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                              a G (lnabla_iter m a G X) (lnabla_iter 3 (j - a) G K) z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 pow j *
    sum(0..j) (\a. ltnorm2 ((m + 1) + j) (G:real^N->real^N^N)
                     ((Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
                        a G (lnabla_iter m a G X) (lnabla_iter 3 (j - a) G K)) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(m + 1) + j`; `U:real^N->bool`; `G:real^N->real^N^N`;
      `\a. (Ls:num->(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
             a G (lnabla_iter m a G X) (lnabla_iter 3 (j - a) G K)`;
      `y:real^N`; `j:num`] GEOB_LTNORM2_SUM_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fld" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  USE_THEN "nb" (MP_TAC o C MATCH_MP (ASSUME `a:num <= j`) o SPEC `a:num`) THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "itx" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "itk" (fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* G1-derivatives of a tensor field are bounded by its G0-derivatives (both  *)
(* measured with G1), uniformly in the order up to j (GEOB_R_DERIV).  Step:  *)
(* nabla_G1^(j+1) X = nabla_G1^j (nabla_G0 X) - nabla_G1^j (geob_ins G1 X K) *)
(* (GEOB_R_SPLIT); the first term by the induction hypothesis at rank m + 1, *)
(* the second by the Leibniz rule and the induction hypothesis for X and for *)
(* K (whose G0-derivatives are bounded by GEOB_KT_BOUND); the arithmetic is  *)
(* GEOB_R_ARITH.                                                             *)
(* ========================================================================= *)

let GEOB_R_SPLIT = prove
 (`!m j s (G0:real^N->real^N^N) G1 y X.
     1 <= m /\ metric_field s G0 /\ metric_field s G1 /\ y IN s /\
     ltensor_field m s X /\ (!u. smooth_map_on s (\z. lift(X z u)))
     ==> ltnorm2 (m + SUC j) G1 (lnabla_iter m (SUC j) G1 X) y <=
         &2 * ltnorm2 ((m + 1) + j) G1 (lnabla_iter (m + 1) j G1 (lnabla m G0 X)) y +
         &2 * ltnorm2 ((m + 1) + j) G1
                (lnabla_iter (m + 1) j G1 (geob_ins m G1 X (geob_kt G0 G1))) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         GEOB_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP RFA_LBILIN_ON_SMOOTH
    (MATCH_MP (INST_TYPE [`:N`,`:N`] GEOB_INS_LBILIN) (ASSUME `1 <= m`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `G1:real^N->real^N^N`;
                             `X:real^N->(num->real^N)->real`;
                             `geob_kt G0 (G1:real^N->real^N^N)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `lnabla m (G0:real^N->real^N^N) X`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `geob_ins m G1 X (geob_kt G0 (G1:real^N->real^N^N))`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `m + SUC j = (m + 1) + j`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `ltnorm2 ((m + 1) + j) (G1:real^N->real^N^N)
      (\z u. lnabla_iter (m + 1) j G1 (lnabla m (G0:real^N->real^N^N) X) z u -
             lnabla_iter (m + 1) j G1 (geob_ins m G1 X (geob_kt G0 G1)) z u) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `u:num->real^N` THEN
    REWRITE_TAC[ADD1; GSYM RFA_LNABLA_ITER_SHIFT] THEN
    SUBGOAL_THEN
     `!z u. z IN s
            ==> lnabla m (G1:real^N->real^N^N) X z u =
                &1 * lnabla m (G0:real^N->real^N^N) X z u +
                --(&1) * geob_ins m G1 X (geob_kt G0 G1) z u`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G1:real^N->real^N^N`; `X:real^N->(num->real^N)->real`;
                     `z:real^N`; `u:num->real^N`] GEOB_CONN_DIFF) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m + 1`; `G1:real^N->real^N^N`; `G1:real^N->real^N^N`;
                   `lnabla m (G1:real^N->real^N^N) X`;
                   `\z u. &1 * lnabla m (G0:real^N->real^N^N) X z u +
                          --(&1) * geob_ins m (G1:real^N->real^N^N) X (geob_kt G0 G1) z u`;
                   `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                   `lnabla m (G0:real^N->real^N^N) X`;
                   `geob_ins m (G1:real^N->real^N^N) X (geob_kt G0 G1)`;
                   `&1`; `--(&1)`] LRG_LNABLA_ITER_LINCOMB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(m + 1) + j`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `lnabla_iter (m + 1) j G1 (lnabla m (G0:real^N->real^N^N) X)`;
                 `lnabla_iter (m + 1) j (G1:real^N->real^N^N)
                    (geob_ins m G1 X (geob_kt (G0:real^N->real^N^N) G1))`;
                 `y:real^N`] GEOB_LTNORM2_SUB_LE) THEN
  ASM_REWRITE_TAC[]);;

let GEOB_R_ARITH = prove
 (`!j N A B SA S P Cm Cm1 C3 Q (cn:num->real) (x:num->real) (kk:num->real).
     &0 <= Cm /\ &0 <= Cm1 /\ &0 <= C3 /\ &0 <= Q /\ &0 <= P /\ &0 <= S /\
     (!a. &0 <= cn a) /\ (!a. a <= j ==> &0 <= x a /\ x a <= Cm * S) /\
     (!a. a <= j ==> &0 <= kk a /\ kk a <= C3 * Q) /\
     N <= &2 * A + &2 * B /\ A <= Cm1 * SA /\ SA <= S /\
     B <= P * sum(0..j) (\a. cn a * x a * kk a)
     ==> N <= (Cm + (&2 * Cm1 + &2 * P * sum(0..j) (\a. cn a * Cm * (C3 * Q)))) * S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..j) (\a. (cn:num->real) a * x a * kk a) <=
    sum(0..j) (\a. cn a * Cm * (C3 * Q)) * S`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `((cn:num->real) a * Cm * (C3 * Q)) * S = cn a * ((Cm * S) * (C3 * Q))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cm1 * SA <= Cm1 * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `P * sum(0..j) (\a. (cn:num->real) a * x a * kk a) <=
    P * (sum(0..j) (\a. cn a * Cm * (C3 * Q)) * S)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cm * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let GEOB_R_DERIV = prove
 (`!k j. j <= k
     ==> !m. 1 <= m
         ==> ?C. &0 <= C /\
             !b s (G0:real^N->real^N^N) G1 y X.
               b <= j /\
               metric_field s G0 /\ metric_field s G1 /\ y IN s /\
               lck_dist2 k G0 G1 y <= &1 / &4 /\
               ltensor_field m s X /\ (!u. smooth_map_on s (\z. lift(X z u)))
               ==> ltnorm2 (m + b) G1 (lnabla_iter m b G1 X) y <=
                   C * sum(0..b) (\i. ltnorm2 (m + i) G1 (lnabla_iter m i G0 X) y)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_POS; ARITH_RULE `b <= 0 <=> b = 0`] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG; lnabla_iter; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(LABEL_TAC "IH")] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  USE_THEN "IH" (MP_TAC o C MATCH_MP (ASSUME `1 <= m`) o SPEC `m:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rm"))) THEN
  USE_THEN "IH" (MP_TAC o SPEC `m + 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cm1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rm1"))) THEN
  USE_THEN "IH" (MP_TAC o SPEC `3`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R3"))) THEN
  MP_TAC(SPECL [`m:num`; `j:num`] (INST_TYPE [`:N`,`:N`] GEOB_INS_ITER_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cn:num->real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INS"))) THEN
  SUBGOAL_THEN `&0 <= sum(0..j) (\i. &2 pow (3 + i))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &2 * Cm1 + &2 * &2 pow j *
          sum(0..j) (\a. (cn:num->real) a * Cm * (C3 * sum(0..j) (\i. &2 pow (3 + i))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Cm + (&2 * Cm1 + &2 * &2 pow j *
                    sum(0..j) (\a. (cn:num->real) a * Cm *
                                   (C3 * sum(0..j) (\i. &2 pow (3 + i)))))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                       `G1:real^N->real^N^N`; `y:real^N`;
                       `X:real^N->(num->real^N)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it0") THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it1") THEN
  SUBGOAL_THEN
   `!i. &0 <= ltnorm2 (m + i) (G1:real^N->real^N^N) (lnabla_iter m i G0 X) y`
  (LABEL_TAC "pos") THENL
   [GEN_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "it0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. &0 <= sum(0..c) (\i. ltnorm2 (m + i) (G1:real^N->real^N^N)
                               (lnabla_iter m i G0 X) y)`
  (LABEL_TAC "spos") THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ASM_CASES_TAC `b:num <= j` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cm * sum(0..b) (\i. ltnorm2 (m + i) (G1:real^N->real^N^N)
                                      (lnabla_iter m i G0 X) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "Rm" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN USE_THEN "spos" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b = SUC j` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `j:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `G1:real^N->real^N^N`; `y:real^N`; `X:real^N->(num->real^N)->real`]
         GEOB_R_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "Rm1" (MP_TAC o SPECL
    [`j:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
     `y:real^N`; `lnabla m (G0:real^N->real^N^N) X`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `sum(0..j) (\i. ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N)
                     (lnabla_iter (m + 1) i G0 (lnabla m G0 X)) y) <=
    sum(0..SUC j) (\i. ltnorm2 (m + i) G1 (lnabla_iter m i G0 X) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[RFA_LNABLA_ITER_SHIFT; ARITH_RULE `(m + 1) + i = m + (i + 1)`] THEN
    MP_TAC(ISPECL [`\i. ltnorm2 (m + i) (G1:real^N->real^N^N) (lnabla_iter m i G0 X) y`;
                   `j:num`] GEOB_SUM_SHIFT_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         GEOB_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `geob_kt G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itk1") THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_kt G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itk0") THEN
  USE_THEN "INS" (MP_TAC o SPECL
    [`s:real^N->bool`; `G1:real^N->real^N^N`; `X:real^N->(num->real^N)->real`;
     `geob_kt G0 (G1:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`j:num`;
    `ltnorm2 (m + SUC j) (G1:real^N->real^N^N) (lnabla_iter m (SUC j) G1 X) y`;
    `ltnorm2 ((m + 1) + j) (G1:real^N->real^N^N)
       (lnabla_iter (m + 1) j G1 (lnabla m (G0:real^N->real^N^N) X)) y`;
    `ltnorm2 ((m + 1) + j) (G1:real^N->real^N^N)
       (lnabla_iter (m + 1) j G1 (geob_ins m G1 X (geob_kt (G0:real^N->real^N^N) G1))) y`;
    `sum(0..j) (\i. ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N)
                      (lnabla_iter (m + 1) i G0 (lnabla m G0 X)) y)`;
    `sum(0..SUC j) (\i. ltnorm2 (m + i) (G1:real^N->real^N^N) (lnabla_iter m i G0 X) y)`;
    `&2 pow j`; `Cm:real`; `Cm1:real`; `C3:real`;
    `sum(0..j) (\i. &2 pow (3 + i))`; `cn:num->real`;
    `\a. ltnorm2 (m + a) (G1:real^N->real^N^N) (lnabla_iter m a G1 X) y`;
    `\a. ltnorm2 (3 + (j - a)) (G1:real^N->real^N^N)
           (lnabla_iter 3 (j - a) G1 (geob_kt (G0:real^N->real^N^N) G1)) y`]
   GEOB_R_ARITH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "it1" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cm * sum(0..a) (\i. ltnorm2 (m + i) (G1:real^N->real^N^N)
                                      (lnabla_iter m i G0 X) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "Rm" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOB_SUM_MONO_LE THEN USE_THEN "pos" (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "itk1" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C3 * sum(0..j - a) (\i. ltnorm2 (3 + i) (G1:real^N->real^N^N)
                                          (lnabla_iter 3 i G0 (geob_kt G0 G1)) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "R3" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..j - a) (\i. &2 pow (3 + i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC GEOB_KT_BOUND THEN EXISTS_TAC `k:num` THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC GEOB_SUM_MONO_LE THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* G0-derivatives of a tensor field are bounded by its G1-derivatives,       *)
(* measured with G1 (GEOB_F_DERIV).  Step: on s, nabla_G0 X = Y := nabla_G1  *)
(* X + geob_ins G1 X K, so nabla_G0^(j+1) X = nabla_G0^j Y; the induction    *)
(* hypothesis at rank m + 1 bounds it by the nabla_G1^i Y, and nabla_G1^i Y  *)
(* = nabla_G1^(i+1) X + nabla_G1^i (ins), the latter bounded by the Leibniz  *)
(* rule and GEOB_R_DERIV for K (GEOB_F_TERM).                                *)
(* ========================================================================= *)

let GEOB_SUMMAND_LE = prove
 (`!(f:num->real) a n. a <= n /\ (!i. i <= n ==> &0 <= f i) ==> f a <= sum(0..n) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `sum(0..n) (f:num->real)`; `0..n`] SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[]]);;

let GEOB_F_TERM = prove
 (`!m i j s (G0:real^N->real^N^N) G1 y X (cn:num->real) KB.
     1 <= m /\ i <= j /\ metric_field s G0 /\ metric_field s G1 /\ y IN s /\
     ltensor_field m s X /\ (!u. smooth_map_on s (\z. lift(X z u))) /\
     (!a. &0 <= cn a) /\ &0 <= KB /\
     (!b. b <= j
          ==> ltnorm2 (3 + b) G1 (lnabla_iter 3 b G1 (geob_kt G0 G1)) y <= KB) /\
     ltnorm2 ((m + 1) + i) G1
       (lnabla_iter (m + 1) i G1 (geob_ins m G1 X (geob_kt G0 G1))) y <=
     &2 pow i *
     sum(0..i) (\a. cn a * ltnorm2 (m + a) G1 (lnabla_iter m a G1 X) y *
                    ltnorm2 (3 + (i - a)) G1 (lnabla_iter 3 (i - a) G1 (geob_kt G0 G1)) y)
     ==> ltnorm2 ((m + 1) + i) G1
           (lnabla_iter (m + 1) i G1
              (\z u. &1 * lnabla m G1 X z u + &1 * geob_ins m G1 X (geob_kt G0 G1) z u)) y <=
         (&2 + &2 * &2 pow i * sum(0..i) (\a. cn a * KB)) *
         sum(0..SUC j) (\l. ltnorm2 (m + l) G1 (lnabla_iter m l G1 X) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         GEOB_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP RFA_LBILIN_ON_SMOOTH
    (MATCH_MP (INST_TYPE [`:N`,`:N`] GEOB_INS_LBILIN) (ASSUME `1 <= m`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `G1:real^N->real^N^N`;
                             `X:real^N->(num->real^N)->real`;
                             `geob_kt G0 (G1:real^N->real^N^N)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itx") THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `geob_kt G0 (G1:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "itk") THEN
  MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `geob_ins m G1 X (geob_kt G0 (G1:real^N->real^N^N))`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field ((m + 1) + i) s (lnabla_iter m (i + 1) (G1:real^N->real^N^N) X)`
  ASSUME_TAC THENL
   [USE_THEN "itx" (MP_TAC o CONJUNCT1 o SPEC `i + 1`) THEN
    REWRITE_TAC[ARITH_RULE `m + i + 1 = (m + 1) + i`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. &0 <= ltnorm2 (m + l) (G1:real^N->real^N^N) (lnabla_iter m l G1 X) y`
  (LABEL_TAC "pos") THENL
   [GEN_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "itx" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l <= SUC j
        ==> ltnorm2 (m + l) (G1:real^N->real^N^N) (lnabla_iter m l G1 X) y <=
            sum(0..SUC j) (\l. ltnorm2 (m + l) G1 (lnabla_iter m l G1 X) y)`
  (LABEL_TAC "summ") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\l. ltnorm2 (m + l) (G1:real^N->real^N^N) (lnabla_iter m l G1 X) y`;
                   `l:num`; `SUC j`] GEOB_SUMMAND_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. lnabla_iter (m + 1) i G1
          (\z u. &1 * lnabla m (G1:real^N->real^N^N) X z u +
                 &1 * geob_ins m G1 X (geob_kt G0 G1) z u) y u =
        lnabla_iter m (i + 1) G1 X y u +
        lnabla_iter (m + 1) i G1 (geob_ins m G1 X (geob_kt G0 G1)) y u`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                   `lnabla m (G1:real^N->real^N^N) X`;
                   `geob_ins m (G1:real^N->real^N^N) X (geob_kt G0 G1)`;
                   `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[RFA_LNABLA_ITER_SHIFT; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N) (lnabla_iter m (i + 1) G1 X) y <=
    sum(0..SUC j) (\l. ltnorm2 (m + l) G1 (lnabla_iter m l G1 X) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(m + 1) + i = m + i + 1`] THEN
    USE_THEN "summ" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..i) (\a. (cn:num->real) a *
                   ltnorm2 (m + a) (G1:real^N->real^N^N) (lnabla_iter m a G1 X) y *
                   ltnorm2 (3 + (i - a)) G1 (lnabla_iter 3 (i - a) G1 (geob_kt G0 G1)) y) <=
    sum(0..i) (\a. cn a * KB) *
    sum(0..SUC j) (\l. ltnorm2 (m + l) G1 (lnabla_iter m l G1 X) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(cn:num->real) a *
                (sum(0..SUC j) (\l. ltnorm2 (m + l) (G1:real^N->real^N^N)
                                      (lnabla_iter m l G1 X) y) * KB)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
        USE_THEN "summ" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "itk" (fun th -> REWRITE_TAC[th]);
        UNDISCH_TAC
         `!b. b <= j
              ==> ltnorm2 (3 + b) (G1:real^N->real^N^N)
                    (lnabla_iter 3 b G1 (geob_kt G0 G1)) y <= KB` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow i *
    sum(0..i) (\a. (cn:num->real) a *
                   ltnorm2 (m + a) (G1:real^N->real^N^N) (lnabla_iter m a G1 X) y *
                   ltnorm2 (3 + (i - a)) G1 (lnabla_iter 3 (i - a) G1 (geob_kt G0 G1)) y) <=
    &2 pow i *
    (sum(0..i) (\a. cn a * KB) *
     sum(0..SUC j) (\l. ltnorm2 (m + l) G1 (lnabla_iter m l G1 X) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N) (lnabla_iter m (i + 1) G1 X) y +
    &2 * ltnorm2 ((m + 1) + i) G1
           (lnabla_iter (m + 1) i G1 (geob_ins m G1 X (geob_kt G0 G1))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N)
        (\z u. lnabla_iter m (i + 1) G1 X z u +
               lnabla_iter (m + 1) i G1 (geob_ins m G1 X (geob_kt G0 G1)) z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`(m + 1) + i`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                     `lnabla_iter m (i + 1) (G1:real^N->real^N^N) X`;
                     `lnabla_iter (m + 1) i (G1:real^N->real^N^N)
                        (geob_ins m G1 X (geob_kt G0 G1))`;
                     `y:real^N`] RFA_LTNORM2_ADD_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]];
    ASM_REAL_ARITH_TAC]);;

let GEOB_F_DERIV = prove
 (`!k j. j <= k
     ==> !m. 1 <= m
         ==> ?C. &0 <= C /\
             !s (G0:real^N->real^N^N) G1 y X.
               metric_field s G0 /\ metric_field s G1 /\ y IN s /\
               lck_dist2 k G0 G1 y <= &1 / &4 /\
               ltensor_field m s X /\ (!u. smooth_map_on s (\z. lift(X z u)))
               ==> ltnorm2 (m + j) G1 (lnabla_iter m j G0 X) y <=
                   C * sum(0..j) (\i. ltnorm2 (m + i) G1 (lnabla_iter m i G1 X) y)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUM_SING_NUMSEG; lnabla_iter; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(LABEL_TAC "IH")] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  USE_THEN "IH" (MP_TAC o SPEC `m + 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F1"))) THEN
  MP_TAC(SPECL [`k:num`; `j:num`] (INST_TYPE [`:N`,`:N`] GEOB_R_DERIV)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `3`)] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R3"))) THEN
  MP_TAC(GEN `i:num` (MATCH_MP (SPECL [`m:num`; `i:num`]
    (INST_TYPE [`:N`,`:N`] GEOB_INS_ITER_BOUND)) (ASSUME `1 <= m`))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `cnf:num->num->real` (LABEL_TAC "INS")) THEN
  SUBGOAL_THEN `&0 <= sum(0..j) (\l. &2 pow (3 + l))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C3 * sum(0..j) (\l. &2 pow (3 + l))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC
   `C1 * sum(0..j) (\i. &2 + &2 * &2 pow i *
                         sum(0..i) (\a. (cnf:num->num->real) i a *
                                        (C3 * sum(0..j) (\l. &2 pow (3 + l)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "INS" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `i:num` th)]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                       `y:real^N`; `X:real^N->(num->real^N)->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         GEOB_KT_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP RFA_LBILIN_ON_SMOOTH
    (MATCH_MP (INST_TYPE [`:N`,`:N`] GEOB_INS_LBILIN) (ASSUME `1 <= m`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `G1:real^N->real^N^N`;
                             `X:real^N->(num->real^N)->real`;
                             `geob_kt G0 (G1:real^N->real^N^N)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m + 1`; `s:real^N->bool`; `lnabla m (G1:real^N->real^N^N) X`;
                 `geob_ins m (G1:real^N->real^N^N) X (geob_kt G0 G1)`; `&1`; `&1`]
         LRG_TENSOR_FIELD_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z u. z IN s
          ==> lnabla m (G0:real^N->real^N^N) X z u =
              &1 * lnabla m G1 X z u + &1 * geob_ins m G1 X (geob_kt G0 G1) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC GEOB_CONN_DIFF THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 (m + SUC j) (G1:real^N->real^N^N) (lnabla_iter m (SUC j) G0 X) y =
    ltnorm2 ((m + 1) + j) G1
      (lnabla_iter (m + 1) j G0
         (\z u. &1 * lnabla m G1 X z u + &1 * geob_ins m G1 X (geob_kt G0 G1) z u)) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `m + SUC j = (m + 1) + j`] THEN
    MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN X_GEN_TAC `u:num->real^N` THEN
    REWRITE_TAC[ADD1; GSYM RFA_LNABLA_ITER_SHIFT] THEN
    MP_TAC(ISPECL [`m + 1`; `G0:real^N->real^N^N`; `G0:real^N->real^N^N`;
                   `lnabla m (G0:real^N->real^N^N) X`;
                   `\z u. &1 * lnabla m (G1:real^N->real^N^N) X z u +
                          &1 * geob_ins m G1 X (geob_kt (G0:real^N->real^N^N) G1) z u`;
                   `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "F1" (MP_TAC o SPECL
    [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`; `y:real^N`;
     `\z u. &1 * lnabla m (G1:real^N->real^N^N) X z u +
            &1 * geob_ins m G1 X (geob_kt (G0:real^N->real^N^N) G1) z u`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!b. b <= j
        ==> ltnorm2 (3 + b) (G1:real^N->real^N^N) (lnabla_iter 3 b G1 (geob_kt G0 G1)) y <=
            C3 * sum(0..j) (\l. &2 pow (3 + l))`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C3 * sum(0..b) (\i. ltnorm2 (3 + i) (G1:real^N->real^N^N)
                                      (lnabla_iter 3 i G0 (geob_kt G0 G1)) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "R3" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..b) (\l. &2 pow (3 + l))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC GEOB_KT_BOUND THEN MAP_EVERY EXISTS_TAC [`k:num`; `s:real^N->bool`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC GEOB_SUM_MONO_LE THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `C1 * sum(0..j) (\i. ltnorm2 ((m + 1) + i) (G1:real^N->real^N^N)
                          (lnabla_iter (m + 1) i G1
                             (\z u. &1 * lnabla m G1 X z u +
                                    &1 * geob_ins m G1 X (geob_kt G0 G1) z u)) y)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`m:num`; `i:num`; `j:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `G1:real^N->real^N^N`; `y:real^N`; `X:real^N->(num->real^N)->real`;
                 `(cnf:num->num->real) i`; `C3 * sum(0..j) (\l. &2 pow (3 + l))`]
         GEOB_F_TERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "INS" (MP_TAC o SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th])
      (MP_TAC o SPECL [`s:real^N->bool`; `G1:real^N->real^N^N`;
                       `X:real^N->(num->real^N)->real`;
                       `geob_kt G0 (G1:real^N->real^N^N)`; `y:real^N`])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* LRG_CK_BASE_CHANGE, the body of P2B_REQ_LRG_BASE_STATEMENT (pc_p2b_defs   *)
(* S9).  With T = G2 - G1 = (G0 + G2 - G1) - G0: for l <= k,                 *)
(* |nabla_G0^l T|^2_G0 <= (3/2)^(2+l) |nabla_G0^l T|^2_G1 (GEOB_NORM_COMPARE)*)
(* <= (3/2)^(2+l) C_l sum_(i<=l) |nabla_G1^i T|^2_G1 (GEOB_F_DERIV at rank  *)
(* 2), and the inner sums are at most lck_dist2 k G1 G2 y.                  *)
(* ========================================================================= *)

let GEOB_CK_BASE_N = prove
 (`!k. ?M. &0 <= M /\
      !s (G0:real^N->real^N^N) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!j. ?C. j <= k
            ==> &0 <= C /\
                !s (G0:real^N->real^N^N) G1 y X.
                  metric_field s G0 /\ metric_field s G1 /\ y IN s /\
                  lck_dist2 k G0 G1 y <= &1 / &4 /\
                  ltensor_field 2 s X /\ (!u. smooth_map_on s (\z. lift(X z u)))
                  ==> ltnorm2 (2 + j) G1 (lnabla_iter 2 j G0 X) y <=
                      C * sum(0..j) (\i. ltnorm2 (2 + i) G1 (lnabla_iter 2 i G1 X) y)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `j:num`] GEOB_F_DERIV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `CF:num->real` (LABEL_TAC "CF")) THEN
  EXISTS_TAC `sum(0..k) (\j. (&3 / &2) pow (2 + j) * CF j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      USE_THEN "CF" (MP_TAC o C MATCH_MP (ASSUME `j:num <= k`) o SPEC `j:num`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                       `G2:real^N->real^N^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G2 z - G1 z) z u - lmetric2 G0 z u) =
    geob_hd G1 G2`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geob_hd; lmetric2] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM geob_hd] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
         GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G1 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it0") THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G1:real^N->real^N^N`;
                 `geob_hd G1 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it1") THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 / &2) pow (2 + j) *
              ltnorm2 (2 + j) (G1:real^N->real^N^N) (lnabla_iter 2 j G0 (geob_hd G1 G2)) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                   `y:real^N`; `2 + j`;
                   `lnabla_iter 2 j G0 (geob_hd G1 (G2:real^N->real^N^N))`]
           GEOB_NORM_COMPARE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "it0" (fun th -> REWRITE_TAC[th]); SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "CF" (MP_TAC o C MATCH_MP (ASSUME `j:num <= k`) o SPEC `j:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                    `y:real^N`; `geob_hd G1 (G2:real^N->real^N^N)`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CF j * sum(0..j) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                                     (lnabla_iter 2 i G1 (geob_hd G1 G2)) y)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GEOB_SUM_MONO_LE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "it1" (fun th -> REWRITE_TAC[th]));;

let LRG_CK_BASE_CHANGE = prove
 (`!k. ?M. &0 <= M /\
      !s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y`,
  MATCH_ACCEPT_TAC GEOB_CK_BASE_N);;

