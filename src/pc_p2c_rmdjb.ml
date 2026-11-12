(* ========================================================================= *)
(* Unit pc_p2c_rmdjb (Part 2C, shared): bounds on |nabla^j Rm|^2             *)
(* (lrm_deriv_norm2 j) for families of metric fields on an open set of R^N:  *)
(* from bounds on the coordinate jets of order j + 2 and a uniform lower     *)
(* bound of the metrics (P2CJ_RMD2_FROM_JB), and from C^m closeness to a     *)
(* fixed metric field on a compact set, m >= j + 2 (P2CJ_JB_FROM_LCK,        *)
(* P2CJ_RMD2_FROM_LCK).  Built on the jet bound calculus rfa_jb of           *)
(* pc_rfa_r1: Christoffel symbols, the Riemann tensor, lrm4 and its          *)
(* covariant derivatives in coordinates, then the tensor norms.              *)
(* ========================================================================= *)

needs "src/pc_p2c_flham.ml";;
needs "src/pc_p3_s14jet.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Jets of the Christoffel symbols of a finite order from jets               *)
(* of the metric of one order more (the finite-order form of               *)
(* P2CH_CHRIST_JB), of their first derivatives, of the Riemann tensor and   *)
(* of lrm4 in coordinates.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2CJ_COMPONENTWISE = prove
 (`!(f:real^M->real^N) x j.
     linear f /\ 1 <= j /\ j <= dimindex(:N)
     ==> f x$j = sum(1..dimindex(:M)) (\i. x$i * f(basis i)$j)`,
  MESON_TAC[LINEAR_COMPONENTWISE_EXPANSION]);;

let P2CJ_CHRIST_JB_FIN = prove
 (`!Js V K (G:real->real^N->real^N^N) Lm M.
     open V /\ K SUBSET V /\ &0 <= Lm /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (G t y ** v))) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K (SUC M) (\t z. G t z$p$q))
     ==> !m. m <= M
             ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                         1 <= s /\ s <= dimindex(:N)
                         ==> rfa_jb Js V K m
                               (\t z. (christoffel (G t) z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m c p q. m <= M /\ 1 <= c /\ c <= dimindex(:N) /\ 1 <= p /\ p <= dimindex(:N) /\
              1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. (mderiv ((G:real->real^N->real^N^N) t) z
                                                 (basis c))$p$q)`
  (LABEL_TAC "d1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
    EXISTS_TAC `rfa_pd c (\t z. (G:real->real^N->real^N^N) t z$p$q)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[rfa_pd] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                     `c:num`; `p:num`; `q:num`] PDE_JG_PARTIAL) THEN
      ASM_SIMP_TAC[pde_jd1; LIFT_DROP];
      MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                     `\t z. (G:real->real^N->real^N^N) t z$p$q`] RFA_JB_SUC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC M` THEN ASM_SIMP_TAC[LE_SUC];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `c:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m <= M /\
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> rfa_jb Js V K m (\t z. matrix_inv((G:real->real^N->real^N^N) t z)$p$q))
        ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                    1 <= s /\ s <= dimindex(:N)
                    ==> rfa_jb Js V K m
                          (\t z. (christoffel (G t) z (basis i) (basis j))$s)`
  (LABEL_TAC "step") THENL
   [GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
    EXISTS_TAC
     `\t z. sum(1..dimindex(:N))
              (\k. matrix_inv((G:real->real^N->real^N^N) t z)$s$k * inv(&2) *
                   ((mderiv (G t) z (basis i))$k$j + (mderiv (G t) z (basis j))$k$i -
                    (mderiv (G t) z (basis k))$i$j))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[PDE_CHR_JET; pde_jchr; pde_jgi; pde_jd1];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_JB_MUL THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFA_JB_CMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m p q. m <= M /\ 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. matrix_inv((G:real->real^N->real^N^N) t z)$p$q)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                     `G:real->real^N->real^N^N`; `Lm:real`] RFA_R1_GINV0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                   `G:real->real^N->real^N^N`] RFA_JB_GINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                       `G:real->real^N->real^N^N`; `Lm:real`] RFA_R1_GINV0) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "step" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      DISCH_THEN(MP_TAC o SPECL [`SUC m`; `p:num`; `q:num`]) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC m <= m + 1`]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

(* Jets of the first derivatives of the Christoffel symbols. *)

let P2CJ_DCHR_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) m i a b k.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
     rfa_jb Js V K (SUC m) (\t z. (christoffel (G t) z (basis a) (basis b))$k)
     ==> rfa_jb Js V K m
           (\t z. (frechet_derivative (\z. christoffel (G t) z (basis a) (basis b)) (at z)
                                      (basis i))$k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `rfa_pd i (\t z. (christoffel ((G:real->real^N->real^N^N) t) z
                                          (basis a) (basis b))$k)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[rfa_pd; partial_derivative] THEN
    MP_TAC(ISPECL [`\z. christoffel ((G:real->real^N->real^N^N) t) z (basis a) (basis b)`;
                   `z:real^N`; `k:num`] FRECHET_DERIVATIVE_LIFT_VECTOR_COMPONENT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
      EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]];
    MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                   `\t z. (christoffel ((G:real->real^N->real^N^N) t) z
                                       (basis a) (basis b))$k`] RFA_JB_SUC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* Jets of the components of the Riemann tensor. *)

let P2CJ_RIEM_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) m a b c k.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K (SUC m) (\t z. (christoffel (G t) z (basis i) (basis j))$s)) /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= c /\ c <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
     ==> rfa_jb Js V K m (\t z. (lriemann (G t) z (basis a) (basis b) (basis c))$k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
            1 <= s /\ s <= dimindex(:N)
            ==> rfa_jb Js V K m
                  (\t z. (christoffel ((G:real->real^N->real^N^N) t) z (basis i) (basis j))$s)`
  (LABEL_TAC "c0") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= SUC m`];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t z. ((frechet_derivative (\z. christoffel ((G:real->real^N->real^N^N) t) z
                                            (basis b) (basis c)) (at z) (basis a))$k -
           (frechet_derivative (\z. christoffel (G t) z (basis a) (basis c))
                               (at z) (basis b))$k) +
          (sum(1..dimindex(:N)) (\r. (christoffel (G t) z (basis b) (basis c))$r *
                                    (christoffel (G t) z (basis a) (basis r))$k) -
           sum(1..dimindex(:N)) (\r. (christoffel (G t) z (basis a) (basis c))$r *
                                    (christoffel (G t) z (basis b) (basis r))$k))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`]
                  LRG_CHRISTOFFEL_LINEAR) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[lriemann; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    SUBGOAL_THEN
     `(christoffel ((G:real->real^N->real^N^N) t) z (basis a)
                   (christoffel (G t) z (basis b) (basis c)))$k =
      sum(1..dimindex(:N)) (\r. (christoffel (G t) z (basis b) (basis c))$r *
                                (christoffel (G t) z (basis a) (basis r))$k) /\
      (christoffel (G t) z (basis b) (christoffel (G t) z (basis a) (basis c)))$k =
      sum(1..dimindex(:N)) (\r. (christoffel (G t) z (basis a) (basis c))$r *
                                (christoffel (G t) z (basis b) (basis r))$k)`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THEN MATCH_MP_TAC P2CJ_COMPONENTWISE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CJ_DCHR_JB THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2CJ_DCHR_JB THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Jets of the components of lrm4. *)

let P2CJ_LRM4_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) m al.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. G t z$p$q)) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K (SUC m) (\t z. (christoffel (G t) z (basis i) (basis j))$s)) /\
     al IN index_tuples 4 (:N)
     ==> rfa_jb Js V K m (\t z. lrm4 (G t) z (\r. basis(al r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. 1 <= r /\ r <= 4 ==> 1 <= (al:num->num) r /\ al r <= dimindex(:N)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(al:num->num) IN index_tuples 4 (:N)` THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(1 <= (al:num->num) 1 /\ al 1 <= dimindex(:N)) /\ (1 <= al 2 /\ al 2 <= dimindex(:N)) /\
    (1 <= al 3 /\ al 3 <= dimindex(:N)) /\ (1 <= al 4 /\ al 4 <= dimindex(:N))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    MESON_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 4 /\ 1 <= 2 /\ 2 <= 4 /\ 1 <= 3 /\ 3 <= 4 /\ 4 <= 4`];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t z. sum(1..dimindex(:N))
            (\q. (G:real->real^N->real^N^N) t z$(al 3)$q *
                 (lriemann (G t) z (basis(al 1)) (basis(al 2)) (basis(al 4)))$q)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[lrm4] THEN ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[dot];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RFA_JB_MUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC P2CJ_RIEM_JB THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Jets of the components of a covariant derivative, from jets              *)
(* of the components of the tensor of one order more and of the Christoffel *)
(* symbols (RFA_PD_TENSOR_COMP solved for the covariant derivative), and by *)
(* induction the jets of the components of nabla^l lrm4.                     *)
(* ------------------------------------------------------------------------- *)

let P2CJ_LNABLA_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) k (Tf:real->real^N->(num->real^N)->real) m.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!t. t IN Js ==> ltensor_field k V (Tf t) /\ (!u. smooth_map_on V (\y. lift(Tf t y u)))) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. (christoffel (G t) z (basis i) (basis j))$s)) /\
     (!al. al IN index_tuples k (:N)
           ==> rfa_jb Js V K (SUC m) (\t z. Tf t z (\r. basis(al r))))
     ==> !be. be IN index_tuples (k + 1) (:N)
              ==> rfa_jb Js V K m (\t z. lnabla k (G t) (Tf t) z (\r. basis(be r)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "chr") (LABEL_TAC "tf")))))) THEN
  X_GEN_TAC `be:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!r. (1 <= r /\ r <= k + 1 ==> 1 <= (be:num->num) r /\ be r <= dimindex(:N)) /\
        (~(1 <= r /\ r <= k + 1) ==> be r = 0)`
  (LABEL_TAC "ber") THENL
   [UNDISCH_TAC `(be:num->num) IN index_tuples (k + 1) (:N)` THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `al = \r. if 1 <= r /\ r <= k then (be:num->num) r else 0` THEN
  ABBREV_TAC `i = (be:num->num) (k + 1)` THEN
  SUBGOAL_THEN `1 <= i /\ i <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN USE_THEN "ber" (MP_TAC o CONJUNCT1 o SPEC `k + 1`) THEN
    ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. 1 <= r /\ r <= k ==> (al:num->num) r = be r` (LABEL_TAC "aleq") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN EXPAND_TAC "al" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. 1 <= r /\ r <= k ==> 1 <= (al:num->num) r /\ al r <= dimindex(:N)`
  (LABEL_TAC "alr") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    USE_THEN "aleq" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "ber" (MP_TAC o CONJUNCT1 o SPEC `r:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s. 1 <= r /\ r <= k /\ 1 <= s /\ s <= dimindex(:N)
          ==> (\j. if j = r then s else (al:num->num) j) IN index_tuples k (:N)`
  (LABEL_TAC "tup") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "alr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC;
      EXPAND_TAC "al" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(al:num->num) IN index_tuples k (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [USE_THEN "alr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "al" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. t IN Js /\ z IN V
          ==> rfa_pd i (\t z. (Tf:real->real^N->(num->real^N)->real) t z
                               (\r. basis((al:num->num) r))) t z -
              sum(1..k) (\r. sum(1..dimindex(:N))
                (\s. (christoffel ((G:real->real^N->real^N^N) t) z
                                  (basis i) (basis(al r)))$s *
                     Tf t z (\j. basis(if j = r then s else al j)))) =
              lnabla k (G t) (Tf t) z (\r. basis(be r))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field V ((G:real->real^N->real^N^N) t) /\
                  ltensor_field k V ((Tf:real->real^N->(num->real^N)->real) t) /\
                  (!u. smooth_map_on V (\y. lift(Tf t y u)))`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `V:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(Tf:real->real^N->(num->real^N)->real) t`; `z:real^N`; `al:num->num`;
                   `i:num`] RFA_PD_TENSOR_COMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `V:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(Tf:real->real^N->(num->real^N)->real) t`] LRG_LNABLA_ITER_FIELD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `SUC 0`) THEN
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\r. basis((be:num->num) r):real^N`;
      `\r. if r = k + 1 then basis i else basis((al:num->num) r):real^N`] o CONJUNCT1) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [EXPAND_TAC "i" THEN ASM_REWRITE_TAC[];
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "aleq" MATCH_MP_TAC THEN
        ASM_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[rfa_pd; partial_derivative; COND_RAND] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t z. rfa_pd i (\t z. (Tf:real->real^N->(num->real^N)->real) t z
                            (\r. basis((al:num->num) r))) t z -
          sum(1..k) (\r. sum(1..dimindex(:N))
            (\s. (christoffel ((G:real->real^N->real^N^N) t) z (basis i) (basis(al r)))$s *
                 Tf t z (\j. basis(if j = r then s else al j))))` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                   `\t z. (Tf:real->real^N->(num->real^N)->real) t z
                            (\r. basis((al:num->num) r))`] RFA_JB_SUC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "tf" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(al:num->num) IN index_tuples k (:N)`)]) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "chr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "alr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC m` THEN
    REWRITE_TAC[ARITH_RULE `m <= SUC m`] THEN
    USE_THEN "tf" MATCH_MP_TAC THEN USE_THEN "tup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Jets of the components of nabla^l lrm4, by induction on l. *)

let P2CJ_LNABLA_ITER_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) M.
     open V /\ K SUBSET V /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K M (\t z. G t z$p$q)) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K (SUC M) (\t z. (christoffel (G t) z (basis i) (basis j))$s))
     ==> !l m be. m + l <= M /\ be IN index_tuples (4 + l) (:N)
                  ==> rfa_jb Js V K m
                        (\t z. lnabla_iter 4 l (G t) (lrm4 (G t)) z (\r. basis(be r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2CJ_LRM4_JB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MONO THENL
     [EXISTS_TAC `M:num`; EXISTS_TAC `SUC M`] THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla_iter] THEN
  SUBGOAL_THEN `(be:num->num) IN index_tuples ((4 + l) + 1) (:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `(be:num->num) IN index_tuples (4 + SUC l) (:N)` THEN
    REWRITE_TAC[ARITH_RULE `4 + SUC l = (4 + l) + 1`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `G:real->real^N->real^N^N`; `4 + l`;
                 `\t. lnabla_iter 4 l ((G:real->real^N->real^N^N) t) (lrm4 (G t))`; `m:num`]
                P2CJ_LNABLA_JB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`4`; `V:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`] LRG_LNABLA_ITER_FIELD) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `SUC M` THEN
      ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `be:num->num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tensor norms from bounds on the components and on the                    *)
(* entries of the inverse metric, and the bound on lrm_deriv_norm2 j from   *)
(* jets of order j + 2 of the metrics and a uniform lower bound.            *)
(* ------------------------------------------------------------------------- *)

let P2CJ_LTNORM2_BOUND = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y C L.
     &0 <= C /\ &0 <= L /\
     (!al. al IN index_tuples k (:N) ==> abs(tf y (\m. basis(al m))) <= C) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> abs(matrix_inv(G y)$p$q) <= L)
     ==> ltnorm2 k G tf y <=
         &(CARD(index_tuples k (:N))) * (&(CARD(index_tuples k (:N))) * (C * C * L pow k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltnorm2] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `abs(product(1..k) (\m. matrix_inv((G:real^N->real^N^N) y)$(i m)$(j m))) <= L pow k`
  ASSUME_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM PRODUCT_CONST_NUMSEG_1] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(i:num->num) IN index_tuples k (:N)`;
                           `(j:num->num) IN index_tuples k (:N)`] THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((tf:real^N->(num->real^N)->real) y (\m. basis(i m))) <= C /\
                abs(tf y (\m. basis(j m))) <= C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]);;

(* The bound on |nabla^j Rm|^2 from jets of order j + 2. *)

let P2CJ_RMD2_FROM_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) Lm j.
     open V /\ K SUBSET V /\ &0 <= Lm /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (G t y ** v))) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K (j + 2) (\t z. G t z$p$q))
     ==> ?C. !t y. t IN Js /\ y IN K ==> lrm_deriv_norm2 j (G t) y <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `G:real->real^N->real^N^N`; `Lm:real`; `j + 1`] P2CJ_CHRIST_JB_FIN) THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC(j + 1) = j + 2`] THEN DISCH_THEN(LABEL_TAC "chr") THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `G:real->real^N->real^N^N`; `j:num`] P2CJ_LNABLA_ITER_JB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `j + 2` THEN ASM_SIMP_TAC[] THEN ARITH_TAC;
      USE_THEN "chr" (MP_TAC o SPEC `SUC j`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `0`]) THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    DISCH_THEN(LABEL_TAC "nab")] THEN
  SUBGOAL_THEN
   `?C. &0 <= C /\
        !be t y. be IN index_tuples (4 + j) (:N) /\ t IN Js /\ y IN K
                 ==> abs(lnabla_iter 4 j ((G:real->real^N->real^N^N) t) (lrm4 (G t)) y
                           (\r. basis(be r))) <= C`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!be. be IN index_tuples (4 + j) (:N)
           ==> ?C. !t y. t IN Js /\ y IN K
                         ==> abs(lnabla_iter 4 j ((G:real->real^N->real^N^N) t)
                                   (lrm4 (G t)) y (\r. basis(be r))) <= C`
    MP_TAC THENL
     [X_GEN_TAC `be:num->num` THEN DISCH_TAC THEN
      USE_THEN "nab" (MP_TAC o C MP (ASSUME `(be:num->num) IN index_tuples (4 + j) (:N)`) o
                      SPEC `be:num->num`) THEN
      REWRITE_TAC[RFA_JB_ZERO] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_TAC `CC:(num->num)->real`) THEN
    MP_TAC(ISPECL [`\be:num->num. abs((CC:(num->num)->real) be)`;
                   `index_tuples (4 + j) (:N)`] UPPER_BOUND_FINITE_SET_REAL) THEN
    REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN EXISTS_TAC `abs a` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(CC:(num->num)->real) be` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs c <= a ==> c <= abs a`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `&(CARD(index_tuples (4 + j) (:N))) *
              (&(CARD(index_tuples (4 + j) (:N))) * (C * C * Lm pow (4 + j)))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real->real^N->real^N^N) t y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
                  LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lrm_deriv_norm2] THEN MATCH_MP_TAC P2CJ_LTNORM2_BOUND THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_GINV_ENTRY_BOUND THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From C^m closeness to a fixed metric field on a compact set              *)
(* to jets of order m (the RFA_COORD_JET argument of P3S_NORMALIZED_JET     *)
(* without the rescaling), and the uniform bound on lrm_deriv_norm2 j for    *)
(* all metric fields that are C^m close, m >= j + 2, with closeness bound    *)
(* e < 1 (by contradiction, along a sequence indexed by the reals &n).       *)
(* The hypothesis e < 1 cannot be dropped: for G = d G0 with small d > 0 and *)
(* a constant G0, lck_dist2 m G0 G is (1 - d) squared times the dimension,   *)
(* so below any e larger than the dimension, while lrm_deriv_norm2 j G is    *)
(* d to the power -(j + 2) times lrm_deriv_norm2 j G0.                       *)
(* ------------------------------------------------------------------------- *)

(* Uniform lower bound of a continuous positive definite matrix field on a  *)
(* compact set: a copy of P2A_FAMILY_LOWER (pc_p2a_lbvp) and                 *)
(* P4_FAMILY_LOWER (pc_p4_width), restated to keep the closure of this       *)
(* shared unit small.                                                        *)

let P2CJ_FAMILY_LOWER = prove
 (`!(G:real^M->real^N^N) S.
        compact S /\ (\z. vectorize(G z)) continuous_on S /\
        (!z v. z IN S /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
        ==> ?m. &0 < m /\
                !z v. z IN S ==> m * norm v pow 2 <= v dot (G z ** v)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S:real^M->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(M,N)finite_sum.
       sndcart p dot ((G:real^M->real^N^N) (fstcart p) ** sndcart p)`;
    `(S:real^M->bool) PCROSS sphere(vec 0:real^N,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      ASM_REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^(M,N)finite_sum. (G:real^M->real^N^N) (fstcart p)) =
        (\z. vectorize(G z)) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^M` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `m = u0 dot ((G:real^M->real^N^N) z0 ** u0)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `inv(norm v) % v:real^N`]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((G:real^M->real^N^N) z ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = (inv n * inv n * q) * n pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;

(* Jets of order m from C^m closeness to G0 on a compact set. *)

let P2CJ_JB_FROM_LCK = prove
 (`!Js V K (G0:real^N->real^N^N) (G:real->real^N->real^N^N) m e.
     metric_field V G0 /\ compact K /\ K SUBSET V /\
     (!t. t IN Js ==> metric_field V (G t)) /\
     (!t y. t IN Js /\ y IN K ==> lck_dist2 m G0 (G t) y < e)
     ==> !p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> rfa_jb Js V K m (\t z. G t z$p$q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "LCK"))))) THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> smooth_map_on V (\z. lift((G0:real^N->real^N^N) z$p$q))`
  (LABEL_TAC "G0S") THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `G0:real^N->real^N^N`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[metric_field]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?L. &0 <= L /\ !y p. y IN K /\ 1 <= p /\ p <= dimindex(:N)
                         ==> (G0:real^N->real^N^N) y$p$p <= L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!p. ?C. 1 <= p /\ p <= dimindex(:N)
              ==> !y. y IN K ==> (G0:real^N->real^N^N) y$p$p <= C`
    MP_TAC THENL
     [X_GEN_TAC `p:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{&0}`; `V:real^N->bool`; `K:real^N->bool`; `0`;
                     `\z. (G0:real^N->real^N^N) z$p$p`] P3S_JB_FIXED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "G0S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[rfa_jb] THEN
      DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `[]:num list`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[IN_SING; pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0;
                      iterated_partial; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `Cp:num->real`) THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))` THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_ABS_POS] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `p:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Cp:num->real) p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= abs c`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`\p. abs((Cp:num->real) p)`;
                     `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))`;
                     `1..dimindex(:N)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = \t:real. \z:real^N. \u:num->real^N.
          lmetric2 ((G:real->real^N->real^N^N) t) z u - lmetric2 (G0:real^N->real^N^N) z u` THEN
  SUBGOAL_THEN
   `!t. t IN Js ==> ltensor_field 2 V ((D:real->real^N->(num->real^N)->real) t) /\
                    (!u. smooth_map_on V (\z. lift(D t z u)))`
  (LABEL_TAC "DF") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `G0:real^N->real^N^N`;
                   `(G:real->real^N->real^N^N) t`] LRG_LMETRIC2_DIFF_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `2`; `\x:real. (G0:real^N->real^N^N)`;
                 `D:real->real^N->(num->real^N)->real`; `Js:real->bool`;
                 `V:real^N->bool`; `K:real^N->bool`] RFA_COORD_JET) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`j:num`; `al:num->num`] THEN STRIP_TAC THEN
      REWRITE_TAC[RFA_JB_ZERO] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        USE_THEN "DF" (MP_TAC o C MP (ASSUME `(x:real) IN Js`) o SPEC `x:real`) THEN
        STRIP_TAC THEN
        MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                       `(D:real->real^N->(num->real^N)->real) x`] LRG_LNABLA_ITER_FIELD) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `e * L pow (2 + j) + &1` THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "DF" (MP_TAC o C MP (ASSUME `(x:real) IN Js`) o SPEC `x:real`) THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`2`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                     `(D:real->real^N->(num->real^N)->real) x`] LRG_LNABLA_ITER_FIELD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(STRIP_ASSUME_TAC o SPEC `j:num`)] THEN
      BETA_TAC THEN MATCH_MP_TAC RFA_COMP_BOUND THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `G0:real^N->real^N^N`] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `lck_dist2 m (G0:real^N->real^N^N) ((G:real->real^N->real^N^N) x) y` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "D" THEN BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC LRG_LCK_DIST2_TERM_LE THEN EXISTS_TAC `V:real^N->bool` THEN
        ASM_SIMP_TAC[];
        USE_THEN "LCK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `s:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC P3S_JB_FIXED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_SMOOTH_CHR_ENTRY THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "CJ")] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC `\t z. (D:real->real^N->(num->real^N)->real) t z
                      (\r. basis(if r = 1 then p else if r = 2 then q else 0)) +
                    (G0:real^N->real^N^N) z$p$q` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "D" THEN ASM_SIMP_TAC[P3S_LMETRIC2_BASIS] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "CJ" MATCH_MP_TAC THEN ASM_SIMP_TAC[P3S_PAIR_INDEX_TUPLE];
      MATCH_MP_TAC P3S_JB_FIXED THEN ASM_SIMP_TAC[]]]);;

(* The uniform bound on |nabla^j Rm|^2 for metric fields C^m close to G0. *)

let P2CJ_RMD2_FROM_LCK = prove
 (`!V K (G0:real^N->real^N^N) m e j.
     metric_field V G0 /\ compact K /\ K SUBSET V /\ e < &1 /\ j + 2 <= m
     ==> ?C. !G y. metric_field V G /\ (!z. z IN K ==> lck_dist2 m G0 G z < e) /\ y IN K
                   ==> lrm_deriv_norm2 j G y <= C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `K:real^N->bool`] P2CJ_FAMILY_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\z. (vectorize:real^N^N->real^(N,N)finite_prod) ((G0:real^N->real^N^N) z)) =
                    vectorize o G0` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[metric_field];
      MAP_EVERY X_GEN_TAC [`z:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      UNDISCH_TAC `metric_field V (G0:real^N->real^N^N)` THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^N` o last o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `sqrt e < &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`e:real`; `&1`] SQRT_MONO_LT) THEN ASM_REWRITE_TAC[SQRT_1];
    ALL_TAC] THEN
  ABBREV_TAC `d = c0 * (&1 - sqrt e)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?G y. metric_field V G /\
              (!z. z IN K ==> lck_dist2 m (G0:real^N->real^N^N) G z < e) /\ y IN K /\
              &n < lrm_deriv_norm2 j G y`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gs:num->real^N->real^N^N`
    (X_CHOOSE_THEN `ys:num->real^N` (LABEL_TAC "bad"))) THEN
  ABBREV_TAC `Js = {&n | n IN (:num)}` THEN
  ABBREV_TAC `GG = \t:real. (Gs:num->real^N->real^N^N) (@n. &n = t)` THEN
  SUBGOAL_THEN `!n. (GG:real->real^N->real^N^N) (&n) = Gs n` (LABEL_TAC "GGn") THENL
   [GEN_TAC THEN EXPAND_TAC "GG" THEN REWRITE_TAC[REAL_OF_NUM_EQ; SELECT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN Js ==> ?n. t = &n` (LABEL_TAC "JS") THENL
   [EXPAND_TAC "Js" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN Js
        ==> metric_field V ((GG:real->real^N->real^N^N) t) /\
            (!z. z IN K ==> lck_dist2 m (G0:real^N->real^N^N) (GG t) z < e)`
  (LABEL_TAC "GGF") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "JS" (MP_TAC o C MP (ASSUME `(t:real) IN Js`) o SPEC `t:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "bad" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `G0:real^N->real^N^N`; `GG:real->real^N->real^N^N`; `m:num`; `e:real`]
                P2CJ_JB_FROM_LCK) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `GG:real->real^N->real^N^N`; `inv d`; `j:num`] P2CJ_RMD2_FROM_JB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "GGF" (MP_TAC o C MP (ASSUME `(t:real) IN Js`) o SPEC `t:real`) THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`m:num`; `V:real^N->bool`; `G0:real^N->real^N^N`;
                     `(GG:real->real^N->real^N^N) t`; `y:real^N`; `v:real^N`] LCK_DIST_C0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `sqrt(lck_dist2 m (G0:real^N->real^N^N) ((GG:real->real^N->real^N^N) t) y)
                    <= sqrt e` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= v dot ((G0:real^N->real^N^N) y ** v) /\
                    c0 * norm(v:real^N) pow 2 <= v dot (G0 y ** v)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * norm(v:real^N) pow 2` THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `d * norm(v:real^N) pow 2 <= v dot ((GG:real->real^N->real^N^N) t y ** v)`
      ASSUME_TAC THENL
       [EXPAND_TAC "d" THEN
        SUBGOAL_THEN
         `sqrt(lck_dist2 m (G0:real^N->real^N^N) ((GG:real->real^N->real^N^N) t) y) *
          (v dot (G0 y ** v)) <= sqrt e * (v dot (G0 y ** v)) /\
          (&1 - sqrt e) * (c0 * norm(v:real^N) pow 2) <= (&1 - sqrt e) * (v dot (G0 y ** v))`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv d * (d * norm(v:real^N) pow 2)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                     REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MONO THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "CB")) THEN
  MP_TAC(SPEC `C:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  USE_THEN "CB" (MP_TAC o SPECL [`&n`; `(ys:num->real^N) n`]) THEN
  USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "bad" (MP_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `&n IN (Js:real->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Js" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

