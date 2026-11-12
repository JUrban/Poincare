(* ========================================================================= *)
(* Unit pc_s2ent_calc: calculus on a closed Riemannian manifold for          *)
(* Hamilton's entropy on surfaces (the statement                             *)
(* P2B_REQ_S2_ENTROPY_STATEMENT of pc_p2b_s2entreq).  Ric = (R/2) g in       *)
(* dimension 2; the trace of tr_g Hess_g V is the Laplacian of tr_g V (for   *)
(* the scalar heat flow from PDE_MLIN); the Bochner formula in local form;   *)
(* the gradient field, integration by parts and the integrated Bochner       *)
(* inequality on a closed surface.                                           *)
(* ========================================================================= *)

needs "src/pc_pde_mexist.ml";;
needs "src/pc_grg_divthm.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_rfa_maxp.ml";;
needs "src/pc_rfa_hcalc.ml";;
needs "src/pc_rfa_rmnorm.ml";;
needs "src/pc_rfa_p3alg.ml";;
needs "src/pc_rf_unique.ml";;

prioritize_real();;
type_invention_error := true;;

let s2e_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* ------------------------------------------------------------------------- *)
(* 2-d curvature algebra, Ric = (R/2) g in dimension 2.                      *)
(* Copies (renamed RFA_S2_ to S2E_) of RFA_S2_ORTHO2_MATRIX,                 *)
(* RFA_S2_RIC_ORTHO and RFA_S2_EINSTEIN2 of unit pc_rfa_s2loc, whose load    *)
(* closure has 147 files.                                                    *)
(* ------------------------------------------------------------------------- *)

let S2E_ORTHO2_MATRIX = prove
 (`!(G0:real^2^2) u v.
     (!a b. a dot (G0 ** b) = b dot (G0 ** a)) /\
     u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ u dot (G0 ** v) = &0
     ==> ?S:real^2^2. invertible S /\ matrix_inv G0 = transp S ** S /\
                      transp S ** basis 1 = u /\ transp S ** basis 2 = v`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(lambda i j. if i = 1 then (u:real^2)$j else (v:real^2)$j):real^2^2` THEN
  ABBREV_TAC `S = (lambda i j. if i = 1 then (u:real^2)$j else (v:real^2)$j):real^2^2` THEN
  SUBGOAL_THEN `transp (S:real^2^2) ** basis 1 = u /\ transp S ** basis 2 = v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THEN
    SIMP_TAC[CART_EQ; MATRIX_VECTOR_MUL_BASIS; column; transp; LAMBDA_BETA;
             DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                      ==> ((S:real^2^2) ** (G0:real^2^2) ** transp S)$i$j =
                          (transp S ** basis i) dot (G0 ** (transp S ** basis j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_2; column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^2^2) ** (G0:real^2^2) ** transp S = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SUBGOAL_THEN `(v:real^2) dot ((G0:real^2^2) ** u) = &0` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH; MAT_COMPONENT; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv (G0:real^2^2) = transp (S:real^2^2) ** S` ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    SUBGOAL_THEN `(G0:real^2^2) ** (transp (S:real^2^2) ** S) = mat 1` ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  EXISTS_TAC `(G0:real^2^2) ** transp (S:real^2^2)` THEN ASM_REWRITE_TAC[]);;

let S2E_RIC_ORTHO = prove
 (`!U (G:real^2->real^2^2) y u v.
     metric_field U G /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> lricci G y u u = lsectional G y u v /\
         lricci G y v v = lsectional G y u v /\
         lricci G y u v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `u:real^2`; `v:real^2`] S2E_ORTHO2_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `lsectional (G:real^2->real^2^2) y u v =
                lrm4 G y (\m. if m = 1 then u else if m = 2 then v
                              else if m = 3 then u else v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lsectional; lrm4] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                RFA_RIC_FRAME_RM) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`]
                RFA_LRM4_ZERO12) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`]
                RFA_LRM4_ZERO34) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `v:real^2`; `u:real^2`]
                RFA_LRM4_SWAP_PAIRS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]);;

let S2E_EINSTEIN2 = prove
 (`!U (G:real^2->real^2^2) y.
     metric_field U G /\ y IN U
     ==> (!v w. lricci G y v w = lscalar G y / &2 * (v dot (G y ** w))) /\
         (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = lscalar G y / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^2->real^2^2) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
          ==> (transp (S:real^2^2) ** basis a) dot ((G:real^2->real^2^2) y ** (transp S ** basis b)) =
              if a = b then &1 else &0`
  (LABEL_TAC "on") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  ABBREV_TAC `K = lsectional (G:real^2->real^2^2) y (transp (S:real^2^2) ** basis 1)
                    (transp S ** basis 2)` THEN
  SUBGOAL_THEN
   `lricci (G:real^2->real^2^2) y (transp (S:real^2^2) ** basis 1) (transp S ** basis 1) = K /\
    lricci G y (transp S ** basis 2) (transp S ** basis 2) = K /\
    lricci G y (transp S ** basis 1) (transp S ** basis 2) = &0 /\
    lricci G y (transp S ** basis 2) (transp S ** basis 1) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 1`; `transp (S:real^2^2) ** basis 2`]
                  S2E_RIC_ORTHO) THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 2`; `transp (S:real^2^2) ** basis 1`]
                  S2E_RIC_ORTHO) THEN
    USE_THEN "on" (fun th -> SIMP_TAC[th; ARITH]) THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`;
                   `transp (S:real^2^2) ** basis 2`; `transp (S:real^2^2) ** basis 1`]
                  RFA_LSECTIONAL_SWAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (G:real^2->real^2^2) y = &2 * K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                  RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w. lricci (G:real^2->real^2^2) y v w = K * (v dot (G y ** w))`
  (LABEL_TAC "ein") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `S:real^2^2`; `lricci (G:real^2->real^2^2) y`;
                   `\v w. K * (v dot ((G:real^2->real^2^2) y ** w))`;
                   `v:real^2`; `w:real^2`] RFA_BILIN_FRAME_EQ) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      REWRITE_TAC[LINEAR_LIFT_DOT];
      GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_2] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    USE_THEN "on" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(a = 1 \/ a = 2) /\ (b = 1 \/ b = 2)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `u:real^2`; `v:real^2`]
                RFA_GS_ORTHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^2` (X_CHOOSE_THEN `v1:real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))))) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `u1:real^2`; `v1:real^2`]
                S2E_RIC_ORTHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  USE_THEN "ein" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The G-trace of tr_G Hess_G V (pde_ltrhess of pc_pde_iface)                *)
(* is the Laplacian of the G-trace of V (local form, any dimension).         *)
(* The contraction of the first two slots commutes with nabla               *)
(* (LRG_LNABLA_CONTRACT, used twice) and llap is the trace of the Hessian    *)
(* (LRG_LLAP_LNABLA).  Used for the scalar heat flow phi = (1/2) tr_g V of a *)
(* solution V of PDE_MLIN.                                                    *)
(* ------------------------------------------------------------------------- *)

(* lmetric2 of a smooth matrix field (LRG_LMETRIC2_FIELD for metric fields,   *)
(* same proof).                                                              *)

let S2E_LMETRIC2_FIELD = prove
 (`!U (V:real^N->real^N^N).
        open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V)
        ==> ltensor_field 2 U (lmetric2 V) /\
            (!u. smooth_map_on U (\y. lift(lmetric2 V y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field; lmetric2] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THEN TRY AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      SUBGOAL_THEN
       `(\v. lift((u:num->real^N) 1 dot ((V:real^N->real^N^N) y ** v))) =
        (\v. (\x. lift(u 1 dot x)) ((\v. V y ** v) v))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
      REWRITE_TAC[LINEAR_LIFT_DOT; MATRIX_VECTOR_MUL_LINEAR]];
    GEN_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]]);;

(* Entries against basis vectors. *)

let S2E_BASIS_DOT_MATRIX = prove
 (`!(A:real^N^N) a b.
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> basis a dot (A ** basis b) = A$a$b`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA]);;

(* The trace identity. *)

let S2E_LTRHESS_TRACE = prove
 (`!U (G:real^N->real^N^N) (V:real^N->real^N^N) y.
        metric_field U G /\
        smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\ y IN U
        ==> sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
              matrix_inv(G y)$i$j * pde_ltrhess G G V y$i$j)) =
            llap G (\z. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                          matrix_inv(G z)$i$j * V z$i$j))) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`] S2E_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (V:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `tv = \z:real^N. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
                     matrix_inv((G:real^N->real^N^N) z)$i$j * (V:real^N->real^N^N) z$i$j))` THEN
  (* the contraction of lmetric2 V is the trace function *)
  SUBGOAL_THEN
   `!x:real^N u:num->real^N.
       sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
         matrix_inv((G:real^N->real^N^N) x)$a$b *
         lmetric2 (V:real^N->real^N^N) x
           (\m. if m = 1 then basis a else if m = 2 then basis b else u(m - 2)))) =
       tv x`
  (LABEL_TAC "CT") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "tv" THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[lmetric2; ARITH] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC S2E_BASIS_DOT_MATRIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* on U the contraction of nabla T is the differential of the trace *)
  SUBGOAL_THEN
   `!x u. x IN U
          ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                matrix_inv((G:real^N->real^N^N) x)$a$b *
                lnabla 2 G (lmetric2 (V:real^N->real^N^N)) x
                  (\m. if m = 1 then basis a else if m = 2 then basis b else u(m - 2)))) =
              drop(frechet_derivative (\w. lift(tv w)) (at x) (u 1))`
  (LABEL_TAC "B") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lmetric2 (V:real^N->real^N^N)`; `x:real^N`; `u:num->real^N`]
                  LRG_LNABLA_CONTRACT) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[lnabla; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO] THEN
    USE_THEN "CT" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the trace function is smooth *)
  SUBGOAL_THEN `smooth_map_on U (\z. lift((tv:real^N->real) z))` ASSUME_TAC THENL
   [EXPAND_TAC "tv" THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\z:real^N. lift(matrix_inv((G:real^N->real^N^N) z)$i$j)`;
                   `\z:real^N. lift((V:real^N->real^N^N) z$i$j)`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GINV_ENTRY_SMOOTH THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`] LRG_SMOOTH_VECTORIZE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* llap of tv as the trace of the Hessian *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `tv:real^N->real`; `y:real^N`]
                LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* the entries of pde_ltrhess *)
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> pde_ltrhess G G (V:real^N->real^N^N) y$i$j =
              sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                matrix_inv((G:real^N->real^N^N) y)$p$q *
                lnabla 3 G (lnabla 2 G (lmetric2 V)) y
                  (\m. if m = 1 then basis i else if m = 2 then basis j
                       else if m - 2 = 1 then basis p else basis q)))`
  (LABEL_TAC "TR") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_ltrhess; LAMBDA_BETA] THEN
    REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH_RULE `m - 2 = 1 <=> m = 3`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  (* move the (p,q) trace outside *)
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      matrix_inv((G:real^N->real^N^N) y)$i$j * pde_ltrhess G G (V:real^N->real^N^N) y$i$j)) =
    sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
      matrix_inv(G y)$p$q *
      sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
        matrix_inv(G y)$i$j *
        lnabla 3 G (lnabla 2 G (lmetric2 V)) y
          (\m. if m = 1 then basis i else if m = 2 then basis j
               else if m - 2 = 1 then basis p else basis q)))))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
        sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
          matrix_inv((G:real^N->real^N^N) y)$p$q *
          matrix_inv(G y)$i$j *
          lnabla 3 G (lnabla 2 G (lmetric2 (V:real^N->real^N^N))) y
            (\m. if m = 1 then basis i else if m = 2 then basis j
                 else if m - 2 = 1 then basis p else basis q)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "TR" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [PDE_SUM4_SWAP] THEN
      REWRITE_TAC[GSYM SUM_LMUL]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y)$q$p = matrix_inv(G y)$p$q`
  SUBST1_TAC THENL [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN
  (* the inner (i,j) contraction of nabla^2 T: LRG_LNABLA_CONTRACT at k = 1 *)
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 G (lmetric2 (V:real^N->real^N^N))`; `y:real^N`;
                 `\m:num. if m = 1 then basis p:real^N else basis q`]
                LRG_LNABLA_CONTRACT) THEN
  REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "B" (fun th -> ASM_SIMP_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The Bochner formula in local form.  For a smooth function f,              *)
(* the rough Laplacian of df is d(Lap f) + Ric(., grad f)                   *)
(* (RFA_LTLAP_COMMUTE_EXACT at k = 0 with RFA_RM_TRACE14), so by             *)
(* RFA_LLAP_LTNORM2 at k = 1, Lap |df|^2 = 2 <df, d Lap f> + 2 Ric(grad f,   *)
(* grad f) + 2 |Hess f|^2; in dimension 2, Ric = (R/2) g (S2E_EINSTEIN2)     *)
(* gives Lap |df|^2 = 2 <df, d Lap f> + R |df|^2 + 2 |Hess f|^2.             *)
(* ------------------------------------------------------------------------- *)

let S2E_SUM_INDEX_TUPLES_1 = prove
 (`!f. sum (index_tuples 1 (:N)) f =
       sum(1..dimindex(:N)) (\q. f (\m. if m = 1 then q else 0))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->real`; `0`] LRG_SUM_INDEX_TUPLES_SUC) THEN
  REWRITE_TAC[ADD_CLAUSES; LRG_SUM_INDEX_TUPLES_0]);;

(* The inner product of two 1-forms given by their values on the first slot. *)

let S2E_LTINNER_1 = prove
 (`!(G:real^N->real^N^N) (Fa:real^N->real^N->real) (Ha:real^N->real^N->real) y.
     ltinner 1 G (\z u. Fa z (u 1)) (\z u. Ha z (u 1)) y =
     sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b * Fa y (basis a) * Ha y (basis b)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ltinner; S2E_SUM_INDEX_TUPLES_1; PRODUCT_SING_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!x y z:real. x * y * z = z * x * y`));;

(* df as a 1-tensor field. *)

let S2E_DF_FORM = prove
 (`!(G:real^N->real^N^N) f.
     lnabla 0 G (\z u. f z) = (\z u. rfa_d1 f z (u 1))`,
  REWRITE_TAC[FUN_EQ_THM; lnabla; rfa_d1; SUM_CLAUSES_NUMSEG; ARITH; ADD_CLAUSES;
              REAL_SUB_RZERO]);;

let S2E_DF_FIELD = prove
 (`!U (G:real^N->real^N^N) f.
     metric_field U G /\ smooth_map_on U (\z. lift(f z))
     ==> ltensor_field 1 U (\z u. rfa_d1 f z (u 1)) /\
         (!u. smooth_map_on U (\z. lift(rfa_d1 f z (u 1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N u:num->real^N. (f:real^N->real) z`]
                LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; S2E_DF_FORM; ADD_CLAUSES]);;

(* The two zero terms of the commutator at k = 0. *)

let S2E_RACT0 = prove
 (`!(G:real^N->real^N^N) sf (tf:real^N->(num->real^N)->real).
     rfa_ract 0 G sf tf = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; rfa_ract; SUM_CLAUSES_NUMSEG; ARITH]);;

let S2E_LNABLA_ZERO = prove
 (`!k (G:real^N->real^N^N) y u. lnabla k G (\z u. &0) y u = &0`,
  REWRITE_TAC[lnabla; LIFT_NUM; FRECHET_DERIVATIVE_CONST_AT; DROP_VEC; SUM_0;
              REAL_SUB_REFL]);;

(* The curvature term: the G-trace of the curvature action on df. *)

let S2E_RACT_TRACE = prove
 (`!U (G:real^N->real^N^N) f y (u:num->real^N).
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           rfa_ract 1 G (lrm4 G) (\z u. rfa_d1 f z (u 1)) y
             (\m. if m = 1 then basis a else if m = 2 then basis b
                  else if m = 3 then u 1 else u m))) =
         --(sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
              matrix_inv(G y)$c$d * rfa_d1 f y (basis d) * lricci G y (u 1) (basis c))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ract; SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_SUM4_SWAP] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `--(matrix_inv((G:real^N->real^N^N) y)$c$d * rfa_d1 f y (basis d) *
       lricci G y ((u:num->real^N) 1) (basis c)) =
    matrix_inv(G y)$c$d * rfa_d1 f y (basis d) * --(lricci G y (u 1) (basis c))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `basis c:real^N`] RFA_RM_TRACE14) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!p q l d:real. p * q * l * d = q * d * p * l`));;

(* The rough Laplacian of df (any dimension). *)

let S2E_LTLAP_DF = prove
 (`!U (G:real^N->real^N^N) f y (u:num->real^N).
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltlap 1 G (\z u. rfa_d1 f z (u 1)) y u =
         rfa_d1 (llap G f) y (u 1) +
         sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
           matrix_inv(G y)$c$d * rfa_d1 f y (basis d) * lricci G y (u 1) (basis c)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z:real^N u:num->real^N. (f:real^N->real) z`; `y:real^N`; `u:num->real^N`]
                RFA_LTLAP_COMMUTE_EXACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0]; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[S2E_DF_FORM; S2E_RACT0; S2E_LNABLA_ZERO; REAL_ADD_RID] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`;
                 `u:num->real^N`] S2E_RACT_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `lnabla 0 G (ltlap 0 G (\z:real^N u:num->real^N. (f:real^N->real) z)) y u =
    rfa_d1 (llap G f) y ((u:num->real^N) 1)`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `lnabla 0 G (\z:real^N u:num->real^N. llap G (f:real^N->real) z) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LTLAP_0 THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[S2E_DF_FORM; ETA_AX]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Bochner formula in dimension 2 (local form):                          *)
(*   Lap |df|^2 = 2 <df, d Lap f> + R |df|^2 + 2 |Hess f|^2,                *)
(* and the trace inequality (Lap f)^2 <= 2 |Hess f|^2 in dimension 2.       *)
(* ------------------------------------------------------------------------- *)

(* The differential as a sum over the basis. *)

let S2E_D1_SUM = prove
 (`!U (f:real^N->real) y w.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> rfa_d1 f y w = sum(1..dimindex(:N)) (\i. w$i * rfa_d1 f y (basis i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift((f:real^N->real) z)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_d1] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; DROP_VSUM] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL]);;

(* Contraction of the inverse metric against the metric. *)

let S2E_GINV_CONTRACT = prove
 (`!(A:real^N^N) (vd:num->real) w.
     ~(det A = &0) /\ transp A = A
     ==> sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
           matrix_inv A$c$d * vd d * (w dot (A ** basis c)))) =
         sum(1..dimindex(:N)) (\i. w$i * vd i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. 1 <= c /\ c <= dimindex(:N)
        ==> w dot ((A:real^N^N) ** basis c) =
            sum(1..dimindex(:N)) (\i. (w:real^N)$i * A$i$c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS] THEN
    REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i d. 1 <= i /\ i <= dimindex(:N) /\ 1 <= d /\ d <= dimindex(:N)
          ==> sum(1..dimindex(:N)) (\c. (A:real^N^N)$i$c * matrix_inv A$c$d) =
              if i = d then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `((A:real^N^N) ** matrix_inv A)$i$d = (mat 1:real^N^N)$i$d` MP_TAC THENL
     [ASM_SIMP_TAC[MATRIX_MUL_RINV]; ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; MAT_COMPONENT];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
      sum(1..dimindex(:N)) (\i.
        matrix_inv(A:real^N^N)$c$d * (vd:num->real) d * ((w:real^N)$i * A$i$c))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM SUM_LMUL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [PDE_JSWAP3] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum(1..dimindex(:N)) (\d. ((w:real^N)$i * (vd:num->real) d) *
      sum(1..dimindex(:N)) (\c. (A:real^N^N)$i$c * matrix_inv A$c$d))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(1..dimindex(:N)) (\d. if d = i then (w:real^N)$i * (vd:num->real) i else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `d:num = i` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

(* In dimension 2: sum_cd G^cd d_d f Ric(w, e_c) = (R/2) df(w). *)

let S2E_EINSTEIN_DF = prove
 (`!U (G:real^2->real^2^2) f y w.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> sum(1..dimindex(:2)) (\c. sum(1..dimindex(:2)) (\d.
           matrix_inv(G y)$c$d * rfa_d1 f y (basis d) * lricci G y w (basis c))) =
         lscalar G y / &2 * rfa_d1 f y w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] S2E_EINSTEIN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `f:real^2->real`; `y:real^2`; `w:real^2`] S2E_D1_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(G:real^2->real^2^2) y`; `\d. rfa_d1 (f:real^2->real) y (basis d)`;
                 `w:real^2`] S2E_GINV_CONTRACT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE; INVERTIBLE_DET_NZ];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* The 2-d Bochner formula. *)

let S2E_LBOCHNER2 = prove
 (`!U (G:real^2->real^2^2) f y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> llap G (lgrad2 G f) y =
         &2 * rfa_lginner G f (llap G f) y + lscalar G y * lgrad2 G f y +
         &2 * ltnorm2 2 G (lnabla 1 G (\z u. rfa_d1 f z (u 1))) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `f:real^2->real`] S2E_DF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lgrad2 (G:real^2->real^2^2) f = ltnorm2 1 G (\z u. rfa_d1 f z (u 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; RFA_LTNORM2_LTINNER; S2E_LTINNER_1; RFA_LGRAD2_D1;
                rfa_lginner];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^2->bool`; `G:real^2->real^2^2`;
                 `\z:real^2 u:num->real^2. rfa_d1 (f:real^2->real) z (u 1)`; `y:real^2`]
                RFA_LLAP_LTNORM2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ltinner 1 G (\z u. rfa_d1 f z (u 1)) (ltlap 1 G (\z u. rfa_d1 f z (u 1))) y =
    ltinner 1 G (\z u. rfa_d1 (f:real^2->real) z (u 1))
      (\z u. rfa_d1 (llap G f) z (u 1) +
             lscalar (G:real^2->real^2^2) y / &2 * rfa_d1 f z (u 1)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN X_GEN_TAC `u:num->real^2` THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `f:real^2->real`; `y:real^2`;
                   `u:num->real^2`] S2E_LTLAP_DF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC S2E_EINSTEIN_DF THEN EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LTINNER_RADD; RFA_LTINNER_RCMUL] THEN
  SUBGOAL_THEN
   `ltinner 1 G (\z u. rfa_d1 f z (u 1)) (\z u. rfa_d1 (llap G f) z (u 1)) y =
    rfa_lginner (G:real^2->real^2^2) f (llap G f) y`
  SUBST1_TAC THENL [REWRITE_TAC[S2E_LTINNER_1; rfa_lginner]; ALL_TAC] THEN
  REWRITE_TAC[GSYM RFA_LTNORM2_LTINNER] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Laplacian is the G-trace of the Hessian, and in                       *)
(* dimension 2 the square of the trace of a 2-tensor is at most twice its    *)
(* squared norm: (Lap f)^2 <= 2 |Hess f|^2.                                  *)
(* ------------------------------------------------------------------------- *)

let S2E_TENSOR_SLOTS = prove
 (`!k U (tf:real^N->(num->real^N)->real) y u u'.
     ltensor_field k U tf /\ y IN U /\ (!m. 1 <= m /\ m <= k ==> u m = u' m)
     ==> tf y u = tf y u'`,
  REWRITE_TAC[ltensor_field] THEN MESON_TAC[]);;

(* Laplacian as the trace of the Hessian lnabla 1 G df. *)

let S2E_LLAP_HESS = prove
 (`!U (G:real^N->real^N^N) f y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> llap G f y =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           lnabla 1 G (\z u. rfa_d1 f z (u 1)) y
             (\m. if m = 1 then basis a else basis b)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
                LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[GSYM rfa_d1] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
  ASM_MESON_TAC[]);;

(* Sums over index tuples of length 2. *)

let S2E_SUM_INDEX_TUPLES_2 = prove
 (`!f. sum (index_tuples 2 (:N)) f =
       sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
         f (\m. if m = 2 then s else if m = 1 then r else 0)))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->real`; `1`] LRG_SUM_INDEX_TUPLES_SUC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[S2E_SUM_INDEX_TUPLES_1]);;

(* The trace and the squared norm of a 2-tensor in a G-orthonormal frame.   *)

let S2E_TENSOR2_FRAME = prove
 (`!U (G:real^N->real^N^N) (H:real^N->(num->real^N)->real) y (S:real^N^N).
     ltensor_field 2 U H /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b * H y (\m. if m = 1 then basis a else basis b))) =
         sum(1..dimindex(:N)) (\r.
           H y (\m. if m = 1 then transp S ** basis r else transp S ** basis r)) /\
         ltnorm2 2 G H y =
         sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
           (H y (\m. if m = 1 then transp S ** basis r else transp S ** basis s)) pow 2))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `H:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`;
                   `\m:num. vec 0:real^N`] RFA_CONTR_FRAME) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' ==> a = b ==> a' = b'`) THEN
    CONJ_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
      AP_TERM_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC S2E_TENSOR_SLOTS THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `m = 1 \/ m = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
      [ASM_ARITH_TAC; REWRITE_TAC[ARITH]; REWRITE_TAC[ARITH]]);
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `H:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
                  LRG_LTNORM2_SQUARES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[S2E_SUM_INDEX_TUPLES_2] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC S2E_TENSOR_SLOTS THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `m = 1 \/ m = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
      [ASM_ARITH_TAC; REWRITE_TAC[ARITH]; REWRITE_TAC[ARITH]])]);;

(* In dimension 2: (tr_G H)^2 <= 2 |H|^2. *)

let S2E_TRACE_SQ_LE2 = prove
 (`!U (G:real^2->real^2^2) (H:real^2->(num->real^2)->real) y.
     metric_field U G /\ ltensor_field 2 U H /\ y IN U
     ==> (sum(1..dimindex(:2)) (\a. sum(1..dimindex(:2)) (\b.
            matrix_inv(G y)$a$b * H y (\m. if m = 1 then basis a else basis b)))) pow 2
         <= &2 * ltnorm2 2 G H y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`]
                LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `H:real^2->(num->real^2)->real`;
                 `y:real^2`; `S:real^2^2`] S2E_TENSOR2_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  ABBREV_TAC `h11 = (H:real^2->(num->real^2)->real) y
                      (\m. if m = 1 then transp (S:real^2^2) ** basis 1 else transp S ** basis 1)` THEN
  ABBREV_TAC `h12 = (H:real^2->(num->real^2)->real) y
                      (\m. if m = 1 then transp (S:real^2^2) ** basis 1 else transp S ** basis 2)` THEN
  ABBREV_TAC `h21 = (H:real^2->(num->real^2)->real) y
                      (\m. if m = 1 then transp (S:real^2^2) ** basis 2 else transp S ** basis 1)` THEN
  ABBREV_TAC `h22 = (H:real^2->(num->real^2)->real) y
                      (\m. if m = 1 then transp (S:real^2^2) ** basis 2 else transp S ** basis 2)` THEN
  MP_TAC(SPEC `h11 - h22:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `h12:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `h21:real` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The vector field 2 a grad b.  Locally it is the field                     *)
(* rfu_vf 0 (pc_rf_unique) with Q = a and X = db, so its divergence is       *)
(* 2 a Lap b + 2 <grad a, grad b> (RFU_DIV_IDENTITY).  It transforms as a    *)
(* vector under chart changes (RFU_MATINV_PULLBACK_VEC), which gives the     *)
(* manifold field s2e_mvf with smooth chart representatives.                 *)
(* ------------------------------------------------------------------------- *)

let s2e_lvf = new_definition
 `s2e_lvf (G:real^N->real^N^N) (a:real^N->real) (b:real^N->real) (y:real^N) =
    matrix_inv(G y) ** ((lambda k. (&2 * a y) * rfa_d1 b y (basis k)):real^N)`;;

let S2E_LVF_RFU = prove
 (`!(G:real^N->real^N^N) a b.
     s2e_lvf G a b = rfu_vf 0 G (\z u. a z) (\z u. rfa_d1 b z (u 1))`,
  REWRITE_TAC[FUN_EQ_THM; s2e_lvf; rfu_vf; ltinner; LRG_SUM_INDEX_TUPLES_0;
              PRODUCT_CLAUSES_NUMSEG; ARITH; ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

(* The divergence of the local field. *)

let S2E_LVF_DIV = prove
 (`!U (G:real^N->real^N^N) a b y.
     metric_field U G /\ smooth_map_on U (\z. lift(a z)) /\
     smooth_map_on U (\z. lift(b z)) /\ y IN U
     ==> ldiv G (s2e_lvf G a b) y =
         &2 * a y * llap G b y + &2 * rfa_lginner G a b y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `b:real^N->real`] S2E_DF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[S2E_LVF_RFU] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z:real^N u:num->real^N. (a:real^N->real) z`;
                 `\z:real^N u:num->real^N. rfa_d1 (b:real^N->real) z (u 1)`; `y:real^N`]
                RFU_DIV_IDENTITY) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[S2E_DF_FORM; S2E_LTINNER_1; GSYM rfa_lginner] THEN
  REWRITE_TAC[ltinner; LRG_SUM_INDEX_TUPLES_0; PRODUCT_CLAUSES_NUMSEG; ARITH;
              REAL_MUL_RID; rfu_tdiv; ADD_CLAUSES] THEN
  MATCH_MP_TAC(MESON[] `(x:real) = y ==> &2 * a * x + l = &2 * a * y + l`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `b:real^N->real`; `y:real^N`]
                S2E_LLAP_HESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LRG_LNABLA_AGREE THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `m = 1 \/ m = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
    [ASM_ARITH_TAC; REWRITE_TAC[ARITH]; REWRITE_TAC[ARITH]]));;

(* Locality of the local field. *)

let S2E_LVF_LOCAL = prove
 (`!(G:real^N->real^N^N) G' a a' b b' s y.
     open s /\ y IN s /\ (!z. z IN s ==> G z = G' z /\ a z = a' z /\ b z = b' z)
     ==> s2e_lvf G a b y = s2e_lvf G' a' b' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_lvf] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y = G' y /\ (a:real^N->real) y = a' y` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]);;

(* Covariance under a diffeomorphism between open sets. *)

let S2E_COVEC_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (b:real^N->real) y c.
     diffeomorphism_on U' U h h' /\ smooth_map_on U (\z. lift(b z)) /\ y IN U'
     ==> ((lambda k. c * rfa_d1 (b o h) y (basis k)):real^N) =
         transp(matrix(frechet_derivative h (at y))) **
         ((lambda k. c * rfa_d1 b (h y) (basis k)):real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U':real^N->bool) /\ open(U:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\z. lift((b:real^N->real) z)) (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `b:real^N->real`; `y:real^N`] LRG_COMPOSE_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[rfa_d1] THEN
  MP_TAC(ISPECL [`frechet_derivative (\z. lift((b:real^N->real) z)) (at ((h:real^N->real^N) y))`;
                 `frechet_derivative (h:real^N->real^N) (at y)`; `k:num`]
                LRG_DROP_LINEAR_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; TRANSP_COMPONENT] THEN REAL_ARITH_TAC);;

let S2E_LVF_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) a b y.
     metric_field U G /\ diffeomorphism_on U' U h h' /\
     smooth_map_on U (\z. lift(b z)) /\ y IN U'
     ==> frechet_derivative h (at y) (s2e_lvf (mpullback h G) (a o h) (b o h) y) =
         s2e_lvf G a b (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[s2e_lvf; o_THM] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `b:real^N->real`; `y:real^N`;
                 `&2 * (a:real^N->real) ((h:real^N->real^N) y)`] S2E_COVEC_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `frechet_derivative (h:real^N->real^N) (at y)` MATRIX_WORKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[mpullback] THEN MATCH_MP_TAC RFU_MATINV_PULLBACK_VEC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]]);;

(* ------------------------------------------------------------------------- *)
(* The field 2 a grad b on a manifold (preferred coordinates),               *)
(* its representative in any chart, its divergence, and integration by      *)
(* parts on a closed Riemannian manifold (MFD_DIVERGENCE_THEOREM):           *)
(*   int (a Lap b + <grad a, grad b>) = 0.                                   *)
(* ------------------------------------------------------------------------- *)

let s2e_mvf = new_definition
 `s2e_mvf (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (a:A->real) (b:A->real)
          (x:A) =
    s2e_lvf (metric_local atlas (chart_at atlas x) g)
            (\y. a(chart_inv (chart_at atlas x) y)) (\y. b(chart_inv (chart_at atlas x) y))
            (SND(chart_at atlas x) x)`;;

(* The manifold inner product of gradients, in preferred coordinates. *)

let s2e_ginner = new_definition
 `s2e_ginner (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (a:A->real) (b:A->real)
             (x:A) =
    rfa_lginner (metric_local atlas (chart_at atlas x) g)
                (\y. a(chart_inv (chart_at atlas x) y)) (\y. b(chart_inv (chart_at atlas x) y))
                (SND(chart_at atlas x) x)`;;

(* Change of chart. *)

let S2E_CHART_LVF = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b U phi V psi x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(b x)) /\
     (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
     ==> chart_jac (U,phi) (V,psi) x
           (s2e_lvf (metric_local atlas (U,phi) g) (\y. a(chart_inv (U,phi) y))
                    (\y. b(chart_inv (U,phi) y)) (phi x)) =
         s2e_lvf (metric_local atlas (V,psi) g) (\y. a(chart_inv (V,psi) y))
                 (\y. b(chart_inv (V,psi) y)) (psi x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) (U INTER V))
                             (metric_local atlas (V,psi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(V:A->bool,psi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s2e_lvf (metric_local atlas (U,phi) (g:A->real^N^N)) (\y. (a:A->real)(chart_inv (U,phi) y))
            (\y. (b:A->real)(chart_inv (U,phi) y)) ((phi:A->real^N) x) =
    s2e_lvf (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g))
            ((\y. a(chart_inv (V,psi) y)) o chart_trans (U,phi) (V,psi))
            ((\y. b(chart_inv (V,psi) y)) o chart_trans (U,phi) (V,psi)) (phi x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC S2E_LVF_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x':A`]
                  CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[chart_jac; SND] THEN
  MP_TAC(ISPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
    `\y. (a:A->real)(chart_inv (V:A->bool,psi:A->real^N) y)`;
    `\y. (b:A->real)(chart_inv (V:A->bool,psi:A->real^N) y)`;
    `(phi:A->real^N) x`] S2E_LVF_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
       [SET_TAC[];
        UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((b:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth; o_DEF] THEN
        DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
        ASM_REWRITE_TAC[FST; SND]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CHART_TRANS_AT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The representative of s2e_mvf in any chart. *)

let S2E_MVF_VREP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(b x)) /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> mfd_vrep atlas (s2e_mvf atlas g a b) c y =
         s2e_lvf (metric_local atlas c g) (\z. a(chart_inv c z)) (\z. b(chart_inv c z)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
                SND c (chart_inv c y) = y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_vrep; s2e_mvf] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `y:real^N`)) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `a:A->real`; `b:A->real`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                S2E_CHART_LVF) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

(* Smoothness of the local field and of the chart representatives. *)

let S2E_LVF_SMOOTH = prove
 (`!U (G:real^N->real^N^N) a b.
     metric_field U G /\ smooth_map_on U (\z. lift(a z)) /\ smooth_map_on U (\z. lift(b z))
     ==> smooth_map_on U (s2e_lvf G a b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `s2e_lvf (G:real^N->real^N^N) a b =
                (\y. matrix_inv(G y) **
                     ((lambda k. (&2 * a y) * rfa_d1 b y (basis k)):real^N))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; s2e_lvf]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE; INVERTIBLE_DET_NZ]];
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\y:real^N. ((lambda k. (&2 * (a:real^N->real) y) *
                                          rfa_d1 (b:real^N->real) y (basis k)):real^N)`]
                  SMOOTH_MAP_ON_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\z:real^N. lift(&2 * (a:real^N->real) z)`;
                   `\z:real^N. lift(rfa_d1 (b:real^N->real) z (basis k))`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[RFA_D1_SMOOTH] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]]);;

let S2E_MVF_SMOOTH = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x)) /\ c IN atlas
     ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (s2e_mvf atlas g a b) c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `s2e_lvf (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                      (\z. (a:A->real)(chart_inv c z)) (\z. (b:A->real)(chart_inv c z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC S2E_MVF_VREP THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC S2E_LVF_SMOOTH THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((a:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((b:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The divergence of s2e_mvf. *)

let S2E_MVF_DIV = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x)) /\
     x IN topspace top
     ==> mfd_div atlas g (s2e_mvf atlas g a b) x =
         &2 * a x * rfa_lap atlas g b x + &2 * s2e_ginner atlas g a b x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `cc = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  REWRITE_TAC[mfd_div; rfa_lap; s2e_ginner] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND (cc:(A->bool)#(A->real^N)) x IN IMAGE (SND cc) (FST cc)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND cc) (FST cc))
                  (metric_local atlas (cc:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:A->real. mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(f x))
                ==> smooth_map_on (IMAGE (SND cc) (FST cc))
                      (\z. lift(f(chart_inv (cc:(A->bool)#(A->real^N)) z)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ldiv (metric_local atlas (cc:(A->bool)#(A->real^N)) (g:A->real^N^N))
         (s2e_lvf (metric_local atlas cc g) (\z. (a:A->real)(chart_inv cc z))
                  (\z. (b:A->real)(chart_inv cc z))) (SND cc x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LDIV_LOCAL THEN EXISTS_TAC `IMAGE (SND cc) (FST (cc:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC S2E_MVF_VREP THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND cc) (FST (cc:(A->bool)#(A->real^N)))`;
                 `metric_local atlas (cc:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `\z. (a:A->real)(chart_inv (cc:(A->bool)#(A->real^N)) z)`;
                 `\z. (b:A->real)(chart_inv (cc:(A->bool)#(A->real^N)) z)`;
                 `SND (cc:(A->bool)#(A->real^N)) x`] S2E_LVF_DIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

(* Integration by parts on a closed Riemannian manifold. *)

let S2E_IBP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x))
     ==> mfd_has_integral (top,atlas) g
           (\x. a x * rfa_lap atlas g b x + s2e_ginner atlas g a b x) (topspace top) (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `s2e_mvf atlas (g:A->real^N^N) a b`] MFD_DIVERGENCE_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC S2E_MVF_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP MFD_HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `a:A->real`; `b:A->real`; `x:A`] S2E_MVF_DIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Scalar quantities in charts.  A local functional of the                   *)
(* metric and two functions that is invariant under pullbacks and local     *)
(* takes the same value in any two charts (S2E_CHART_SCALAR); so the         *)
(* manifold Laplacian rfa_lap and the inner product of gradients s2e_ginner *)
(* are given in every chart by llap and rfa_lginner, they are smooth, and   *)
(* smooth functions on a closed manifold are integrable.                     *)
(* ------------------------------------------------------------------------- *)

let S2E_CHART_SCALAR = prove
 (`!(Qf:(real^N->real^N^N)->(real^N->real)->(real^N->real)->real^N->real)
    (top:A topology) atlas (g:A->real^N^N) a b U phi V psi x.
     (!U U' (h:real^N->real^N) h' G a b y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        smooth_map_on U (\z. lift(a z)) /\ smooth_map_on U (\z. lift(b z)) /\ y IN U'
        ==> Qf (mpullback h G) (a o h) (b o h) y = Qf G a b (h y)) /\
     (!G G' a a' b b' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G z = G' z /\ a z = a' z /\ b z = b' z)
        ==> Qf G a b y = Qf G' a' b' y) /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x)) /\
     (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
     ==> Qf (metric_local atlas (U,phi) g) (\y. a(chart_inv (U,phi) y))
            (\y. b(chart_inv (U,phi) y)) (phi x) =
         Qf (metric_local atlas (V,psi) g) (\y. a(chart_inv (V,psi) y))
            (\y. b(chart_inv (V,psi) y)) (psi x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pb")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) (U INTER V))
                             (metric_local atlas (V,psi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(V:A->bool,psi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:A->real. mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(f x))
                ==> smooth_map_on (IMAGE (psi:A->real^N) (U INTER V))
                      (\z. lift(f(chart_inv (V,psi) z)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Qf:(real^N->real^N^N)->(real^N->real)->(real^N->real)->real^N->real)
      (metric_local atlas (U,phi) (g:A->real^N^N)) (\y. (a:A->real)(chart_inv (U,phi) y))
      (\y. (b:A->real)(chart_inv (U,phi) y)) ((phi:A->real^N) x) =
    Qf (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g))
       ((\y. a(chart_inv (V,psi) y)) o chart_trans (U,phi) (V,psi))
       ((\y. b(chart_inv (V,psi) y)) o chart_trans (U,phi) (V,psi)) (phi x)`
  SUBST1_TAC THENL
   [USE_THEN "loc" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x':A`]
                  CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  USE_THEN "pb" (MP_TAC o SPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
    `\y. (a:A->real)(chart_inv (V:A->bool,psi:A->real^N) y)`;
    `\y. (b:A->real)(chart_inv (V:A->bool,psi:A->real^N) y)`;
    `(phi:A->real^N) x`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CHART_TRANS_AT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The inner product of gradients: dot form, pullback, locality. *)

let S2E_LGINNER_DOT = prove
 (`!(G:real^N->real^N^N) a b y.
     rfa_lginner G a b y =
     ((lambda k. rfa_d1 a y (basis k)):real^N) dot
     (matrix_inv(G y) ** ((lambda k. rfa_d1 b y (basis k)):real^N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_lginner; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

let S2E_LGINNER_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) a b y.
     metric_field U G /\ diffeomorphism_on U' U h h' /\
     smooth_map_on U (\z. lift(a z)) /\ smooth_map_on U (\z. lift(b z)) /\ y IN U'
     ==> rfa_lginner (mpullback h G) (a o h) (b o h) y = rfa_lginner G a b (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[S2E_LGINNER_DOT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `a:real^N->real`; `y:real^N`; `&1`]
                S2E_COVEC_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `b:real^N->real`; `y:real^N`; `&1`]
                S2E_COVEC_PULLBACK) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[mpullback; DOT_MATRIX_TRANSP_LMUL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFU_MATINV_PULLBACK_VEC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]]);;

let S2E_LGINNER_LOCAL = prove
 (`!(G:real^N->real^N^N) G' a a' b b' s y.
     open s /\ y IN s /\ (!z. z IN s ==> G z = G' z /\ a z = a' z /\ b z = b' z)
     ==> rfa_lginner G a b y = rfa_lginner G' a' b' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_lginner] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y = G' y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!h. rfa_d1 (a:real^N->real) y h = rfa_d1 a' y h /\
                    rfa_d1 (b:real^N->real) y h = rfa_d1 b' y h`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC RFA_D1_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]);;

(* rfa_lap and s2e_ginner in any chart. *)

let S2E_LAP_CHART = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f c z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(f x)) /\ c IN atlas /\ z IN IMAGE (SND c) (FST c)
     ==> rfa_lap atlas g f (chart_inv c z) =
         llap (metric_local atlas c g) (\y. f(chart_inv c y)) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN FST c /\
                SND c (chart_inv c z) = z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) z` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `z:real^N`)) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_lap] THEN
  MP_TAC(ISPECL [`\(G:real^N->real^N^N) (a:real^N->real) (b:real^N->real) (y:real^N).
                    llap G b y`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `f:A->real`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                S2E_CHART_SCALAR) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LLAP_PULLBACK THEN ASM_MESON_TAC[];
      MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]];
    SIMP_TAC[]]);;

let S2E_GINNER_CHART = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b c z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x)) /\
     c IN atlas /\ z IN IMAGE (SND c) (FST c)
     ==> s2e_ginner atlas g a b (chart_inv c z) =
         rfa_lginner (metric_local atlas c g) (\y. a(chart_inv c y)) (\y. b(chart_inv c y)) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN FST c /\
                SND c (chart_inv c z) = z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) z` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `z:real^N`)) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[s2e_ginner] THEN
  MP_TAC(ISPECL [`rfa_lginner:(real^N->real^N^N)->(real^N->real)->(real^N->real)->real^N->real`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `a:A->real`; `b:A->real`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                S2E_CHART_SCALAR) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC S2E_LGINNER_PULLBACK THEN ASM_MESON_TAC[];
      MATCH_MP_TAC S2E_LGINNER_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[]];
    SIMP_TAC[]]);;

(* Smoothness of the local Laplacian and inner product (P2BS_LLAP_SMOOTH of  *)
(* pc_p2b_sol has the same statement; that unit is not in this closure).     *)

let S2E_LLAP_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> smooth_map_on U (\y. lift(llap G f y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. lift(ltlap 0 (G:real^N->real^N^N) (\x u. (f:real^N->real) x) y (\m. vec 0))` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_LTLAP_0 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z:real^N u:num->real^N. (f:real^N->real) z`] RFA_LTLAP_FIELD) THEN
    ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ETA_AX] THEN SIMP_TAC[]]);;

let S2E_LGINNER_SMOOTH = prove
 (`!U (G:real^N->real^N^N) a b.
     metric_field U G /\ smooth_map_on U (\y. lift(a y)) /\ smooth_map_on U (\y. lift(b y))
     ==> smooth_map_on U (\y. lift(rfa_lginner G a b y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[rfa_lginner; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\z:real^N. lift(matrix_inv((G:real^N->real^N^N) z)$i$j)`;
                 `\z:real^N. lift(rfa_d1 (a:real^N->real) z (basis i) *
                                  rfa_d1 (b:real^N->real) z (basis j))`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RFA_GINV_ENTRY_SMOOTH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z:real^N. lift(rfa_d1 (a:real^N->real) z (basis i))`;
                 `\z:real^N. lift(rfa_d1 (b:real^N->real) z (basis j))`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[RFA_D1_SMOOTH]);;

(* The manifold Laplacian and inner product of smooth functions are smooth. *)

let S2E_LAP_SMOOTH = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(f x))
     ==> mfd_smooth atlas (\x. lift(rfa_lap atlas g f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                            (\y. (f:A->real)(chart_inv c y)) z)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC S2E_LAP_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC S2E_LLAP_SMOOTH THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let S2E_GINNER_SMOOTH = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(a x)) /\ mfd_smooth atlas (\x. lift(b x))
     ==> mfd_smooth atlas (\x. lift(s2e_ginner atlas g a b x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(rfa_lginner (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                         (\y. (a:A->real)(chart_inv c y)) (\y. (b:A->real)(chart_inv c y)) z)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC S2E_GINNER_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC S2E_LGINNER_SMOOTH THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((a:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((b:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Smooth (indeed continuous in charts) functions on a compact manifold are *)
(* integrable.                                                               *)

let S2E_INTEGRABLE = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f.
     smooth_manifold_atlas top atlas /\ compact_space top /\ riemannian_metric atlas g /\
     (!c. c IN atlas ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c))
     ==> mfd_integrable_on (top,atlas) g f (topspace top)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGT_COMPACT_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
    (X_CHOOSE_THEN `q:num->real^N` STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[mfd_integrable_on] THEN
  MATCH_MP_TAC(MESON[] `(?v:real. P v) ==> (?v. P v)`) THEN
  EXISTS_TAC `sum(1..k) (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                    ((E:num->A->bool) n))
                                 (mfd_chart_integrand atlas (g:A->real^N^N) f (c n))))` THEN
  MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    is_forall(concl th) && s2e_mentions "closed_interval" th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[(p:num->real^N) n,q n]` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `mfd_chart_integrand atlas (g:A->real^N^N) f ((c:num->(A->bool)#(A->real^N)) n) =
      (\y. (f:A->real)(chart_inv (c n) y) % lift(mfd_density atlas (c n) g y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; LIFT_CMUL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\y. (f:A->real)(chart_inv ((c:num->(A->bool)#(A->real^N)) n) y) %
                        lift(mfd_density atlas (c n) (g:A->real^N^N) y)`;
                   `interval[(p:num->real^N) n,q n]`] PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q /\ s) ==> r`) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) (FST(c n))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GRGV_DENSITY_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `mfd_chart_partition atlas (topspace top) (c:num->(A->bool)#(A->real^N))
                                     (E:num->A->bool)` THEN
    REWRITE_TAC[mfd_chart_partition] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Bochner inequality on a closed surface.  Pointwise                    *)
(*   Lap |grad f|^2 >= 2 <grad f, grad Lap f> + R |grad f|^2 + (Lap f)^2     *)
(* (S2E_LBOCHNER2 and S2E_TRACE_SQ_LE2 in the preferred chart), integrated   *)
(* with S2E_IBP twice:  int R |grad f|^2 <= int (Lap f)^2.                   *)
(* ------------------------------------------------------------------------- *)

(* Closure properties of smooth functions on a manifold. *)

let S2E_MFD_SMOOTH_CONST = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c. mfd_smooth atlas (\x:A. lift c)`,
  REWRITE_TAC[mfd_smooth; o_DEF; SMOOTH_MAP_ON_CONST]);;

let S2E_MFD_SMOOTH_ADD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) f g.
     smooth_manifold_atlas top atlas /\
     mfd_smooth atlas (\x. lift(f x)) /\ mfd_smooth atlas (\x. lift(g x))
     ==> mfd_smooth atlas (\x. lift(f x + g x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF; LIFT_ADD] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[MFDM_CHART]);;

let S2E_MFD_SMOOTH_CMUL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) f c.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x))
     ==> mfd_smooth atlas (\x. lift(c * f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF; LIFT_CMUL] THEN STRIP_TAC THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[MFDM_CHART]);;

let S2E_SCALAR_SMOOTH = prove
 (`!(top:A topology) atlas (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> mfd_smooth atlas (\x. lift(mfd_scalar atlas g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) z)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `g:A->real^N^N`; `chart_inv (c:(A->bool)#(A->real^N)) z`] MFD_SCALAR_CHART) THEN
    ASM_SIMP_TAC[PAIR];
    MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let S2E_SMOOTH_INTEGRABLE = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f.
     smooth_manifold_atlas top atlas /\ compact_space top /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(f x))
     ==> mfd_integrable_on (top,atlas) g f (topspace top)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC S2E_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
  REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The inner product with a constant vanishes; symmetry. *)

let S2E_GINNER_CONST = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c b x.
     s2e_ginner atlas g (\x. c) b x = &0`,
  REWRITE_TAC[s2e_ginner; rfa_lginner; RFA_D1_CONST; REAL_MUL_LZERO; REAL_MUL_RZERO;
              SUM_0]);;

let S2E_GINNER_SYM = prove
 (`!(top:A topology) atlas (g:A->real^N^N) a b x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> s2e_ginner atlas g a b x = s2e_ginner atlas g b a x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner] THEN
  MATCH_MP_TAC RFA_LGINNER_SYM THEN
  EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                    (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The pointwise Bochner inequality on a surface. *)

let S2E_MBOCHNER2_GE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) f x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth atlas (\x. lift(f x)) /\ x IN topspace top
     ==> &2 * s2e_ginner atlas g f (rfa_lap atlas g f) x +
         mfd_scalar atlas g x * s2e_ginner atlas g f f x + (rfa_lap atlas g f x) pow 2
         <= rfa_lap atlas g (s2e_ginner atlas g f f) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `cc = chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)` THEN
  ABBREV_TAC `W = IMAGE (SND (cc:(A->bool)#(A->real^2))) (FST cc)` THEN
  ABBREV_TAC `G = metric_local atlas (cc:(A->bool)#(A->real^2)) (g:A->real^2^2)` THEN
  ABBREV_TAC `F0 = \y. (f:A->real)(chart_inv (cc:(A->bool)#(A->real^2)) y)` THEN
  SUBGOAL_THEN `SND (cc:(A->bool)#(A->real^2)) x IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (G:real^2->real^2^2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "G"] THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^2^2)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\z. lift((F0:real^2->real) z))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "F0"] THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the manifold quantities at x in the chart cc *)
  SUBGOAL_THEN
   `rfa_lap atlas (g:A->real^2^2) (s2e_ginner atlas g f f) x =
    llap (G:real^2->real^2^2) (lgrad2 G F0) (SND (cc:(A->bool)#(A->real^2)) x)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[rfa_lap] THEN MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[RFA_LGRAD2_D1] THEN MAP_EVERY EXPAND_TAC ["G"; "F0"] THEN
    MATCH_MP_TAC S2E_GINNER_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s2e_ginner atlas (g:A->real^2^2) f (rfa_lap atlas g f) x =
    rfa_lginner (G:real^2->real^2^2) F0 (llap G F0) (SND (cc:(A->bool)#(A->real^2)) x)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[s2e_ginner] THEN MATCH_MP_TAC S2E_LGINNER_LOCAL THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["G"; "F0"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC S2E_LAP_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s2e_ginner atlas (g:A->real^2^2) f f x =
      lgrad2 (G:real^2->real^2^2) F0 (SND (cc:(A->bool)#(A->real^2)) x) /\
    mfd_scalar atlas g x = lscalar G (SND cc x) /\
    rfa_lap atlas g f x = llap G F0 (SND cc x)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[s2e_ginner; mfd_scalar; rfa_lap; RFA_LGRAD2_D1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `G:real^2->real^2^2`; `F0:real^2->real`;
                 `SND (cc:(A->bool)#(A->real^2)) x`] S2E_LBOCHNER2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `G:real^2->real^2^2`; `F0:real^2->real`;
                 `SND (cc:(A->bool)#(A->real^2)) x`] S2E_LLAP_HESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `G:real^2->real^2^2`;
                 `lnabla 1 (G:real^2->real^2^2) (\z u. rfa_d1 (F0:real^2->real) z (u 1))`;
                 `SND (cc:(A->bool)#(A->real^2)) x`] S2E_TRACE_SQ_LE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W:real^2->bool`; `G:real^2->real^2^2`; `F0:real^2->real`] S2E_DF_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`1`; `W:real^2->bool`; `G:real^2->real^2^2`;
                   `\z:real^2 u:num->real^2. rfa_d1 (F0:real^2->real) z (u 1)`]
                  LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* The integrated Bochner inequality on a closed surface. *)

let S2E_IBOCHNER2 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) f.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(f x))
     ==> mfd_integral (top,atlas) g (topspace top)
           (\x. mfd_scalar atlas g x * s2e_ginner atlas g f f x) <=
         mfd_integral (top,atlas) g (topspace top) (\x. (rfa_lap atlas g f x) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = \x:A. s2e_ginner atlas (g:A->real^2^2) f f x` THEN
  ABBREV_TAC `L = \x:A. rfa_lap atlas (g:A->real^2^2) f x` THEN
  SUBGOAL_THEN `mfd_smooth atlas (\x:A. lift((P:A->real) x)) /\
                mfd_smooth atlas (\x:A. lift((L:A->real) x)) /\
                mfd_smooth atlas (\x:A. lift(mfd_scalar atlas (g:A->real^2^2) x))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "L"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC S2E_GINNER_SMOOTH; MATCH_MP_TAC S2E_LAP_SMOOTH;
      MATCH_MP_TAC S2E_SCALAR_SMOOTH] THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the four integrands are integrable *)
  SUBGOAL_THEN
   `!h:A->real. mfd_smooth atlas (\x. lift(h x))
                ==> mfd_has_integral (top,atlas) (g:A->real^2^2) h (topspace top)
                                     (mfd_integral (top,atlas) g (topspace top) h)`
  (LABEL_TAC "INT") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth atlas (\x:A. lift(mfd_scalar atlas (g:A->real^2^2) x * P x)) /\
    mfd_smooth atlas (\x:A. lift((L:A->real) x pow 2)) /\
    mfd_smooth atlas (\x:A. lift(s2e_ginner atlas (g:A->real^2^2) f L x)) /\
    mfd_smooth atlas (\x:A. lift(rfa_lap atlas (g:A->real^2^2) P x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2E_GINNER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ETA_AX];
      MATCH_MP_TAC S2E_LAP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ETA_AX]];
    ALL_TAC] THEN
  (* int Lap P = 0 *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^2^2) (\x:A. rfa_lap atlas g P x) (topspace top) (&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `\x:A. &1`; `P:A->real`] S2E_IBP) THEN
    ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST; S2E_GINNER_CONST; REAL_MUL_LID; REAL_ADD_RID] THEN
    SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  (* int (L^2 + <grad L, grad f>) = 0 *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^2^2)
      (\x:A. (L:A->real) x pow 2 + s2e_ginner atlas g f L x) (topspace top) (&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `L:A->real`; `f:A->real`] S2E_IBP) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `rfa_lap atlas (g:A->real^2^2) f x = (L:A->real) x` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `L:A->real`; `f:A->real`; `x:A`] S2E_GINNER_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_2];
    ALL_TAC] THEN
  (* the pointwise inequality, integrated *)
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> &2 * s2e_ginner atlas (g:A->real^2^2) f L x + mfd_scalar atlas g x * P x +
              (L:A->real) x pow 2 <= rfa_lap atlas g P x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "L"] THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC S2E_MBOCHNER2_GE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `I2 = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                     (\x:A. s2e_ginner atlas g f L x)` THEN
  ABBREV_TAC `I3 = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                     (\x:A. mfd_scalar atlas g x * P x)` THEN
  ABBREV_TAC `I4 = mfd_integral (top,atlas) (g:A->real^2^2) (topspace top)
                     (\x:A. (L:A->real) x pow 2)` THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^2^2) (\x:A. s2e_ginner atlas g f L x) (topspace top) I2 /\
    mfd_has_integral (top,atlas) g (\x:A. mfd_scalar atlas g x * P x) (topspace top) I3 /\
    mfd_has_integral (top,atlas) g (\x:A. (L:A->real) x pow 2) (topspace top) I4`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["I2"; "I3"; "I4"] THEN REPEAT CONJ_TAC THEN
    USE_THEN "INT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* I4 + I2 = 0 *)
  SUBGOAL_THEN `I4 + I2 = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                          `g:A->real^2^2`;
                          `\x:A. (L:A->real) x pow 2 + s2e_ginner atlas (g:A->real^2^2) f L x`;
                          `topspace (top:A topology)`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `\x:A. (L:A->real) x pow 2`; `\x:A. s2e_ginner atlas (g:A->real^2^2) f L x`;
                   `topspace (top:A topology)`; `I4:real`; `I2:real`] MFD_HAS_INTEGRAL_ADD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* 2 I2 + I3 + I4 <= 0 *)
  SUBGOAL_THEN `&2 * I2 + I3 + I4 <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                          `g:A->real^2^2`;
                          `\x:A. &2 * s2e_ginner atlas (g:A->real^2^2) f L x + mfd_scalar atlas g x * P x +
                                 (L:A->real) x pow 2`;
                          `\x:A. rfa_lap atlas (g:A->real^2^2) P x`;
                          `topspace (top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:A. mfd_scalar atlas (g:A->real^2^2) x * s2e_ginner atlas g f f x) =
    (\x. mfd_scalar atlas g x * P x) /\
    (\x:A. (rfa_lap atlas (g:A->real^2^2) f x) pow 2) = (\x. (L:A->real) x pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["P"; "L"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

