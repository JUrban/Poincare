(* ========================================================================= *)
(* Unit pc_p2b_w920 (Part 2B): the chart-local layer of MT Prop 9.20 (Ch 9   *)
(* Sections 2.3-2.6): Lemma 9.21 (energy convergence, Claim 9.22), Lemma     *)
(* 9.23 (D >= 0, Lipschitz tests), Cor 9.24 (the weight e^-l), the limit of  *)
(* the identity l_tau = (R - |grad l|^2)/2 - l/(2 tau), and the final step   *)
(* (parabolic regularity WAN_CONJ_HEAT_REG; (9.4), (9.5) pointwise).  Main   *)
(* theorems: P2BW_LIMIT, P2BW_REG and P2BW_COEFF_BRIDGE (of the statements   *)
(* P2BW_LIMIT_STATEMENT, P2BW_REG_STATEMENT and                              *)
(* P2BW_COEFF_BRIDGE_STATEMENT), and P2BW_LLAP_DIV, the statement            *)
(* WAN_LLAP_DIV_STATEMENT of pc_wan_defs.  Space-time points z of            *)
(* real^(N,1)finite_sum, backward time tau = drop(sndcart z) > 0;            *)
(* rho = sqrt(det G), A = rho G^-1.  Generic N.  The shared vocabulary is in *)
(* pc_p2b_w3iface.                                                           *)
(* ========================================================================= *)

needs "src/pc_p2b_w3iface.ml";;
needs "src/pc_wan_preg.ml";;
needs "src/pc_wan_lipx.ml";;

prioritize_real();;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* W0. Vocabulary (p2bw_bil, p2bw_t1, p2bw_t2, p2bw_tid: unit             *)
(* pc_p2b_w3iface).                                                          *)
(* ------------------------------------------------------------------------- *)

(* Local uniform convergence and uniform local Lipschitz bounds on om. *)

let p2bw_locunif = new_definition
 `p2bw_locunif (om:real^(N,1)finite_sum->bool) (f:num->real^(N,1)finite_sum->real)
               (f0:real^(N,1)finite_sum->real) <=>
    !k e. compact k /\ k SUBSET om /\ &0 < e
          ==> ?M. !n z. M <= n /\ z IN k ==> abs(f n z - f0 z) < e`;;

let p2bw_locunif_m = new_definition
 `p2bw_locunif_m (om:real^(N,1)finite_sum->bool)
                 (A:num->real^(N,1)finite_sum->real^N^N) (A0:real^(N,1)finite_sum->real^N^N) <=>
    !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> p2bw_locunif om (\n z. A n z$i$j) (\z. A0 z$i$j)`;;

let p2bw_unilip = new_definition
 `p2bw_unilip (om:real^(N,1)finite_sum->bool) (f:num->real^(N,1)finite_sum->real) <=>
    !k. compact k /\ k SUBSET om
        ==> ?L. !n z w. z IN k /\ w IN k ==> abs(f n z - f n w) <= L * norm(z - w)`;;

(* The coefficient class: continuous; A symmetric positive semidefinite;    *)
(* rho nonnegative.                                                          *)

let p2bw_coeff = new_definition
 `p2bw_coeff (om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
             (rho:real^(N,1)finite_sum->real) <=>
    (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A z)) continuous_on om /\
    (\z. lift(rho z)) continuous_on om /\
    !z. z IN om ==> transp(A z) = A z /\ (!v. &0 <= v dot (A z ** v)) /\ &0 <= rho z`;;

(* Nonnegative locally Lipschitz test functions with compact support (the  *)
(* exhaustion cutoffs of MT Cor 9.30 are of this kind; WAN_LIP_TEST_APPROX  *)
(* approximates them by smooth tests).                                       *)

let p2bw_ltest = new_definition
 `p2bw_ltest (om:real^(N,1)finite_sum->bool) (psi:real^(N,1)finite_sum->real) <=>
    wan_loclip om psi /\ (!z. &0 <= psi z) /\
    ?k. compact k /\ k SUBSET om /\ !z. ~(z IN k) ==> psi z = &0`;;

(* U = tau^(-n/2) e^(-l) (MT Section 2.6). *)

let p2bw_uof = new_definition
 `p2bw_uof (l:real^(N,1)finite_sum->real) (z:real^(N,1)finite_sum) =
    exp(--(l z + &(dimindex(:N)) / &2 * log(drop(sndcart z))))`;;

(* U is a weak subsolution of the conjugate heat equation                   *)
(* dU/dtau = Delta U - R U (W(psi) <= 0 for nonnegative Lipschitz tests).    *)

let p2bw_csub = new_definition
 `p2bw_csub (om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
            (rho:real^(N,1)finite_sum->real) (R:real^(N,1)finite_sum->real)
            (U:real^(N,1)finite_sum->real) <=>
    !psi. p2bw_ltest om psi
          ==> drop(integral om (\z. lift(psi z * (wan_tder U z + R z * U z) * rho z +
                                          p2bw_bil A U psi z))) <= &0`;;

(* ------------------------------------------------------------------------- *)
(* W1. The limit lemma (MT Lemmas 9.21, 9.23, Cor 9.24 and the limit of the  *)
(* identity): l_n -> l0 locally uniformly with uniform local Lipschitz       *)
(* bounds, coefficients converging locally uniformly, Thm 7.13 and the a.e. *)
(* identity for each l_n.                                                    *)
(* ------------------------------------------------------------------------- *)

let P2BW_LIMIT_STATEMENT = new_definition
 `P2BW_LIMIT_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) A rho R l A0 rho0 R0 l0.
       open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
       (!m. p2bw_coeff om (A m) (rho m) /\ (\z. lift(R m z)) continuous_on om) /\
       p2bw_coeff om A0 rho0 /\ (\z. lift(R0 z)) continuous_on om /\
       p2bw_locunif_m om A A0 /\ p2bw_locunif om rho rho0 /\ p2bw_locunif om R R0 /\
       p2bw_unilip om l /\ p2bw_locunif om l l0 /\
       (!m. p2bw_t1 om (A m) (rho m) (R m) (l m) /\ p2bw_t2 om (A m) (rho m) (R m) (l m) /\
            p2bw_tid om (A m) (rho m) (R m) (l m))
       ==> wan_loclip om l0 /\
           (!phi. wan_test om phi /\ (!z. &0 <= phi z)
                  ==> ((\m. integral om (\z. lift(phi z * p2bw_bil (A m) (l m) (l m) z))) -->
                       integral om (\z. lift(phi z * p2bw_bil A0 l0 l0 z))) sequentially) /\
           p2bw_t1 om A0 rho0 R0 l0 /\
           p2bw_csub om A0 rho0 R0 (p2bw_uof l0) /\
           (!phi. wan_test om phi /\ (!z. &0 <= phi z)
                  ==> integral om (\z. lift(phi z * wan_tder l0 z * rho0 z)) =
                      integral om (\z. lift(phi z * ((R0 z * rho0 z - p2bw_bil A0 l0 l0 z) / &2 -
                                                     l0 z / (&2 * drop(sndcart z)) * rho0 z))))`;;

(* ------------------------------------------------------------------------- *)
(* W2. The final step (MT p. 198): if U = tau^(-n/2) e^(-l) solves the       *)
(* conjugate heat equation weakly (the global argument of Section 2.6 gives  *)
(* W = 0) and the weak identity holds, then l is smooth and (9.4), (9.5)    *)
(* hold pointwise with the slice operators lgrad2 and llap.                 *)
(* ------------------------------------------------------------------------- *)

let p2bw_slice = new_definition
 `p2bw_slice (G:real^(N,1)finite_sum->real^N^N) (z:real^(N,1)finite_sum) =
    \x:real^N. G(pastecart x (sndcart z))`;;

let p2bw_fslice = new_definition
 `p2bw_fslice (f:real^(N,1)finite_sum->real) (z:real^(N,1)finite_sum) =
    \x:real^N. f(pastecart x (sndcart z))`;;

let P2BW_REG_STATEMENT = new_definition
 `P2BW_REG_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) R l0.
       open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
       smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
       (!z. z IN om ==> transp(G z) = G z /\
                        !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
       smooth_map_on om (\z. lift(R z)) /\ wan_loclip om l0 /\
       (!phi. wan_test om phi
              ==> integral om
                    (\z. lift((phi z * wan_tder (p2bw_uof l0) z + R z * phi z * p2bw_uof l0 z +
                               sum(1..dimindex(:N))
                                  (\i. sum(1..dimindex(:N))
                                         (\j. matrix_inv(G z)$i$j * wan_xder i (p2bw_uof l0) z *
                                              wan_xder j phi z))) *
                              sqrt(det(G z)))) = vec 0) /\
       (!phi. wan_test om phi /\ (!z. &0 <= phi z)
              ==> integral om (\z. lift(phi z * wan_tder l0 z * sqrt(det(G z)))) =
                  integral om
                    (\z. lift(phi z * ((R z * sqrt(det(G z)) -
                                        p2bw_bil (\w. sqrt(det(G w)) %% matrix_inv(G w)) l0 l0 z) / &2 -
                                       l0 z / (&2 * drop(sndcart z)) * sqrt(det(G z))))))
       ==> smooth_map_on om (\z. lift(l0 z)) /\
           !z. z IN om
               ==> wan_tder l0 z + lgrad2 (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) -
                   R z + &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                   llap (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) = &0 /\
                   &2 * llap (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) -
                   lgrad2 (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) + R z +
                   (l0 z - &(dimindex(:N))) / drop(sndcart z) = &0`;;

(* Bridge: metrics converging locally uniformly give the divergence-form     *)
(* coefficients converging locally uniformly (LIM_MATRIX_INV, det).         *)

let P2BW_COEFF_BRIDGE_STATEMENT = new_definition
 `P2BW_COEFF_BRIDGE_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (G:num->real^(N,1)finite_sum->real^N^N) G0.
       open om /\
       (!m. (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (G m z)) continuous_on om) /\
       (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (G0 z)) continuous_on om /\
       (!m z. z IN om ==> transp(G m z) = G m z /\
                          !v. ~(v = vec 0) ==> &0 < v dot (G m z ** v)) /\
       (!z. z IN om ==> transp(G0 z) = G0 z /\
                        !v. ~(v = vec 0) ==> &0 < v dot (G0 z ** v)) /\
       p2bw_locunif_m om G G0
       ==> p2bw_locunif_m om (\m z. sqrt(det(G m z)) %% matrix_inv(G m z))
                              (\z. sqrt(det(G0 z)) %% matrix_inv(G0 z)) /\
           p2bw_locunif om (\m z. sqrt(det(G m z))) (\z. sqrt(det(G0 z))) /\
           (!m. p2bw_coeff om (\z. sqrt(det(G m z)) %% matrix_inv(G m z)) (\z. sqrt(det(G m z)))) /\
           p2bw_coeff om (\z. sqrt(det(G0 z)) %% matrix_inv(G0 z)) (\z. sqrt(det(G0 z)))`;;

(* ------------------------------------------------------------------------- *)
(* The coefficient bridge (P2BW_COEFF_BRIDGE): metrics converging           *)
(* locally uniformly give the divergence-form coefficients rho = sqrt det G *)
(* and A = rho G^-1 converging locally uniformly (compactness argument      *)
(* P2BW_LOCUNIF_COMPOSE with LIM_MATRIX_INV and LIM_LIFT_DET), and their    *)
(* continuity, symmetry and positivity (P2BW_COEFF_CONT).                   *)
(* ------------------------------------------------------------------------- *)

let P2BW_SEQ_SQRT_DET = prove
 (`!(Ms:num->real^N^N) (M0:real^N^N).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> ((\n. lift(Ms n$i$j)) --> lift(M0$i$j)) sequentially)
     ==> ((\n. lift(sqrt(det(Ms n)))) --> lift(sqrt(det M0))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Ms:num->real^N^N`; `M0:real^N^N`; `sequentially`] LIM_LIFT_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lift o sqrt o drop`; `sequentially`;
                 `\n. lift(det((Ms:num->real^N^N) n))`; `lift(det(M0:real^N^N))`]
                LIM_CONTINUOUS_FUNCTION) THEN
  ASM_REWRITE_TAC[CONTINUOUS_AT_SQRT; o_DEF; LIFT_DROP]);;

let P2BW_SEQ_INV_ENTRY = prove
 (`!(Ms:num->real^N^N) (M0:real^N^N) i j.
     ~(det M0 = &0) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> ((\n. lift(Ms n$i$j)) --> lift(M0$i$j)) sequentially) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\n. lift(matrix_inv(Ms n)$i$j)) --> lift(matrix_inv M0$i$j)) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `Ms:num->real^N^N`; `M0:real^N^N`] LIM_MATRIX_INV) THEN
  REWRITE_TAC[LIM_MATRIX_COMPONENTWISE] THEN ASM_SIMP_TAC[]);;

let P2BW_SEQ_COEFF_ENTRY = prove
 (`!(Ms:num->real^N^N) (M0:real^N^N) i j.
     ~(det M0 = &0) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> ((\n. lift(Ms n$i$j)) --> lift(M0$i$j)) sequentially) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\n. lift((sqrt(det(Ms n)) %% matrix_inv(Ms n))$i$j)) -->
          lift((sqrt(det M0) %% matrix_inv M0)$i$j)) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT; LIFT_CMUL] THEN
  MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_SEQ_SQRT_DET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_SEQ_INV_ENTRY THEN ASM_REWRITE_TAC[]]);;

let P2BW_LOCUNIF_COMPOSE = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:num->real^(N,1)finite_sum->real^N^N) G0
    (Fm:real^N^N->real).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(G0 z$i$j)) continuous_on om) /\
     (!z. z IN om ==> &0 < det(G0 z)) /\
     (!(M0:real^N^N) (Ms:num->real^N^N).
        &0 < det M0 /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\n. lift(Ms n$i$j)) --> lift(M0$i$j)) sequentially)
        ==> ((\n. lift(Fm(Ms n))) --> lift(Fm M0)) sequentially) /\
     p2bw_locunif_m om G G0
     ==> p2bw_locunif om (\m z. Fm(G m z)) (\z. Fm(G0 z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_locunif_m; p2bw_locunif] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (CONJUNCTS_THEN2 (LABEL_TAC "det")
    (CONJUNCTS_THEN2 (LABEL_TAC "seq") (LABEL_TAC "unif")))) THEN
  MAP_EVERY X_GEN_TAC [`k:real^(N,1)finite_sum->bool`; `e:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:num->num` (X_CHOOSE_THEN `zz:num->real^(N,1)finite_sum`
    (LABEL_TAC "bad"))) THEN
  SUBGOAL_THEN `!n. (zz:num->real^(N,1)finite_sum) n IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[compact] (ASSUME `compact(k:real^(N,1)finite_sum->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `zz:num->real^(N,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs:real^(N,1)finite_sum` (X_CHOOSE_THEN `r:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(zs:real^(N,1)finite_sum) IN om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> ((\n. lift((G0:real^(N,1)finite_sum->real^N^N) (zz((r:num->num) n))$i$j)) -->
               lift(G0 zs$i$j)) sequentially`
  (LABEL_TAC "c0") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cont" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPECL [`(zz:num->real^(N,1)finite_sum) o (r:num->num)`;
                               `zs:real^(N,1)finite_sum`]) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [GEN_TAC THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> ((\n. lift((G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n))$i$j)) -->
               lift((G0:real^(N,1)finite_sum->real^N^N) zs$i$j)) sequentially`
  (LABEL_TAC "c1") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `((\n. lift((G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n))$i$j) -
            lift((G0:real^(N,1)finite_sum->real^N^N) (zz(r n))$i$j)) --> vec 0) sequentially`
    MP_TAC THENL
     [REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; GSYM LIFT_SUB; NORM_LIFT] THEN
      X_GEN_TAC `d:real` THEN DISCH_TAC THEN
      USE_THEN "unif" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `d:real`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
      EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(r:num->num) n` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `n:num` (MATCH_MP MONOTONE_BIGGER th)));
        USE_THEN "bad" (MP_TAC o SPEC `(r:num->num) n`) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\n. lift((G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n))$i$j) -
                        lift((G0:real^(N,1)finite_sum->real^N^N) (zz(r n))$i$j)`;
                   `\n. lift((G0:real^(N,1)finite_sum->real^N^N) (zz((r:num->num) n))$i$j)`;
                   `vec 0:real^1`; `lift((G0:real^(N,1)finite_sum->real^N^N) zs$i$j)`]
                  LIM_ADD) THEN
    ASM_SIMP_TAC[VECTOR_ADD_LID; VECTOR_SUB_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lift((Fm:real^N^N->real) ((G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n)))) -
          lift(Fm((G0:real^(N,1)finite_sum->real^N^N) (zz(r n))))) --> vec 0) sequentially`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < det((G0:real^(N,1)finite_sum->real^N^N) zs)` ASSUME_TAC THENL
     [USE_THEN "det" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\n. lift((Fm:real^N^N->real) ((G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n))))`;
                   `\n. lift((Fm:real^N^N->real) ((G0:real^(N,1)finite_sum->real^N^N) (zz((r:num->num) n))))`;
                   `lift((Fm:real^N^N->real) ((G0:real^(N,1)finite_sum->real^N^N) zs))`;
                   `lift((Fm:real^N^N->real) ((G0:real^(N,1)finite_sum->real^N^N) zs))`]
                  LIM_SUB) THEN
    REWRITE_TAC[VECTOR_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "seq" (MP_TAC o BETA_RULE o SPECL [`(G0:real^(N,1)finite_sum->real^N^N) zs`;
        `\n. (G:num->real^(N,1)finite_sum->real^N^N) (mm((r:num->num) n)) (zz(r n))`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "seq" (MP_TAC o BETA_RULE o SPECL [`(G0:real^(N,1)finite_sum->real^N^N) zs`;
        `\n. (G0:real^(N,1)finite_sum->real^N^N) (zz((r:num->num) n))`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; GSYM LIFT_SUB; NORM_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_NOT_LT] THEN
  USE_THEN "bad" (MP_TAC o SPEC `(r:num->num) M`) THEN SIMP_TAC[]);;

let P2BW_CONT_COMPOSE = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) (Fm:real^N^N->real).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(G z$i$j)) continuous_on om) /\
     (!z. z IN om ==> &0 < det(G z)) /\
     (!(M0:real^N^N) (Ms:num->real^N^N).
        &0 < det M0 /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\n. lift(Ms n$i$j)) --> lift(M0$i$j)) sequentially)
        ==> ((\n. lift(Fm(Ms n))) --> lift(Fm M0)) sequentially)
     ==> (\z. lift(Fm(G z))) continuous_on om`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (CONJUNCTS_THEN2 (LABEL_TAC "det")
    (LABEL_TAC "seq"))) THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real^(N,1)finite_sum`; `a:real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
  USE_THEN "seq" (MP_TAC o BETA_RULE o SPECL [`(G:real^(N,1)finite_sum->real^N^N) a`;
                                              `\n:num. (G:real^(N,1)finite_sum->real^N^N) ((x:num->real^(N,1)finite_sum) n)`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [USE_THEN "det" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  USE_THEN "cont" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:num->real^(N,1)finite_sum`; `a:real^(N,1)finite_sum`]) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* Pointwise facts of the divergence-form coefficients of a positive definite *)
(* matrix.                                                                    *)

let P2BW_COEFF_POINT = prove
 (`!M:real^N^N.
     transp M = M /\ (!v. ~(v = vec 0) ==> &0 < v dot (M ** v))
     ==> &0 < det M /\
         transp(sqrt(det M) %% matrix_inv M) = sqrt(det M) %% matrix_inv M /\
         (!v. &0 <= v dot ((sqrt(det M) %% matrix_inv M) ** v)) /\
         &0 <= sqrt(det M)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `positive_definite(M:real^N^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[positive_definite; symmetric_matrix]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(M:real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MATRIX_INV] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MP_TAC(ISPEC `M:real^N^N` POSITIVE_DEFINITE_INV) THEN ASM_REWRITE_TAC[positive_definite] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

let P2BW_COEFF_CONT = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N).
     (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (G z)) continuous_on om /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v))
     ==> p2bw_coeff om (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN om ==> &0 < det((G:real^(N,1)finite_sum->real^N^N) z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPEC `(G:real^(N,1)finite_sum->real^N^N) z` P2BW_COEFF_POINT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                   `\M:real^N^N. (sqrt(det M) %% matrix_inv M)$i$j`] P2BW_CONT_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SEQ_COEFF_ENTRY THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                   `\M:real^N^N. sqrt(det M)`] P2BW_CONT_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SEQ_SQRT_DET THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(G:real^(N,1)finite_sum->real^N^N) z` P2BW_COEFF_POINT) THEN
    ASM_SIMP_TAC[]]);;

let P2BW_COEFF_BRIDGE = prove
 (`!n:N->bool. P2BW_COEFF_BRIDGE_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[P2BW_COEFF_BRIDGE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`om:real^(N,1)finite_sum->bool`;
                       `G:num->real^(N,1)finite_sum->real^N^N`;
                       `G0:real^(N,1)finite_sum->real^N^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN om ==> &0 < det((G0:real^(N,1)finite_sum->real^N^N) z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPEC `(G0:real^(N,1)finite_sum->real^N^N) z` P2BW_COEFF_POINT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                      ==> (\z. lift((G0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((G0:real^(N,1)finite_sum->real^N^N) z)) continuous_on om` THEN
    REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2bw_locunif_m] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:num->real^(N,1)finite_sum->real^N^N`;
                   `G0:real^(N,1)finite_sum->real^N^N`;
                   `\M:real^N^N. (sqrt(det M) %% matrix_inv M)$i$j`] P2BW_LOCUNIF_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SEQ_COEFF_ENTRY THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:num->real^(N,1)finite_sum->real^N^N`;
                   `G0:real^(N,1)finite_sum->real^N^N`;
                   `\M:real^N^N. sqrt(det M)`] P2BW_LOCUNIF_COMPOSE) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SEQ_SQRT_DET THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN MATCH_MP_TAC P2BW_COEFF_CONT THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BW_COEFF_CONT THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Analysis plumbing: Lipschitz localization near a compact set             *)
(* (Kirszbraun extensions, P2BW_UNILIP_EXT, P2BW_LOCLIP_EXT,                *)
(* P2BW_LOCALIZE), the bounded measurable representative p2bw_trd of the    *)
(* a.e. derivative, integral bounds, and the weak convergence of            *)
(* derivative-weight products (P2BW_WEAK_PRODUCT_CONV, from W-A and          *)
(* P2BW_DERIV_SMALL_WEIGHT).                                                 *)
(* ------------------------------------------------------------------------- *)

let P2BW_UNILIP_EXT = prove
 (`!(om:real^M->bool) (u:num->real^M->real) k.
     open om /\
     (!kk. compact kk /\ kk SUBSET om
           ==> ?L. !n x y. x IN kk /\ y IN kk ==> abs(u n x - u n y) <= L * norm(x - y)) /\
     compact k /\ k SUBSET om
     ==> ?uu kk ug L. open uu /\ compact kk /\ k SUBSET uu /\ uu SUBSET kk /\ kk SUBSET om /\
                      &0 <= L /\
                      (!n x y. abs(ug n x - ug n y) <= L * norm(x - y)) /\
                      (!n x y. x IN kk /\ y IN kk ==> abs(u n x - u n y) <= L * norm(x - y)) /\
                      (!n x. x IN kk ==> ug n x = u n x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lip") STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "lip" (MP_TAC o SPEC `{x + y:real^M | x IN k /\ y IN cball(vec 0,d)}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `L0:real`)] THEN
  SUBGOAL_THEN
   `!n x y. x IN {x + y:real^M | x IN k /\ y IN cball(vec 0,d)} /\
            y IN {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}
            ==> abs((u:num->real^M->real) n x - u n y) <= abs L0 * norm(x - y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L0 * norm(x - y:real^M)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?gg. !n. (!x y. norm((gg:num->real^M->real^1) n x - gg n y) <= abs L0 * norm(x - y)) /\
             (!x. x IN {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}
                  ==> gg n x = lift((u:num->real^M->real) n x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC KIRSZBRAUN THEN
    ASM_SIMP_TAC[REAL_ABS_POS; GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{x + y:real^M | x IN k /\ y IN ball(vec 0,d)}`;
                        `{x + y:real^M | x IN k /\ y IN cball(vec 0,d)}`;
                        `\n x. drop((gg:num->real^M->real^1) n x)`; `abs L0`] THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LIFT_DROP]]);;

let P2BW_LOCLIP_EXT = prove
 (`!(om:real^M->bool) (u:real^M->real) k.
     open om /\ wan_loclip om u /\ compact k /\ k SUBSET om
     ==> ?uu kk ug L. open uu /\ compact kk /\ k SUBSET uu /\ uu SUBSET kk /\ kk SUBSET om /\
                      &0 <= L /\
                      (!x y. abs(ug x - ug y) <= L * norm(x - y)) /\
                      (!x y. x IN kk /\ y IN kk ==> abs(u x - u y) <= L * norm(x - y)) /\
                      (!x. x IN kk ==> ug x = u x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `\n:num. (u:real^M->real)`; `k:real^M->bool`]
                P2BW_UNILIP_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `wan_loclip om (u:real^M->real)` THEN
    REWRITE_TAC[wan_loclip] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^M->bool` (X_CHOOSE_THEN `kk:real^M->bool`
    (X_CHOOSE_THEN `ug:num->real^M->real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`uu:real^M->bool`; `kk:real^M->bool`;
                        `(ug:num->real^M->real) 0`; `L:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The derivative of u along v at x where u is differentiable, and 0 elsewhere *)
(* (a bounded measurable representative of the a.e. derivative of a         *)
(* Lipschitz function).                                                      *)

let p2bw_trd = new_definition
 `p2bw_trd (u:real^M->real) (v:real^M) (x:real^M) =
    if (\y. lift(u y)) differentiable at x
    then drop(frechet_derivative (\y. lift(u y)) (at x) v) else &0`;;

let P2BW_TRD_FACTS = prove
 (`!(u:real^M->real) L v.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y))
     ==> negligible {x | ~((\y. lift(u y)) differentiable at x)} /\
         (!x. abs(p2bw_trd u v x) <= L * norm v) /\
         (\x. lift(p2bw_trd u v x)) measurable_on (:real^M) /\
         (!x. (\y. lift(u y)) differentiable at x
              ==> p2bw_trd u v x = drop(frechet_derivative (\y. lift(u y)) (at x) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `negligible {x | ~((\y. lift((u:real^M->real) y)) differentiable at x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RADEMACHER_UNIV THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[p2bw_trd] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC WAN_LIP_DERIV_BOUND THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE]];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
    EXISTS_TAC `\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v))` THEN
    EXISTS_TAC `{x | ~((\y. lift((u:real^M->real) y)) differentiable at x)}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; p2bw_trd] THEN SIMP_TAC[];
      MATCH_MP_TAC WAN_LIP_DERIV_MEASURABLE THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[p2bw_trd]]);;

let P2BW_INT_ABS_LE = prove
 (`!(X:real^M->real) k e.
     compact k /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (!x. abs(X x) <= e)
     ==> drop(integral (:real^M) (\x. lift(abs(X x)))) <= e * measure k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measurable(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^M->real`; `e:real`; `k:real^M->bool`] WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(indicator(k:real^M->bool)) integrable_on (:real^M)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTEGRABLE_ON_INDICATOR; INTER_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M) (\x. e % indicator(k:real^M->bool) x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(\x. lift((X:real^M->real) x)) absolutely_integrable_on (:real^M)` THEN
      REWRITE_TAC[absolutely_integrable_on; NORM_LIFT] THEN SIMP_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; DROP_CMUL; indicator] THEN
      COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_MUL_RID; REAL_MUL_RZERO] THEN
      ASM_SIMP_TAC[REAL_ABS_NUM; REAL_LE_REFL]];
    ASM_SIMP_TAC[INTEGRAL_CMUL; ETA_AX] THEN
    ASM_SIMP_TAC[DROP_CMUL; INTEGRAL_INDICATOR; INTER_UNIV; LIFT_DROP; REAL_LE_REFL]]);;

let P2BW_ARITH_CHAIN = prove
 (`!L n J q mu e b.
     &0 <= L /\ &0 <= n /\ b <= L * n * J /\ J <= q * mu /\ L * n * mu * q < e ==> b < e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `L * n * q * mu` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * n * J` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `L * n * q * mu = L * n * mu * q` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let P2BW_DERIV_SMALL_WEIGHT = prove
 (`!(u:num->real^M->real) L (X:num->real^M->real) k v.
     &0 <= L /\ (!m x y. abs(u m x - u m y) <= L * norm(x - y)) /\ compact k /\
     (!m x. ~(x IN k) ==> X m x = &0) /\ (!m. (\x. lift(X m x)) measurable_on (:real^M)) /\
     (!e. &0 < e ==> ?N. !m x. N <= m ==> abs(X m x) < e)
     ==> ((\m. integral (:real^M)
                 (\x. lift(drop(frechet_derivative (\y. lift(u m y)) (at x) v) * X m x)))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `c = L * norm(v:real^M) * measure(k:real^M->bool) + &1` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; MEASURE_POS_LE; MEASURABLE_COMPACT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / c`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. abs((X:num->real^M->real) m x) <= e / &2 / c` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:num->real^M->real) m`; `L:real`; `(X:num->real^M->real) m`;
                 `e / &2 / c`; `k:real^M->bool`; `v:real^M`] WAN_LIP_DERIV_TIMES_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`(X:num->real^M->real) m`; `k:real^M->bool`; `e / &2 / c`] P2BW_INT_ABS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `L * norm(v:real^M) * measure(k:real^M->bool) * (e / &2 / c) < e`
  MP_TAC THENL
   [SUBGOAL_THEN `L * norm(v:real^M) * measure(k:real^M->bool) * (e / &2 / c) =
                  (L * norm v * measure k) / c * (e / &2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * e / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN EXPAND_TAC "c" THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC P2BW_ARITH_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`L:real`; `norm(v:real^M)`;
                        `drop(integral (:real^M) (\x. lift(abs((X:num->real^M->real) m x))))`;
                        `e / &2 / c`; `measure(k:real^M->bool)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE]);;

let P2BW_LDTB_INT = prove
 (`!(u:real^M->real) L (X:real^M->real) B k v.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y)) /\ compact k /\
     (!x. ~(x IN k) ==> X x = &0) /\ (\x. lift(X x)) measurable_on (:real^M) /\
     (!x. abs(X x) <= B)
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * X x))
           integrable_on (:real^M)`,
  MESON_TAC[WAN_LIP_DERIV_TIMES_BOUNDED]);;

let P2BW_WEAK_PRODUCT_CONV = prove
 (`!(u:num->real^M->real) u0 L (W:num->real^M->real) W0 (Y:real^M->real) B BW k kk d v.
     &0 <= L /\ (!m x y. abs(u m x - u m y) <= L * norm(x - y)) /\
     (!x y. abs(u0 x - u0 y) <= L * norm(x - y)) /\
     compact k /\ &0 < d /\ {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET kk /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN kk ==> abs(u m x - u0 x) < e) /\
     (!m x. ~(x IN k) ==> W m x = &0) /\ (!x. ~(x IN k) ==> W0 x = &0) /\
     (!m. (\x. lift(W m x)) measurable_on (:real^M)) /\ (\x. lift(W0 x)) measurable_on (:real^M) /\
     (!m x. abs(W m x) <= BW) /\ (!x. abs(W0 x) <= BW) /\
     (!e. &0 < e ==> ?N. !m x. N <= m ==> abs(W m x - W0 x) < e) /\
     (\x. lift(Y x)) measurable_on (:real^M) /\ (!x. abs(Y x) <= B)
     ==> ((\m. integral (:real^M)
                 (\x. lift(drop(frechet_derivative (\y. lift(u m y)) (at x) v) * (W m x * Y x)))) -->
          integral (:real^M)
            (\x. lift(drop(frechet_derivative (\y. lift(u0 y)) (at x) v) * (W0 x * Y x))))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= BW /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `abs((W0:real^M->real) (vec 0))`;
      EXISTS_TAC `abs((Y:real^M->real) (vec 0))`] THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (\x. lift(((W:num->real^M->real) m x - W0 x) * Y x)) measurable_on (:real^M) /\
        (\x. lift((W0:real^M->real) x * Y x)) measurable_on (:real^M) /\
        (\x. lift((W:num->real^M->real) m x * Y x)) measurable_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN
    ASM_REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m x. abs(((W:num->real^M->real) m x - W0 x) * Y x) <= (BW + BW) * B /\
          abs((W0:real^M->real) x * Y x) <= BW * B /\
          abs((W:num->real^M->real) m x * Y x) <= BW * B`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs a <= b /\ abs c <= b ==> abs(a - c) <= b + b`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W:num->real^M->real) m x * Y x))) =
        integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W m x - W0 x) * Y x))) +
        integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W0:real^M->real) x * Y x)))`
  (LABEL_TAC "split") THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral (:real^M)
                  (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * (((W:num->real^M->real) m x - W0 x) * Y x)) +
                       lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W0:real^M->real) x * Y x)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD] THEN GEN_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN MATCH_MP_TAC P2BW_LDTB_INT THEN
      EXISTS_TAC `L:real` THENL
       [EXISTS_TAC `(BW + BW) * B`; EXISTS_TAC `BW * B`] THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[REAL_SUB_REFL; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\m. integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * (((W:num->real^M->real) m x - W0 x) * Y x)))) -->
     vec 0) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_DERIV_SMALL_WEIGHT THEN
    MAP_EVERY EXISTS_TAC [`L:real`; `k:real^M->bool`] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (B + &1)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `(W0:real^M->real)`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th) &&
      not (can (find_term (fun t -> t = `(u0:real^M->real)`)) (concl th)))) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `x:real^M`] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / (B + &1) * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
      SUBGOAL_THEN `e / (B + &1) * B = e * (B / (B + &1))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 <= B` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * x < e * &1 ==> e * x < e`) THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= B ==> &0 < B + &1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\m. integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W0:real^M->real) x * Y x)))) -->
     integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u0:real^M->real) y)) (at x) v) * ((W0:real^M->real) x * Y x)))) sequentially`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[LIM_NULL] THEN
    MP_TAC(ISPECL [`u:num->real^M->real`; `u0:real^M->real`; `\x. (W0:real^M->real) x * Y x`;
                   `BW * B`; `k:real^M->bool`; `kk:real^M->bool`; `L:real`; `v:real^M`; `d:real`]
                  WAN_LIP_DERIV_WEAK_CONV_GLOBAL) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
    MP_TAC(ISPECL [`(u:num->real^M->real) m`; `u0:real^M->real`; `L:real`;
                   `\x. (W0:real^M->real) x * Y x`; `BW * B`; `k:real^M->bool`; `v:real^M`]
                  WAN_LIP_DIFF_TIMES_BOUNDED) THEN
    BETA_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\m. integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * (((W:num->real^M->real) m x - W0 x) * Y x)))`;
                 `\m. integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) m y)) (at x) v) * ((W0:real^M->real) x * Y x)))`;
                 `vec 0:real^1`;
                 `integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift((u0:real^M->real) y)) (at x) v) * ((W0:real^M->real) x * Y x)))`] LIM_ADD) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID]);;

let P2BW_LOCALIZE = prove
 (`!(om:real^M->bool) (l:num->real^M->real) l0 k.
     open om /\
     (!kk. compact kk /\ kk SUBSET om
           ==> ?L. !m x y. x IN kk /\ y IN kk ==> abs(l m x - l m y) <= L * norm(x - y)) /\
     (!kk e. compact kk /\ kk SUBSET om /\ &0 < e
             ==> ?N. !m x. N <= m /\ x IN kk ==> abs(l m x - l0 x) < e) /\
     compact k /\ k SUBSET om
     ==> ?d lg lg0 L.
           &0 < d /\ &0 <= L /\
           compact {x + y | x IN k /\ y IN cball(vec 0,d)} /\
           {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET om /\
           open {x + y | x IN k /\ y IN ball(vec 0,d)} /\
           k SUBSET {x + y | x IN k /\ y IN ball(vec 0,d)} /\
           {x + y | x IN k /\ y IN ball(vec 0,d)} SUBSET {x + y | x IN k /\ y IN cball(vec 0,d)} /\
           (!m x y. abs(lg m x - lg m y) <= L * norm(x - y)) /\
           (!x y. abs(lg0 x - lg0 y) <= L * norm(x - y)) /\
           (!m x. x IN {x + y | x IN k /\ y IN cball(vec 0,d)} ==> lg m x = l m x) /\
           (!x. x IN {x + y | x IN k /\ y IN cball(vec 0,d)} ==> lg0 x = l0 x) /\
           (!e. &0 < e
                ==> ?N. !m x. N <= m /\ x IN {x + y | x IN k /\ y IN cball(vec 0,d)}
                              ==> abs(lg m x - lg0 x) < e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip")
   (CONJUNCTS_THEN2 (LABEL_TAC "conv") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  ABBREV_TAC `uu = {x + y:real^M | x IN k /\ y IN ball(vec 0,d)}` THEN
  STRIP_TAC THEN
  USE_THEN "lip" (MP_TAC o SPEC `kk:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `L0:real`)] THEN
  ABBREV_TAC `L = abs L0` THEN
  SUBGOAL_THEN
   `&0 <= L /\
    !m x y. x IN kk /\ y IN kk
            ==> abs((l:num->real^M->real) m x - l m y) <= L * norm(x - y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L0 * norm(x - y:real^M)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !m x. N <= m /\ x IN kk ==> abs((l:num->real^M->real) m x - l0 x) < e`
  (LABEL_TAC "ukk") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPECL [`kk:real^M->bool`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN kk /\ y IN kk ==> abs((l0:real^M->real) x - l0 y) <= L * norm(x - y)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `e3 = (abs((l0:real^M->real) x - l0 y) - L * norm(x - y:real^M)) / &3` THEN
    SUBGOAL_THEN `&0 < e3` ASSUME_TAC THENL [EXPAND_TAC "e3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ukk" (fun th -> X_CHOOSE_TAC `N:num` (MATCH_MP th (ASSUME `&0 < e3`))) THEN
    SUBGOAL_THEN
     `abs((l:num->real^M->real) N x - l0 x) < e3 /\ abs(l N y - l0 y) < e3`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((l:num->real^M->real) N x - l N y) <= L * norm(x - y:real^M)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?G. !m. (!x y. norm((G:num->real^M->real^1) m x - G m y) <= L * norm(x - y)) /\
            (!x. x IN kk ==> G m x = lift((l:num->real^M->real) m x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `m:num` THEN
    MATCH_MP_TAC KIRSZBRAUN THEN ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g0. (!x y. norm((g0:real^M->real^1) x - g0 y) <= L * norm(x - y)) /\
         (!x. x IN kk ==> g0 x = lift((l0:real^M->real) x))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC KIRSZBRAUN THEN ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `\m x. drop((G:num->real^M->real^1) m x)`;
                        `\x. drop((g0:real^M->real^1) x)`; `L:real`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1] THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "ukk" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM LIFT_SUB; NORM_LIFT; DROP_SUB]);;

(* ------------------------------------------------------------------------- *)
(* Locally essentially bounded measurable functions (p2bw_lebm) and the     *)
(* extension of weak inequalities from smooth to Lipschitz nonnegative      *)
(* tests (P2BW_LTEST_EXT, via W-B WAN_LIP_TEST_APPROX).                      *)
(* ------------------------------------------------------------------------- *)

(* fz is locally essentially bounded and measurable on om (L^infinity_loc):  *)
(* on every compact k inside om it agrees almost everywhere with a bounded   *)
(* measurable function.                                                       *)

let p2bw_lebm = new_definition
 `p2bw_lebm (om:real^M->bool) (fz:real^M->real) <=>
    !k. compact k /\ k SUBSET om
        ==> ?G B. (\x. lift(G x)) measurable_on (:real^M) /\ (!x. abs(G x) <= B) /\
                  negligible {x | x IN k /\ ~(fz x = G x)}`;;

let P2BW_LEBM_CONT = prove
 (`!(om:real^M->bool) fz. (\x. lift(fz x)) continuous_on om ==> p2bw_lebm om fz`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_lebm] THEN X_GEN_TAC `k:real^M->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((fz:real^M->real) x)) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((fz:real^M->real) x)`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. if x IN k then (fz:real^M->real) x else &0` THEN EXISTS_TAC `B:real` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COND_RAND; LIFT_NUM] THEN REWRITE_TAC[MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    GEN_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_ABS_NUM; REAL_LT_IMP_LE];
    MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(s:real^M->bool) = {} ==> negligible s`) THEN
    SIMP_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BW_LEBM_LIPDER = prove
 (`!(om:real^M->bool) u v.
     open om /\ wan_loclip om u
     ==> p2bw_lebm om (\x. drop(frechet_derivative (\y. lift(u y)) (at x) v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_lebm] THEN X_GEN_TAC `k:real^M->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `u:real^M->real`; `k:real^M->bool`] P2BW_LOCLIP_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^M->bool` (X_CHOOSE_THEN `kk:real^M->bool`
    (X_CHOOSE_THEN `ug:real^M->real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`ug:real^M->real`; `L:real`; `v:real^M`] P2BW_TRD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `p2bw_trd (ug:real^M->real) v` THEN EXISTS_TAC `L * norm(v:real^M)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | ~((\y. lift((ug:real^M->real) y)) differentiable at x)}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[TAUT `(a /\ ~b) ==> ~c <=> a /\ c ==> b`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN uu` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift((u:real^M->real) y)) (at x) =
    frechet_derivative (\y. lift((ug:real^M->real) y)) (at x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `uu:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^M) IN kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let P2BW_LEBM_ADD = prove
 (`!(om:real^M->bool) f g.
     p2bw_lebm om f /\ p2bw_lebm om g ==> p2bw_lebm om (\x. f x + g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_lebm] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G1:real^M->real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `G2:real^M->real` (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. (G1:real^M->real) x + G2 x` THEN EXISTS_TAC `B1 + B2:real` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs a <= b /\ abs c <= d ==> abs(a + c) <= b + d`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN k /\ ~((f:real^M->real) x = G1 x)} UNION
                {x | x IN k /\ ~((g:real^M->real) x = G2 x)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN SET_TAC[]]);;

let P2BW_LEBM_MUL = prove
 (`!(om:real^M->bool) f g.
     p2bw_lebm om f /\ p2bw_lebm om g ==> p2bw_lebm om (\x. f x * g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_lebm] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G1:real^M->real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `G2:real^M->real` (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. (G1:real^M->real) x * G2 x` THEN EXISTS_TAC `B1 * B2:real` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN k /\ ~((f:real^M->real) x = G1 x)} UNION
                {x | x IN k /\ ~((g:real^M->real) x = G2 x)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

let P2BW_LEBM_CMUL = prove
 (`!(om:real^M->bool) c f. p2bw_lebm om f ==> p2bw_lebm om (\x. c * f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `\x:real^M. c:real`; `f:real^M->real`] P2BW_LEBM_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P2BW_LEBM_CONT THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST]);;

let P2BW_LEBM_SUB = prove
 (`!(om:real^M->bool) f g.
     p2bw_lebm om f /\ p2bw_lebm om g ==> p2bw_lebm om (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^M->real) x - g x) = (\x. f x + --(&1) * g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `f:real^M->real`; `\x. --(&1) * (g:real^M->real) x`]
                P2BW_LEBM_ADD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[P2BW_LEBM_CMUL]);;

let P2BW_LEBM_SUM = prove
 (`!(om:real^M->bool) (f:num->real^M->real) n.
     (!j. 1 <= j /\ j <= n ==> p2bw_lebm om (f j))
     ==> p2bw_lebm om (\x. sum(1..n) (\j. f j x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [DISCH_TAC THEN REWRITE_TAC[ARITH] THEN MATCH_MP_TAC P2BW_LEBM_CONT THEN
    REWRITE_TAC[LIFT_NUM; CONTINUOUS_ON_CONST];
    DISCH_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
    MP_TAC(ISPECL [`om:real^M->bool`; `\x. sum(1..n) (\j. (f:num->real^M->real) j x)`;
                   `(f:num->real^M->real) (SUC n)`] P2BW_LEBM_ADD) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

let P2BW_LEBM_L1BOUND = prove
 (`!(om:real^M->bool) h k.
     open om /\ p2bw_lebm om h /\ compact k /\ k SUBSET om
     ==> ?B. &0 <= B /\
             !g. (\x. lift(g x)) absolutely_integrable_on (:real^M) /\
                 (!x. ~(x IN k) ==> g x = &0)
                 ==> (\x. lift(g x * h x)) absolutely_integrable_on (:real^M) /\
                     (\x. lift(g x * h x)) absolutely_integrable_on om /\
                     integral om (\x. lift(g x * h x)) =
                     integral (:real^M) (\x. lift(g x * h x)) /\
                     abs(drop(integral om (\x. lift(g x * h x)))) <=
                     B * drop(integral (:real^M) (\x. lift(abs(g x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bw_lebm om (h:real^M->real)` THEN REWRITE_TAC[p2bw_lebm] THEN
  DISCH_THEN(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^M->real` (X_CHOOSE_THEN `B0:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `abs B0` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  X_GEN_TAC `g:real^M->real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(abs((g:real^M->real) x))) integrable_on (:real^M)` ASSUME_TAC THENL
   [UNDISCH_TAC `(\x. lift((g:real^M->real) x)) absolutely_integrable_on (:real^M)` THEN
    REWRITE_TAC[absolutely_integrable_on; NORM_LIFT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((g:real^M->real) x * G x)) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. abs B0 % lift(abs((g:real^M->real) x))` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP; REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B0:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | ~(lift((g:real^M->real) x * h x) = lift(g x * G x))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN k /\ ~((h:real^M->real) x = G x)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN k` THEN ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((g:real^M->real) x * h x)) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\x. lift((g:real^M->real) x * G x)` THEN
    EXISTS_TAC `{x | ~(lift((g:real^M->real) x * h x) = lift(g x * G x))}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\x. lift((g:real^M->real) x * h x)) = integral (:real^M) (\x. lift(g x * h x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; REAL_MUL_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^M)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^M) (\x. lift((g:real^M->real) x * h x)) =
    integral (:real^M) (\x. lift(g x * G x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | ~(lift((g:real^M->real) x * h x) = lift(g x * G x))}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M) (\x. abs B0 % lift(abs((g:real^M->real) x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP; REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B0:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]]);;

let P2BW_LIP_DER_ABSINT = prove
 (`!(u:real^M->real) L k v.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y)) /\ compact k /\
     (!x. ~(x IN k) ==> u x = &0)
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v)))
           absolutely_integrable_on (:real^M) /\
         (!x. ~(x IN k) ==> drop(frechet_derivative (\y. lift(u y)) (at x) v) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~(x IN k) ==> drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\y. lift((u:real^M->real) y)`; `k:real^M->bool`; `x:real^M`]
                  WAN_FRECHET_ZERO_OUTSIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; LIFT_NUM; DROP_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`u:real^M->real`; `L:real`; `v:real^M`] P2BW_TRD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  EXISTS_TAC `\x. lift(p2bw_trd (u:real^M->real) v x)` THEN
  EXISTS_TAC `{x | ~((\y. lift((u:real^M->real) y)) differentiable at x)}` THEN
  ASM_SIMP_TAC[IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
  MP_TAC(ISPECL [`p2bw_trd (u:real^M->real) v`; `L * norm(v:real^M)`; `k:real^M->bool`]
                WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[p2bw_trd] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let P2BW_ARITH_DIV = prove
 (`!B e x y. &0 <= B /\ &0 < e /\ &0 <= y /\ y < e / (B + &1) /\ x <= B * y ==> x < e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * (e / (B + &1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    SUBGOAL_THEN `B * (e / (B + &1)) = e * (B / (B + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= B` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * x < e * &1 ==> e * x < e`) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= B ==> &0 < B + &1`] THEN
    REAL_ARITH_TAC]);;

let P2BW_L1_CONV_PAIRING = prove
 (`!(om:real^M->bool) h k (g:num->real^M->real) g0.
     open om /\ p2bw_lebm om h /\ compact k /\ k SUBSET om /\
     (!n. (\x. lift(g n x)) absolutely_integrable_on (:real^M)) /\
     (\x. lift(g0 x)) absolutely_integrable_on (:real^M) /\
     (!n x. ~(x IN k) ==> g n x = &0) /\ (!x. ~(x IN k) ==> g0 x = &0) /\
     ((\n. integral (:real^M) (\x. lift(abs(g n x - g0 x)))) --> vec 0) sequentially
     ==> ((\n. integral om (\x. lift(g n x * h x))) --> integral om (\x. lift(g0 x * h x)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `h:real^M->real`; `k:real^M->bool`] P2BW_LEBM_L1BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "bd"))) THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN
  SUBGOAL_THEN
   `!n. integral om (\x. lift((g:num->real^M->real) n x * h x)) - integral om (\x. lift(g0 x * h x)) =
        integral om (\x. lift((g n x - g0 x) * h x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `(g:num->real^M->real) n`) THEN
    USE_THEN "bd" (MP_TAC o SPEC `g0:real^M->real`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; LIFT_SUB] THEN
    MATCH_MP_TAC(GSYM INTEGRAL_SUB) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY] o check (fun th ->
    can (find_term (fun t -> t = `(g0:real^M->real)`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `e / (B + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[DIST_0; NORM_1; DROP_SUB] THEN
  REWRITE_TAC[DROP_VEC; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  USE_THEN "bd" (MP_TAC o SPEC `\x. (g:num->real^M->real) n x - g0 x`) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; LIFT_SUB] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 <= drop(integral (:real^M) (\x. lift(abs((g:num->real^M->real) n x - g0 x))))`
  MP_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM NORM_LIFT; LIFT_SUB] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_1] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC P2BW_ARITH_DIV THEN
  MAP_EVERY EXISTS_TAC
   [`B:real`; `drop(integral (:real^M) (\x. lift(abs((g:num->real^M->real) n x - g0 x))))`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BW_UNIF_L1_CONV = prove
 (`!(g:num->real^M->real) g0 k.
     compact k /\ (!n x. ~(x IN k) ==> g n x = &0) /\ (!x. ~(x IN k) ==> g0 x = &0) /\
     (!n. (\x. lift(g n x)) measurable_on (:real^M)) /\ (\x. lift(g0 x)) measurable_on (:real^M) /\
     (!e. &0 < e ==> ?N. !n x. N <= n ==> abs(g n x - g0 x) < e)
     ==> ((\n. integral (:real^M) (\x. lift(abs(g n x - g0 x)))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= measure(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / (measure(k:real^M->bool) + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. (g:num->real^M->real) n x - g0 x`; `k:real^M->bool`;
                 `e / &2 / (measure(k:real^M->bool) + &1)`] P2BW_INT_ABS_LE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; LIFT_SUB; MEASURABLE_ON_SUB] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop(integral (:real^M) (\x. lift(abs((g:num->real^M->real) n x - g0 x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_ABS_POS] THEN
    MP_TAC(ISPECL [`\x. (g:num->real^M->real) n x - g0 x`;
                   `e / &2 / (measure(k:real^M->bool) + &1)`; `k:real^M->bool`]
                  WAN_BOUNDED_MEASURABLE_FACTS) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_SUB_REFL; LIFT_SUB; MEASURABLE_ON_SUB] THEN
      GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[absolutely_integrable_on; NORM_LIFT] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_1] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!x y e. &0 <= x /\ x <= y /\ y < e ==> abs x < e`) THEN
  EXISTS_TAC `e / &2 / (measure(k:real^M->bool) + &1) * measure(k:real^M->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e / &2 / (measure(k:real^M->bool) + &1) * measure k =
                e / &2 * (measure k / (measure k + &1))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 <= measure(k:real^M->bool)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 * &1 ==> x < e`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= m ==> &0 < m + &1`] THEN
  ASM_REAL_ARITH_TAC);;

let P2BW_DECOMP = prove
 (`!(om:real^M->bool) (fz:real^M->real) (H:num->real^M->real) (vv:num->real^M) n K2
    (phi:real^M->real).
     open om /\ p2bw_lebm om fz /\ (!j. 1 <= j /\ j <= n ==> p2bw_lebm om (H j)) /\
     compact K2 /\ K2 SUBSET om /\
     (\x. lift(phi x)) absolutely_integrable_on (:real^M) /\ (!x. ~(x IN K2) ==> phi x = &0) /\
     (!j. (\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j))))
            absolutely_integrable_on (:real^M) /\
          (!x. ~(x IN K2) ==> drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j)) = &0))
     ==> (\x. lift(phi x * fz x)) integrable_on om /\
         (!j. 1 <= j /\ j <= n
              ==> (\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j)) * H j x))
                    integrable_on om) /\
         integral om
           (\x. lift(phi x * fz x +
                     sum(1..n) (\j. drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j)) *
                                    H j x))) =
         integral om (\x. lift(phi x * fz x)) +
         vsum(1..n) (\j. integral om
                           (\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j)) *
                                     H j x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x * fz x)) integrable_on om` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^M->bool`; `fz:real^M->real`; `K2:real^M->bool`] P2BW_LEBM_L1BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (MP_TAC o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^M->real`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> (\x. lift(drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) (vv j)) *
                      (H:num->real^M->real) j x)) integrable_on om`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^M->bool`; `(H:num->real^M->real) j`; `K2:real^M->bool`]
                  P2BW_LEBM_L1BOUND) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (MP_TAC o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o SPEC
      `\x. drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) (vv(j:num)))`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\x. lift((phi:real^M->real) x * fz x)`;
                 `\x. vsum(1..n) (\j. lift(drop(frechet_derivative (\y. lift((phi:real^M->real) y))
                                                (at x) (vv j)) * (H:num->real^M->real) j x))`;
                 `om:real^M->bool`] INTEGRAL_ADD) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\j x. lift(drop(frechet_derivative (\y. lift((phi:real^M->real) y))
                                   (at x) (vv j)) * (H:num->real^M->real) j x)`;
                 `om:real^M->bool`; `1..n`] INTEGRAL_VSUM) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX];
    SIMP_TAC[ETA_AX]]);;

let P2BW_LIP_SUPPORT_ABSINT = prove
 (`!(u:real^M->real) L k.
     (!x y. abs(u x - u y) <= L * norm(x - y)) /\ compact k /\ (!x. ~(x IN k) ==> u x = &0)
     ==> (\x. lift(u x)) absolutely_integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((u:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(abs((u:real^M->real) x))` THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; NORM_LIFT; LIFT_DROP; REAL_LE_REFL] THEN
  MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[REAL_ABS_NUM; LIFT_NUM] THEN
  REWRITE_TAC[GSYM NORM_LIFT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]);;

let P2BW_LTEST_EXT = prove
 (`!(om:real^M->bool) (fz:real^M->real) (H:num->real^M->real) (vv:num->real^M) n.
     open om /\ p2bw_lebm om fz /\ (!j. 1 <= j /\ j <= n ==> p2bw_lebm om (H j)) /\
     (!phi. wan_test om phi /\ (!x. &0 <= phi x)
            ==> drop(integral om
                  (\x. lift(phi x * fz x +
                            sum(1..n) (\j. drop(frechet_derivative (\y. lift(phi y)) (at x) (vv j)) *
                                           H j x)))) <= &0)
     ==> !psi. wan_loclip om psi /\ (!x. &0 <= psi x) /\
               (?k. compact k /\ k SUBSET om /\ !x. ~(x IN k) ==> psi x = &0)
               ==> drop(integral om
                     (\x. lift(psi x * fz x +
                               sum(1..n) (\j. drop(frechet_derivative (\y. lift(psi y)) (at x) (vv j)) *
                                              H j x)))) <= &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp")))) THEN
  X_GEN_TAC `psi:real^M->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `psi:real^M->real`; `k:real^M->bool`] WAN_LIP_TEST_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `L0:real`
    (X_CHOOSE_THEN `ph:num->real^M->real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `psi:real^M->real`; `k:real^M->bool`]
                WAN_LOCLIP_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Lp:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K2 = (k:real^M->bool) UNION k1` THEN
  SUBGOAL_THEN `compact(K2:real^M->bool) /\ K2 SUBSET om /\ k SUBSET K2 /\ k1 SUBSET K2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN ASM_SIMP_TAC[COMPACT_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m x y. abs((ph:num->real^M->real) m x - ph m y) <= abs L0 * norm(x - y)) /\
    (!x y. abs((psi:real^M->real) x - psi y) <= abs Lp * norm(x - y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `L0 * norm(x - y:real^M)`; EXISTS_TAC `Lp * norm(x - y:real^M)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m x. ~(x IN K2) ==> (ph:num->real^M->real) m x = &0) /\
    (!x. ~(x IN K2) ==> (psi:real^M->real) x = &0)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* the derivative terms are absolutely integrable and vanish off K2 *)
  SUBGOAL_THEN
   `!v. (!m. (\x. lift(drop(frechet_derivative (\y. lift((ph:num->real^M->real) m y)) (at x) v)))
               absolutely_integrable_on (:real^M) /\
             (!x. ~(x IN K2) ==> drop(frechet_derivative (\y. lift(ph m y)) (at x) v) = &0)) /\
        (\x. lift(drop(frechet_derivative (\y. lift((psi:real^M->real) y)) (at x) v)))
          absolutely_integrable_on (:real^M) /\
        (!x. ~(x IN K2) ==> drop(frechet_derivative (\y. lift(psi y)) (at x) v) = &0)`
  (LABEL_TAC "dv") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BW_LIP_DER_ABSINT THEN EXISTS_TAC `abs L0` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC P2BW_LIP_DER_ABSINT THEN EXISTS_TAC `abs Lp` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m. (\x. lift((ph:num->real^M->real) m x)) absolutely_integrable_on (:real^M)) /\
    (\x. lift((psi:real^M->real) x)) absolutely_integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BW_LIP_SUPPORT_ABSINT THENL
     [EXISTS_TAC `abs L0`; EXISTS_TAC `abs Lp`] THEN
    EXISTS_TAC `K2:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* decompositions *)
  SUBGOAL_THEN
   `!m. integral om
          (\x. lift((ph:num->real^M->real) m x * fz x +
                    sum(1..n) (\j. drop(frechet_derivative (\y. lift((ph:num->real^M->real) m y)) (at x) (vv j)) * (H:num->real^M->real) j x))) =
        integral om (\x. lift(ph m x * fz x)) +
        vsum(1..n) (\j. integral om (\x. lift(drop(frechet_derivative (\y. lift((ph:num->real^M->real) m y)) (at x) (vv j)) * H j x)))`
  (LABEL_TAC "dm") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`om:real^M->bool`; `fz:real^M->real`; `H:num->real^M->real`;
                   `vv:num->real^M`; `n:num`; `K2:real^M->bool`;
                   `(ph:num->real^M->real) m`] P2BW_DECOMP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `fz:real^M->real`; `H:num->real^M->real`;
                 `vv:num->real^M`; `n:num`; `K2:real^M->bool`; `psi:real^M->real`] P2BW_DECOMP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND) THEN
  EXISTS_TAC `\m. integral om (\x. lift((ph:num->real^M->real) m x * fz x)) +
                  vsum(1..n) (\j. integral om (\x. lift(drop(frechet_derivative (\y. lift((ph:num->real^M->real) m y)) (at x) (vv j)) * (H:num->real^M->real) j x)))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_L1_CONV_PAIRING THEN EXISTS_TAC `K2:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_UNIF_L1_CONV THEN
      EXISTS_TAC `K2:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; INTEGRABLE_IMP_MEASURABLE];
      MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BW_L1_CONV_PAIRING THEN EXISTS_TAC `K2:real^M->bool` THEN
      ASM_SIMP_TAC[ETA_AX]];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "dm" (SUBST1_TAC o SYM o SPEC `m:num`) THEN
    USE_THEN "hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Energy convergence in the global (Lipschitz-extended) setting:           *)
(* positivity P2BW_QUAD_PSD, the split of divergence-form integrals         *)
(* P2BW_BIL_SPLIT, their convergence P2BW_BIL_CONV (W-A), and               *)
(* P2BW_ENERGY_GLOBAL (lower bound by convexity, upper bound supplied by    *)
(* Claim 9.22).                                                              *)
(* ------------------------------------------------------------------------- *)

let P2BW_QUAD_PSD = prove
 (`!(A:real^N^N) (a:num->real) (b:num->real).
     transp A = A /\ (!v. &0 <= v dot (A ** v))
     ==> &2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * a i * b j)) -
         sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * b i * b j))
         <= sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * a i * a j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (A:real^N^N)$j$i = A$i$j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(transp(A:real^N^N))$i$j = A$i$j` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[TRANSP_COMPONENT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. a i - b i):real^N`) THEN
  SUBGOAL_THEN
   `((lambda i. a i - b i):real^N) dot ((A:real^N^N) ** (lambda i. a i - b i)) =
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * a i * a j)) -
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * a i * b j)) -
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * b i * a j)) +
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * b i * b j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[dot] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN REWRITE_TAC[dot] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. (A:real^N^N)$i$j * b i * a j)) =
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * a i * b j))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The divergence-form integral split into its (i,j) terms, the second       *)
(* derivative replaced by its bounded representative p2bw_trd.               *)

let P2BW_BIL_SPLIT = prove
 (`!(u:real^(N,1)finite_sum->real) w L (W:real^(N,1)finite_sum->real^N^N) BW k.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y)) /\
     (!x y. abs(w x - w y) <= L * norm(x - y)) /\
     compact k /\ (!x i j. ~(x IN k) ==> W x$i$j = &0) /\
     (!i j. (\x. lift(W x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!x i j. abs(W x$i$j) <= BW)
     ==> (\x. lift(p2bw_bil W u w x)) integrable_on (:real^(N,1)finite_sum) /\
         integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W u w x)) =
         vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. integral (:real^(N,1)finite_sum)
                         (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x)
                                          (pastecart (basis i) (vec 0))) *
                                   (W x$i$j * p2bw_trd w (pastecart (basis j) (vec 0)) x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. (\x. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x)
                         (pastecart (basis i) (vec 0))) *
                    ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                     p2bw_trd (w:real^(N,1)finite_sum->real) (pastecart (basis j) (vec 0)) x)))
          integrable_on (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BW_LDTB_INT THEN
    MP_TAC(ISPECL [`w:real^(N,1)finite_sum->real`; `L:real`;
                   `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_TRD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real`; `BW * L * norm(pastecart (basis j:real^N) (vec 0:real^1))`;
                          `k:real^(N,1)finite_sum->bool`] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^(N,1)finite_sum->real`; `L:real`;
                 `vec 0:real^(N,1)finite_sum`] P2BW_TRD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!x. (\y. lift((w:real^(N,1)finite_sum->real) y)) differentiable at x
        ==> lift(p2bw_bil (W:real^(N,1)finite_sum->real^N^N) u w x) =
            vsum(1..dimindex(:N))
              (\i. vsum(1..dimindex(:N))
                     (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y))
                                      (at x) (pastecart (basis i) (vec 0))) *
                               (W x$i$j * p2bw_trd w (pastecart (basis j) (vec 0)) x))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[p2bw_bil; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[p2bw_trd; wan_xder] THEN
    REWRITE_TAC[REAL_ARITH `!a b c:real. a * b * c = b * (a * c)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y))
                                   (at x) (pastecart (basis i) (vec 0))) *
                            ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                             p2bw_trd (w:real^(N,1)finite_sum->real) (pastecart (basis j) (vec 0)) x)))))
    integrable_on (:real^(N,1)finite_sum) /\
    integral (:real^(N,1)finite_sum)
     (\x. vsum(1..dimindex(:N))
           (\i. vsum(1..dimindex(:N))
                  (\j. lift(drop(frechet_derivative (\y. lift(u y)) (at x)
                                   (pastecart (basis i) (vec 0))) *
                            (W x$i$j * p2bw_trd w (pastecart (basis j) (vec 0)) x))))) =
    vsum(1..dimindex(:N))
     (\i. vsum(1..dimindex(:N))
            (\j. integral (:real^(N,1)finite_sum)
                   (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x)
                                    (pastecart (basis i) (vec 0))) *
                             (W x$i$j * p2bw_trd w (pastecart (basis j) (vec 0)) x)))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      MP_TAC(ISPECL
        [`\i x. vsum(1..dimindex(:N))
                  (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x) (pastecart (basis i) (vec 0))) *
                            ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                             p2bw_trd (w:real^(N,1)finite_sum->real) (pastecart (basis j) (vec 0)) x)))`;
         `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL
        [`\j x. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x) (pastecart (basis i) (vec 0))) *
                     ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                      p2bw_trd (w:real^(N,1)finite_sum->real) (pastecart (basis j) (vec 0)) x))`;
         `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN (:real^(N,1)finite_sum) DIFF
             {x | ~((\y. lift((w:real^(N,1)finite_sum->real) y)) differentiable at x)}
        ==> vsum(1..dimindex(:N))
              (\i. vsum(1..dimindex(:N))
                     (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x) (pastecart (basis i) (vec 0))) *
                               ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                                p2bw_trd w (pastecart (basis j) (vec 0)) x)))) =
            lift(p2bw_bil W u w x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\x. vsum(1..dimindex(:N))
                     (\i. vsum(1..dimindex(:N))
                            (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x) (pastecart (basis i) (vec 0))) *
                                      ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                                       p2bw_trd (w:real^(N,1)finite_sum->real)
                                                (pastecart (basis j) (vec 0)) x))))` THEN
    EXISTS_TAC `{x | ~((\y. lift((w:real^(N,1)finite_sum->real) y)) differentiable at x)}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral (:real^(N,1)finite_sum)
                  (\x. vsum(1..dimindex(:N))
                     (\i. vsum(1..dimindex(:N))
                            (\j. lift(drop(frechet_derivative (\y. lift((u:real^(N,1)finite_sum->real) y)) (at x) (pastecart (basis i) (vec 0))) *
                                      ((W:real^(N,1)finite_sum->real^N^N) x$i$j *
                                       p2bw_trd (w:real^(N,1)finite_sum->real)
                                                (pastecart (basis j) (vec 0)) x)))))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | ~((\y. lift((w:real^(N,1)finite_sum->real) y)) differentiable at x)}` THEN
    ASM_REWRITE_TAC[]]);;

let P2BW_BIL_CONV = prove
 (`!(u:num->real^(N,1)finite_sum->real) u0 w L (W:num->real^(N,1)finite_sum->real^N^N) W0
    BW k kk d.
     &0 <= L /\ (!m x y. abs(u m x - u m y) <= L * norm(x - y)) /\
     (!x y. abs(u0 x - u0 y) <= L * norm(x - y)) /\
     (!x y. abs(w x - w y) <= L * norm(x - y)) /\
     compact k /\ &0 < d /\ {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET kk /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN kk ==> abs(u m x - u0 x) < e) /\
     (!m x i j. ~(x IN k) ==> W m x$i$j = &0) /\ (!x i j. ~(x IN k) ==> W0 x$i$j = &0) /\
     (!m i j. (\x. lift(W m x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!i j. (\x. lift(W0 x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!m x i j. abs(W m x$i$j) <= BW) /\ (!x i j. abs(W0 x$i$j) <= BW) /\
     (!e. &0 < e ==> ?N. !m x i j. N <= m ==> abs(W m x$i$j - W0 x$i$j) < e)
     ==> ((\m. integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil (W m) (u m) w x))) -->
          integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 u0 w x))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                                               ((u:num->real^(N,1)finite_sum->real) m) w x)) =
        vsum(1..dimindex(:N))
          (\i. vsum(1..dimindex(:N))
                 (\j. integral (:real^(N,1)finite_sum)
                        (\x. lift(drop(frechet_derivative (\y. lift(u m y)) (at x)
                                         (pastecart (basis i) (vec 0))) *
                                  (W m x$i$j * p2bw_trd w (pastecart (basis j) (vec 0)) x)))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(u:num->real^(N,1)finite_sum->real) m`; `w:real^(N,1)finite_sum->real`;
                   `L:real`; `(W:num->real^(N,1)finite_sum->real^N^N) m`; `BW:real`;
                   `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SPLIT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u0:real^(N,1)finite_sum->real`; `w:real^(N,1)finite_sum->real`;
                 `L:real`; `W0:real^(N,1)finite_sum->real^N^N`; `BW:real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SPLIT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^(N,1)finite_sum->real`; `L:real`;
                 `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_TRD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real^(N,1)finite_sum->real`; `u0:real^(N,1)finite_sum->real`; `L:real`;
                 `\m x. ((W:num->real^(N,1)finite_sum->real^N^N) m x)$i$j`;
                 `\x. ((W0:real^(N,1)finite_sum->real^N^N) x)$i$j`;
                 `p2bw_trd (w:real^(N,1)finite_sum->real) (pastecart (basis j) (vec 0))`;
                 `L * norm(pastecart (basis j:real^N) (vec 0:real^1))`; `BW:real`;
                 `k:real^(N,1)finite_sum->bool`; `kk:real^(N,1)finite_sum->bool`; `d:real`;
                 `pastecart (basis i:real^N) (vec 0:real^1)`] P2BW_WEAK_PRODUCT_CONV) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `(W0:real^(N,1)finite_sum->real^N^N)`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th) &&
    not (can (find_term (fun t -> t = `(u0:real^(N,1)finite_sum->real)`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P2BW_ENERGY_GLOBAL = prove
 (`!(lg:num->real^(N,1)finite_sum->real) lg0 L (W:num->real^(N,1)finite_sum->real^N^N) W0
    BW k kk d.
     &0 <= L /\ (!m x y. abs(lg m x - lg m y) <= L * norm(x - y)) /\
     (!x y. abs(lg0 x - lg0 y) <= L * norm(x - y)) /\
     compact k /\ &0 < d /\ {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET kk /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN kk ==> abs(lg m x - lg0 x) < e) /\
     (!m x i j. ~(x IN k) ==> W m x$i$j = &0) /\ (!x i j. ~(x IN k) ==> W0 x$i$j = &0) /\
     (!m i j. (\x. lift(W m x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!i j. (\x. lift(W0 x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!m x i j. abs(W m x$i$j) <= BW) /\ (!x i j. abs(W0 x$i$j) <= BW) /\
     (!e. &0 < e ==> ?N. !m x i j. N <= m ==> abs(W m x$i$j - W0 x$i$j) < e) /\
     (!m x. transp(W m x) = W m x /\ (!v. &0 <= v dot (W m x ** v))) /\
     (!e. &0 < e
          ==> ?M. !m. M <= m
                      ==> drop(integral (:real^(N,1)finite_sum)
                                 (\x. lift(p2bw_bil (W m) (lg m) (lg m) x))) <=
                          drop(integral (:real^(N,1)finite_sum)
                                 (\x. lift(p2bw_bil (W m) (lg m) lg0 x))) + e)
     ==> ((\m. integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil (W m) (lg m) (lg m) x))) -->
          integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 lg0 lg0 x))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                               ((lg:num->real^(N,1)finite_sum->real) m) lg0 x))) -->
     integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 lg0 lg0 x))) sequentially /\
    ((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m) lg0 lg0 x))) -->
     integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 lg0 lg0 x))) sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BW_BIL_CONV THEN
    MAP_EVERY EXISTS_TAC [`L:real`; `BW:real`; `k:real^(N,1)finite_sum->bool`;
                          `kk:real^(N,1)finite_sum->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. &2 * drop(integral (:real^(N,1)finite_sum)
                   (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                                      ((lg:num->real^(N,1)finite_sum->real) m) lg0 x))) -
        drop(integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil (W m) lg0 lg0 x))) <=
        drop(integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil (W m) (lg m) (lg m) x)))`
  (LABEL_TAC "low") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `!u w. (!x y. abs(u x - u y) <= L * norm(x - y)) /\ (!x y. abs(w x - w y) <= L * norm(x - y))
            ==> (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                                   (u:real^(N,1)finite_sum->real) w x))
                integrable_on (:real^(N,1)finite_sum)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`u:real^(N,1)finite_sum->real`; `w:real^(N,1)finite_sum->real`; `L:real`;
                     `(W:num->real^(N,1)finite_sum->real^N^N) m`; `BW:real`;
                     `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SPLIT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^(N,1)finite_sum)
                  (\x. &2 % lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                                          ((lg:num->real^(N,1)finite_sum->real) m) lg0 x) -
                       lift(p2bw_bil (W m) lg0 lg0 x)))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_SUB; DROP_CMUL;
                   REAL_LE_REFL];
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CMUL] THEN
      X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_SUB; DROP_CMUL; LIFT_DROP; p2bw_bil] THEN
      MATCH_MP_TAC P2BW_QUAD_PSD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m)
                               ((lg:num->real^(N,1)finite_sum->real) m) lg0 x))) -->
     integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 lg0 lg0 x))) sequentially` THEN
  UNDISCH_TAC
   `((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil ((W:num->real^(N,1)finite_sum->real^N^N) m) lg0 lg0 x))) -->
     integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil W0 lg0 lg0 x))) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_bil")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th) &&
    not (can (find_term (fun t -> t = `W0:real^(N,1)finite_sum->real^N^N`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `M3:num`)] THEN
  EXISTS_TAC `M1 + M2 + M3:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `M1 <= m /\ M2 <= m /\ M3 <= m:num` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `M3 <= m:num`) o SPEC `m:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `M3:num`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `M2 <= m:num`) o SPEC `m:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `M2:num`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `M1 <= m:num`) o SPEC `m:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `M1:num`)) (concl th))) THEN
  USE_THEN "low" (MP_TAC o SPEC `m:num`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Weak inequalities of divergence form for Lipschitz tests                 *)
(* (P2BW_BILFORM_LIP, from P2BW_LTEST_EXT), product and difference rules    *)
(* for derivatives at differentiability points, products of locally         *)
(* Lipschitz functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let P2BW_BIL_PAIR = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u (phi:real^(N,1)finite_sum->real) c z.
     c * p2bw_bil A u phi z =
     sum(1..dimindex(:N))
       (\j. drop(frechet_derivative (\y. lift(phi y)) (at z) (pastecart (basis j) (vec 0))) *
            (c * sum(1..dimindex(:N)) (\i. A z$i$j * wan_xder i u z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_bil] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[wan_xder] THEN
  REWRITE_TAC[REAL_ARITH `!a b c d:real. c * a * b * d = d * c * a * b`]);;

let P2BW_BILFORM_LIP = prove
 (`!(om:real^(N,1)finite_sum->bool) fz c (A:real^(N,1)finite_sum->real^N^N) l.
     open om /\ p2bw_lebm om fz /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     wan_loclip om l /\
     (!phi. wan_test om phi /\ (!z. &0 <= phi z)
            ==> drop(integral om (\z. lift(phi z * fz z + c * p2bw_bil A l phi z))) <= &0)
     ==> !psi. p2bw_ltest om psi
               ==> drop(integral om (\z. lift(psi z * fz z + c * p2bw_bil A l psi z))) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_ltest] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2BW_BIL_PAIR]) THEN REWRITE_TAC[P2BW_BIL_PAIR] THEN
  MATCH_MP_TAC P2BW_LTEST_EXT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC P2BW_LEBM_CMUL THEN
  MATCH_MP_TAC P2BW_LEBM_SUM THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[]]);;

let P2BW_DER_MUL = prove
 (`!(f:real^M->real) g x v.
     (\y. lift(f y)) differentiable at x /\ (\y. lift(g y)) differentiable at x
     ==> (\y. lift(f y * g y)) differentiable at x /\
         drop(frechet_derivative (\y. lift(f y * g y)) (at x) v) =
         f x * drop(frechet_derivative (\y. lift(g y)) (at x) v) +
         g x * drop(frechet_derivative (\y. lift(f y)) (at x) v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real`;
                 `\h. drop(frechet_derivative (\y. lift((f:real^M->real) y)) (at x) h)`;
                 `\y. lift((g:real^M->real) y)`;
                 `frechet_derivative (\y. lift((g:real^M->real) y)) (at x)`; `x:real^M`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let P2BW_DER_DIFF_CONST = prove
 (`!(f:real^M->real) g c x v.
     (\y. lift(f y)) differentiable at x /\ (\y. lift(g y)) differentiable at x
     ==> (\y. lift(f y - g y + c)) differentiable at x /\
         drop(frechet_derivative (\y. lift(f y - g y + c)) (at x) v) =
         drop(frechet_derivative (\y. lift(f y)) (at x) v) -
         drop(frechet_derivative (\y. lift(g y)) (at x) v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift((f:real^M->real) y - g y + c)) has_derivative
     (\h. frechet_derivative (\y. lift(f y)) (at x) h -
          frechet_derivative (\y. lift((g:real^M->real) y)) (at x) h + vec 0)) (at x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC]);;

let P2BW_LOCLIP_MUL = prove
 (`!(om:real^M->bool) f g.
     open om /\ wan_loclip om f /\ wan_loclip om g ==> wan_loclip om (\x. f x * g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_loclip] THEN X_GEN_TAC `k:real^M->bool` THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `k:real^M->bool` (REWRITE_RULE[wan_loclip]
    (ASSUME `wan_loclip om (g:real^M->real)`))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Lg:real`) THEN
  MP_TAC(SPEC `k:real^M->bool` (REWRITE_RULE[wan_loclip]
    (ASSUME `wan_loclip om (f:real^M->real)`))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Lf:real`) THEN
  SUBGOAL_THEN `?Bf Bg. (!x. x IN k ==> abs((f:real^M->real) x) <= Bf) /\
                        (!x. x IN k ==> abs((g:real^M->real) x) <= Bg)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift((f:real^M->real) x)) continuous_on k /\
                  (\x. lift((g:real^M->real) x)) continuous_on k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `om:real^M->bool` THEN
      ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. lift((f:real^M->real) x)`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `b1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\x. lift((g:real^M->real) x)`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `b2:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b1:real`; `b2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `abs Bf * abs Lg + abs Bg * abs Lf` THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `abs((f:real^M->real) x) <= abs Bf /\ abs((g:real^M->real) y) <= abs Bg /\
    abs(g x - g y) <= abs Lg * norm(x - y:real^M) /\
    abs(f x - f y) <= abs Lf * norm(x - y:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lg * norm(x - y:real^M)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lf * norm(x - y:real^M)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((f:real^M->real) x) * abs((g:real^M->real) x - g y) + abs(g y) * abs(f x - f y)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Claim 9.22 for one index (P2BW_CLAIM922_STEP): T2 tested with the        *)
(* Lipschitz test psi = phi (l0 - l + ep), and its supporting facts (the    *)
(* vanishing bound sequence P2BW_SUP_SEQ, a.e. differentiability on        *)
(* compacts, local boundedness of bilinear forms, integrability).           *)
(* ------------------------------------------------------------------------- *)

let P2BW_SUP_SEQ = prove
 (`!(u:num->real^M->real) u0 k.
     compact k /\ (!m. (\x. lift(u m x)) continuous_on k) /\ (\x. lift(u0 x)) continuous_on k /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN k ==> abs(u m x - u0 x) < e)
     ==> ?ep. (!m. &0 < ep m) /\ (!m x. x IN k ==> abs(u m x - u0 x) <= ep m) /\
              (!e. &0 < e ==> ?N. !m. N <= m ==> ep m < e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))) THEN
  SUBGOAL_THEN `!m. ?b. !x. x IN k ==> abs((u:num->real^M->real) m x - u0 x) <= b`
  (LABEL_TAC "bd") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\x. lift((u:num->real^M->real) m x - u0 x)`; `k:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (!x. x IN k
             ==> abs((u:num->real^M->real) m x - u0 x) <=
                 sup(&0 INSERT IMAGE (\x. abs(u m x - u0 x)) k)) /\
        &0 <= sup(&0 INSERT IMAGE (\x. abs(u m x - u0 x)) k) /\
        (!c. &0 <= c /\ (!x. x IN k ==> abs(u m x - u0 x) <= c)
             ==> sup(&0 INSERT IMAGE (\x. abs(u m x - u0 x)) k) <= c)`
  (LABEL_TAC "sup") THENL
   [GEN_TAC THEN USE_THEN "bd" (X_CHOOSE_TAC `b:real` o SPEC `m:num`) THEN
    MP_TAC(ISPEC `&0 INSERT IMAGE (\x. abs((u:num->real^M->real) m x - u0 x)) k` SUP) THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [EXISTS_TAC `abs b` THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b`];
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\m. sup(&0 INSERT IMAGE (\x. abs((u:num->real^M->real) m x - u0 x)) k) +
                  inv(&m + &1)` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &m + &1`];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= a /\ &0 < b ==> x <= a + b`) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &m + &1`];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= e / &2 /\ b < e / &2 ==> a + b < e`) THEN CONJ_TAC THENL
     [USE_THEN "sup" (MATCH_MP_TAC o last o CONJUNCTS o SPEC `m:num`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]]);;

let P2BW_LOCLIP_AE_ON = prove
 (`!(om:real^M->bool) u k.
     open om /\ wan_loclip om u /\ compact k /\ k SUBSET om
     ==> negligible {z | z IN k /\ ~((\y. lift(u y)) differentiable at z)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `u:real^M->real`; `k:real^M->bool`] P2BW_LOCLIP_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^M->bool` (X_CHOOSE_THEN `kk:real^M->bool`
    (X_CHOOSE_THEN `ug:real^M->real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`ug:real^M->real`; `L:real`; `vec 0:real^M`] P2BW_TRD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | ~((\y. lift((ug:real^M->real) y)) differentiable at x)}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^M` THEN
  REWRITE_TAC[TAUT `(a /\ ~b) ==> ~c <=> a /\ c ==> b`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^M) IN uu` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `open(uu:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\y. lift((ug:real^M->real) y)`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^M) IN kk` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^M`) THEN ASM_MESON_TAC[DIST_SYM; SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* The test function psi = phi (l0 - l + ep) of Claim 9.22. *)

let P2BW_PSI_FACTS = prove
 (`!(om:real^M->bool) phi l l0 ep k.
     open om /\ wan_test om phi /\ (!x. &0 <= phi x) /\ compact k /\ k SUBSET om /\
     (!x. ~(x IN k) ==> phi x = &0) /\ wan_loclip om l /\ wan_loclip om l0 /\
     (!x. x IN k ==> abs(l x - l0 x) <= ep)
     ==> wan_loclip om (\x. phi x * (l0 x - l x + ep)) /\
         (!x. &0 <= phi x * (l0 x - l x + ep)) /\
         (!x. ~(x IN k) ==> phi x * (l0 x - l x + ep) = &0) /\
         (!z v. (\y. lift(l y)) differentiable at z /\ (\y. lift(l0 y)) differentiable at z
                ==> drop(frechet_derivative (\y. lift(phi y * (l0 y - l y + ep))) (at z) v) =
                    phi z * (drop(frechet_derivative (\y. lift(l0 y)) (at z) v) -
                             drop(frechet_derivative (\y. lift(l y)) (at z) v)) +
                    (l0 z - l z + ep) * drop(frechet_derivative (\y. lift(phi y)) (at z) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. (\y. lift((phi:real^M->real) y)) differentiable at z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^M)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    ASM_MESON_TAC[wan_test];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
      REWRITE_TAC[wan_loclip] THEN MESON_TAC[];
      UNDISCH_TAC `wan_loclip om (l:real^M->real)` THEN
      UNDISCH_TAC `wan_loclip om (l0:real^M->real)` THEN REWRITE_TAC[wan_loclip] THEN
      REPEAT DISCH_TAC THEN X_GEN_TAC `kk:real^M->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `kk:real^M->bool`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `kk:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN DISCH_THEN(X_CHOOSE_TAC `L2:real`) THEN
      EXISTS_TAC `L1 + L2:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b c d e x y.
         abs(a - b) <= x /\ abs(c - d) <= y ==> abs((a - c + e) - (b - d + e)) <= x + y`) THEN
      ASM_SIMP_TAC[]];
    GEN_TAC THEN ASM_CASES_TAC `(x:real^M) IN k` THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `ep:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LE_REFL]];
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^M->real`; `\y. (l0:real^M->real) y - l y + ep`; `z:real^M`;
                   `v:real^M`] P2BW_DER_MUL) THEN
    MP_TAC(ISPECL [`l0:real^M->real`; `l:real^M->real`; `ep:real`; `z:real^M`; `v:real^M`]
                  P2BW_DER_DIFF_CONST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BW_LEBM_BIL = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) u w.
     open om /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     wan_loclip om u /\ wan_loclip om w
     ==> p2bw_lebm om (p2bw_bil A u w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) u w =
                (\z. sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                       (\j. A z$i$j * wan_xder i u z * wan_xder j w z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bw_bil]; ALL_TAC] THEN
  MATCH_MP_TAC P2BW_LEBM_SUM THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BW_LEBM_SUM THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BW_LEBM_MUL THEN REWRITE_TAC[wan_xder] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[]);;

let P2BW_LEBM_NEG = prove
 (`!(om:real^M->bool) f. p2bw_lebm om f ==> p2bw_lebm om (\x. --(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. --((f:real^M->real) x)) = (\x. --(&1) * f x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BW_LEBM_CMUL THEN ASM_REWRITE_TAC[]);;

let P2BW_CONT_TAU_INV = prove
 (`!(om:real^(N,1)finite_sum->bool).
     (!z. z IN om ==> &0 < drop(sndcart z))
     ==> (\z. lift(inv(drop(sndcart z)))) continuous_on om`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(N,1)finite_sum. drop(sndcart z)`; `om:real^(N,1)finite_sum->bool`]
                CONTINUOUS_ON_INV) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX; LINEAR_SNDCART];
    ASM_MESON_TAC[REAL_LT_IMP_NZ]]);;

let P2BW_CONT_T2COEFF = prove
 (`!(om:real^(N,1)finite_sum->bool) rho R l c.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l
     ==> (\z. lift((R z + (l z - c) / drop(sndcart z)) * rho z)) continuous_on om`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((l:real^(N,1)finite_sum->real) z)) continuous_on om` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPEC `om:real^(N,1)finite_sum->bool` P2BW_CONT_TAU_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; LIFT_CMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]);;

(* The T2 integrand of a nonnegative Lipschitz test in the form of           *)
(* P2BW_BILFORM_LIP.                                                          *)

let P2BW_T2_LIP = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ p2bw_t2 om A rho R l
     ==> !psi. p2bw_ltest om psi
               ==> drop(integral om
                     (\z. lift(psi z * (--(p2bw_bil A l l z) +
                                        (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z) +
                               --(&2) * p2bw_bil A l psi z))) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BW_BILFORM_LIP THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
      MATCH_MP_TAC P2BW_CONT_T2COEFF THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2bw_t2 om (A:real^(N,1)finite_sum->real^N^N) rho R l` THEN
    REWRITE_TAC[p2bw_t2] THEN DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let P2BW_LEBM_TEST_INT = prove
 (`!(om:real^M->bool) phi h v.
     open om /\ wan_test om phi /\ p2bw_lebm om h
     ==> (\z. lift(phi z * h z)) integrable_on om /\
         (\z. lift(drop(frechet_derivative (\y. lift(phi y)) (at z) v) * h z)) integrable_on om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_TEST_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[wan_test]; DISCH_THEN(X_CHOOSE_TAC `B:real`)] THEN
  SUBGOAL_THEN `!x y. abs((phi:real^M->real) x - phi y) <= abs B * norm(x - y)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(x - y:real^M)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `h:real^M->real`; `k:real^M->bool`] P2BW_LEBM_L1BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^M->real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LIP_SUPPORT_ABSINT THEN
      MAP_EVERY EXISTS_TAC [`abs B`; `k:real^M->bool`] THEN ASM_REWRITE_TAC[];
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
    FIRST_X_ASSUM(MP_TAC o SPEC `\x. drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v)`) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [MATCH_MP_TAC P2BW_LIP_DER_ABSINT THEN EXISTS_TAC `abs B` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]]);;

let P2BW_LEBM_LTEST_INT = prove
 (`!(om:real^(N,1)finite_sum->bool) psi h.
     open om /\ p2bw_ltest om psi /\ p2bw_lebm om h
     ==> (\z. lift(psi z * h z)) integrable_on om`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_ltest] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_LOCLIP_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `h:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`] P2BW_LEBM_L1BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPEC `psi:real^(N,1)finite_sum->real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LIP_SUPPORT_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `k:real^(N,1)finite_sum->bool`] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]);;

let P2BW_BIL_PSI_ID = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) l l0 phi ep z.
     (!j. wan_xder j (\y. phi y * (l0 y - l y + ep)) z =
          phi z * (wan_xder j l0 z - wan_xder j l z) + (l0 z - l z + ep) * wan_xder j phi z)
     ==> p2bw_bil A l (\y. phi y * (l0 y - l y + ep)) z =
         phi z * p2bw_bil A l l0 z - phi z * p2bw_bil A l l z +
         (l0 z - l z + ep) * p2bw_bil A l phi z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_bil] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2BW_CLAIM922_STEP = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l l0 phi ep k.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_loclip om l0 /\ p2bw_t2 om A rho R l /\
     wan_test om phi /\ (!z. &0 <= phi z) /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> phi z = &0) /\ (!z. z IN k ==> abs(l z - l0 z) <= ep)
     ==> drop(integral om (\z. lift(phi z * p2bw_bil A l l z))) <=
         drop(integral om (\z. lift(phi z * p2bw_bil A l l0 z))) +
         drop(integral om (\z. lift((l0 z - l z + ep) * p2bw_bil A l phi z))) -
         drop(integral om (\z. lift((phi z * (l0 z - l z + ep)) *
                                    (--(p2bw_bil A l l z) +
                                     (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) *
                                     rho z)))) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `l:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`; `ep:real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_PSI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Fz = \z. --(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) +
                       ((R:real^(N,1)finite_sum->real) z +
                        (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z` THEN
  SUBGOAL_THEN `p2bw_lebm om (Fz:real^(N,1)finite_sum->real)` ASSUME_TAC THENL
   [EXPAND_TAC "Fz" THEN MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
      MATCH_MP_TAC P2BW_CONT_T2COEFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_ltest om (\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_ltest] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                 `rho:real^(N,1)finite_sum->real`; `R:real^(N,1)finite_sum->real`;
                 `l:real^(N,1)finite_sum->real`] P2BW_T2_LIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)`) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_TAC THEN
  ABBREV_TAC `S = {z | z IN k /\ ~((\y. lift((l:real^(N,1)finite_sum->real) y)) differentiable at z)} UNION
                  {z | z IN k /\ ~((\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at z)}` THEN
  SUBGOAL_THEN `negligible (S:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z IN S)
        ==> p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l (\y. (phi:real^(N,1)finite_sum->real) y * ((l0:real^(N,1)finite_sum->real) y - l y + ep)) z =
            phi z * p2bw_bil A l l0 z - phi z * p2bw_bil A l l z +
            (l0 z - l z + ep) * p2bw_bil A l phi z`
  (LABEL_TAC "id") THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BW_BIL_PSI_ID THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[wan_xder] THEN
    ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN k` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "frechet_derivative")) (concl th) &&
        can (find_term (fun t -> t = `ep:real`)) (concl th))) THEN
      UNDISCH_TAC `~((z:real^(N,1)finite_sum) IN S)` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `!f:real^(N,1)finite_sum->real.
          (!x. ~(x IN k) ==> f x = &0)
          ==> drop(frechet_derivative (\y. lift(f y)) (at z) (pastecart (basis j) (vec 0))) = &0`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`\y. lift((f:real^(N,1)finite_sum->real) y)`; `k:real^(N,1)finite_sum->bool`;
                       `z:real^(N,1)finite_sum`] WAN_FRECHET_ZERO_OUTSIDE) THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; LIFT_NUM; DROP_VEC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(((phi:real^(N,1)finite_sum->real) z * ((l0:real^(N,1)finite_sum->real) z - l z + ep)) * (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) + ((R:real^(N,1)finite_sum->real) z + ((l:real^(N,1)finite_sum->real) z - &(dimindex(:N))) / drop(sndcart z)) * (rho:real^(N,1)finite_sum->real) z))) integrable_on om /\
    (\z. lift(phi z * p2bw_bil A l l0 z)) integrable_on om /\
    (\z. lift(phi z * p2bw_bil A l l z)) integrable_on om /\
    (\z. lift(((l0:real^(N,1)finite_sum->real) z - l z + ep) * p2bw_bil A l phi z)) integrable_on om`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\z. (phi:real^(N,1)finite_sum->real) z * ((l0:real^(N,1)finite_sum->real) z - l z + ep)`;
                     `Fz:real^(N,1)finite_sum->real`] P2BW_LEBM_LTEST_INT) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fz" THEN SIMP_TAC[];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l0`; `vec 0:real^(N,1)finite_sum`]
                    P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
                      SIMP_TAC[]];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l`; `vec 0:real^(N,1)finite_sum`]
                    P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
                      SIMP_TAC[]];
      ONCE_REWRITE_TAC[P2BW_BIL_PAIR] THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
      MATCH_MP_TAC INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `\z. ((l0:real^(N,1)finite_sum->real) z - l z + ep) * sum(1..dimindex(:N))
                            (\i. (A:real^(N,1)finite_sum->real^N^N) z$i$j * wan_xder i l z)`;
                     `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LEBM_CONT THEN
        REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN
        REPEAT((MATCH_MP_TAC CONTINUOUS_ON_ADD ORELSE MATCH_MP_TAC CONTINUOUS_ON_SUB) THEN
               CONJ_TAC) THEN
        ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC P2BW_LEBM_SUM THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\z. lift(((phi:real^(N,1)finite_sum->real) z * ((l0:real^(N,1)finite_sum->real) z - l z + ep)) * (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) + ((R:real^(N,1)finite_sum->real) z + ((l:real^(N,1)finite_sum->real) z - &(dimindex(:N))) / drop(sndcart z)) * (rho:real^(N,1)finite_sum->real) z) +
                         --(&2) * p2bw_bil A l (\y. (phi:real^(N,1)finite_sum->real) y * ((l0:real^(N,1)finite_sum->real) y - l y + ep)) z)) =
    integral om (\z. lift((phi z * ((l0:real^(N,1)finite_sum->real) z - l z + ep)) * (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) + ((R:real^(N,1)finite_sum->real) z + ((l:real^(N,1)finite_sum->real) z - &(dimindex(:N))) / drop(sndcart z)) * (rho:real^(N,1)finite_sum->real) z))) -
    &2 % integral om (\z. lift(phi z * p2bw_bil A l l0 z)) +
    &2 % integral om (\z. lift(phi z * p2bw_bil A l l z)) -
    &2 % integral om (\z. lift(((l0:real^(N,1)finite_sum->real) z - l z + ep) * p2bw_bil A l phi z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral om (\z. lift(((phi:real^(N,1)finite_sum->real) z * ((l0:real^(N,1)finite_sum->real) z - l z + ep)) * (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) + ((R:real^(N,1)finite_sum->real) z + ((l:real^(N,1)finite_sum->real) z - &(dimindex(:N))) / drop(sndcart z)) * (rho:real^(N,1)finite_sum->real) z)) -
                       &2 % lift(phi z * p2bw_bil A l l0 z) +
                       &2 % lift(phi z * p2bw_bil A l l z) -
                       &2 % lift(((l0:real^(N,1)finite_sum->real) z - l z + ep) * p2bw_bil A l phi z))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `S:real^(N,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      USE_THEN "id" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((z:real^(N,1)finite_sum) IN S)`)]) THEN
      REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; GSYM LIFT_SUB] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_SUB; INTEGRAL_CMUL; INTEGRABLE_ADD; INTEGRABLE_SUB;
                   INTEGRABLE_CMUL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_binary "real_le" (concl th) &&
    can (find_term (fun t -> t = `--(&2)`)) (concl th))) THEN
  ASM_REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Lemma 9.21 (P2BW_ENERGY_LOCAL): localization tools (cut-off          *)
(* weights, local-to-global integrals, uniform bounds), Claim 9.22 in       *)
(* global form for one index (P2BW_CLAIM922_GLOBAL) and as a sequence       *)
(* (P2BW_CLAIM922_SEQ), and the energy convergence on om.                   *)
(* ------------------------------------------------------------------------- *)

(* s1: tools for the local energy convergence (MT Lemma 9.21). *)

let P2BW_INDEX_INRANGE = prove
 (`!i j. ?i' j'. 1 <= i' /\ i' <= dimindex(:N) /\ 1 <= j' /\ j' <= dimindex(:N) /\
                 !M:real^N^N. M$i$j = M$i'$j'`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC
    (SPEC `i:num` (INST_TYPE [`:real^N`,`:A`] FINITE_INDEX_INRANGE)) THEN
  X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC
    (SPEC `j:num` (INST_TYPE [`:real`,`:A`] FINITE_INDEX_INRANGE)) THEN
  MAP_EVERY EXISTS_TAC [`i':num`; `j':num`] THEN ASM_REWRITE_TAC[]);;

let P2BW_IJ_TAC =
  MP_TAC(SPECL [`i:num`; `j:num`] P2BW_INDEX_INRANGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` (X_CHOOSE_THEN `j':num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (fun th -> REWRITE_TAC[th])))))));;

let P2BW_UNIF_BOUNDED = prove
 (`!(u:num->real^M->real) u0 k.
     compact k /\ (!m. (\x. lift(u m x)) continuous_on k) /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN k ==> abs(u m x - u0 x) < e)
     ==> ?B. &0 <= B /\ (!m x. x IN k ==> abs(u m x) <= B) /\
             (!x. x IN k ==> abs(u0 x) <= B)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N0"))) THEN
  SUBGOAL_THEN `!m. ?b. !x. x IN k ==> abs((u:num->real^M->real) m x) <= b` MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\x. lift((u:num->real^M->real) m x)`; `k:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `b:num->real` (LABEL_TAC "B"))] THEN
  USE_THEN "N0" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MP_TAC(ISPECL [`b:num->real`; `0..N`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (LABEL_TAC "A")) THEN
  SUBGOAL_THEN `!x. x IN k ==> abs((u0:real^M->real) x) <= abs a + &1` (LABEL_TAC "U0") THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPECL [`N:num`; `x:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; DISCH_TAC] THEN
    USE_THEN "B" (MP_TAC o SPECL [`N:num`; `x:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "A" (MP_TAC o SPEC `N:num`) THEN
    ANTS_TAC THENL [REWRITE_TAC[LE_REFL]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `abs a + &2` THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`m:num`; `x:real^M`] THEN DISCH_TAC THEN
    DISJ_CASES_TAC(ARITH_RULE `m <= N \/ N <= m:num`) THENL
     [USE_THEN "B" (MP_TAC o SPECL [`m:num`; `x:real^M`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "A" (MP_TAC o SPEC `m:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "N" (MP_TAC o SPECL [`m:num`; `x:real^M`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "U0" (MP_TAC o SPEC `x:real^M`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "U0" (fun th -> MESON_TAC[th; REAL_ARITH `x <= a + &1 ==> x <= a + &2`])]);;

let P2BW_UNIF_BOUNDED_M = prove
 (`!(A:num->real^M->real^N^N) (A0:real^M->real^N^N) k.
     compact k /\
     (!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (\x. lift(A m x$i$j)) continuous_on k) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> !e. &0 < e ==> ?N. !m x. N <= m /\ x IN k ==> abs(A m x$i$j - A0 x$i$j) < e)
     ==> ?B. &0 <= B /\ (!m x i j. x IN k ==> abs(A m x$i$j) <= B) /\
             (!x i j. x IN k ==> abs(A0 x$i$j) <= B)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?b. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> &0 <= b /\ (!m x. x IN k ==> abs((A:num->real^M->real^N^N) m x$i$j) <= b) /\
                  (!x. x IN k ==> abs((A0:real^M->real^N^N) x$i$j) <= b)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\m x. (A:num->real^M->real^N^N) m x$i$j`; `\x. (A0:real^M->real^N^N) x$i$j`;
                   `k:real^M->bool`] P2BW_UNIF_BOUNDED) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `b:num->num->real` (LABEL_TAC "B"))] THEN
  MP_TAC(ISPECL [`\p:num#num. (b:num->num->real) (FST p) (SND p)`;
                 `(1..dimindex(:N)) CROSS (1..dimindex(:N))`] UPPER_BOUND_FINITE_SET_REAL) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (LABEL_TAC "A")) THEN
  EXISTS_TAC `abs a` THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THEN (REPEAT GEN_TAC THEN
  P2BW_IJ_TAC THEN DISCH_TAC THEN
  USE_THEN "B" (MP_TAC o SPECL [`i':num`; `j':num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "A" (MP_TAC o SPECL [`i':num`; `j':num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x b a. x <= b /\ b <= a ==> x <= abs a`) THEN
  EXISTS_TAC `(b:num->num->real) i' j'` THEN ASM_SIMP_TAC[]));;

let P2BW_CUT_MEAS = prove
 (`!(f:real^M->real) k.
     compact k /\ (\x. lift(f x)) continuous_on k
     ==> (\x. lift(if x IN k then f x else &0)) measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COND_RAND; LIFT_NUM; MEASURABLE_ON_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED]);;

let P2BW_CUT_MAT = prove
 (`!(Fm:real^M->real^N^N) k B.
     compact k /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\x. lift(Fm x$i$j)) continuous_on k) /\
     (!x i j. x IN k ==> abs(Fm x$i$j) <= B) /\ &0 <= B
     ==> (!x i j. ~(x IN k) ==> (if x IN k then Fm x else mat 0)$i$j = &0) /\
         (!i j. (\x. lift((if x IN k then Fm x else mat 0)$i$j)) measurable_on (:real^M)) /\
         (!x i j. abs((if x IN k then Fm x else mat 0)$i$j) <= B)`,
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[MAT_0_COMPONENT];
    P2BW_IJ_TAC THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; MAT_0_COMPONENT; LIFT_NUM; MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    COND_CASES_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT; REAL_ABS_NUM]]);;

let P2BW_BIL_ZERO_MAT = prove
 (`!(u:real^(N,1)finite_sum->real) w z.
     p2bw_bil (\x. mat 0:real^N^N) u w z = &0`,
  REWRITE_TAC[p2bw_bil; MAT_0_COMPONENT; REAL_MUL_LZERO; SUM_0]);;

let P2BW_LOCGLOB = prove
 (`!(om:real^(N,1)finite_sum->bool) uu k (A:real^(N,1)finite_sum->real^N^N) c u w ug wg.
     open uu /\ k SUBSET uu /\ k SUBSET om /\
     (!x. x IN uu ==> ug x = u x) /\ (!x. x IN uu ==> wg x = w x) /\
     (!x. x IN om /\ ~(x IN k) ==> c x * p2bw_bil A u w x = &0)
     ==> integral om (\z. lift(c z * p2bw_bil A u w z)) =
         integral (:real^(N,1)finite_sum)
           (\z. lift(p2bw_bil (\x. if x IN k then c x %% A x else mat 0) ug wg z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((c:real^(N,1)finite_sum->real) z *
                           p2bw_bil (A:real^(N,1)finite_sum->real^N^N) u w z)`;
                 `om:real^(N,1)finite_sum->bool`] INTEGRAL_RESTRICT_UNIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN BETA_TAC THEN
  ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN k` THENL
   [SUBGOAL_THEN `(z:real^(N,1)finite_sum) IN om /\ z IN uu` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (\y. lift((ug:real^(N,1)finite_sum->real) y)) (at z) =
      frechet_derivative (\y. lift(u y)) (at z) /\
      frechet_derivative (\y. lift((wg:real^(N,1)finite_sum->real) y)) (at z) =
      frechet_derivative (\y. lift(w y)) (at z)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `uu:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[p2bw_bil; wan_xder; MATRIX_CMUL_COMPONENT; GSYM SUM_LMUL; REAL_MUL_ASSOC];
    SUBGOAL_THEN
     `p2bw_bil (\x. if x IN k then (c:real^(N,1)finite_sum->real) x %%
                                   (A:real^(N,1)finite_sum->real^N^N) x else mat 0)
               ug wg z = &0`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[p2bw_bil; MAT_0_COMPONENT; REAL_MUL_LZERO; SUM_0]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LIFT_NUM]]);;

let P2BW_LOCGLOB_D = prove
 (`!(om:real^M->bool) uu k (c:real^M->real) u ug v.
     open uu /\ k SUBSET uu /\ k SUBSET om /\
     (!x. x IN uu ==> ug x = u x) /\ (!x. ~(x IN k) ==> c x = &0)
     ==> integral om (\z. lift(c z * drop(frechet_derivative (\y. lift(u y)) (at z) v))) =
         integral (:real^M)
           (\z. lift(drop(frechet_derivative (\y. lift(ug y)) (at z) v) *
                     ((if z IN k then c z else &0) * &1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((c:real^M->real) z *
                           drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at z) v))`;
                 `om:real^M->bool`] INTEGRAL_RESTRICT_UNIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^M` THEN BETA_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
  ASM_CASES_TAC `(z:real^M) IN k` THENL
   [SUBGOAL_THEN `(z:real^M) IN om /\ z IN uu` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (\y. lift((ug:real^M->real) y)) (at z) =
      frechet_derivative (\y. lift(u y)) (at z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `uu:real^M->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; LIFT_NUM; COND_ID]]);;

let P2BW_LOCGLOB_F = prove
 (`!(om:real^M->bool) k (f:real^M->real).
     k SUBSET om /\ (!x. x IN om /\ ~(x IN k) ==> f x = &0)
     ==> integral om (\z. lift(f z)) =
         integral (:real^M) (\z. lift(if z IN k then f z else &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((f:real^M->real) z)`; `om:real^M->bool`] INTEGRAL_RESTRICT_UNIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^M` THEN BETA_TAC THEN
  ASM_CASES_TAC `(z:real^M) IN k` THENL
   [SUBGOAL_THEN `(z:real^M) IN om` ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    COND_CASES_TAC THEN ASM_SIMP_TAC[LIFT_NUM]]);;

let P2BW_ARITH_SMALLPROD = prove
 (`!a b e c. &0 < c /\ &0 < e /\ abs a < e / c /\ abs b <= c - &1 ==> abs(a * b) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `&0 < e / c` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / c * (c - &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `e / c * (c - &1) = e - e / c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]);;

let P2BW_LIM_VSUM2_0 = prove
 (`!(f:num->num->num->real^1) n.
     (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> ((\m. f i j m) --> vec 0) sequentially)
     ==> ((\m. vsum(1..n) (\i. vsum(1..n) (\j. f i j m))) --> vec 0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vec 0:real^1 = vsum(1..n) (\i. vsum(1..n) (\j. vec 0))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL [REWRITE_TAC[VSUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[ETA_AX]);;

let P2BW_BIL_SMALL = prove
 (`!(u:num->real^(N,1)finite_sum->real) (w:num->real^(N,1)finite_sum->real) L
    (V:num->real^(N,1)finite_sum->real^N^N) k.
     &0 <= L /\ (!m x y. abs(u m x - u m y) <= L * norm(x - y)) /\
     (!m x y. abs(w m x - w m y) <= L * norm(x - y)) /\ compact k /\
     (!m x i j. ~(x IN k) ==> V m x$i$j = &0) /\
     (!m i j. (\x. lift(V m x$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
     (!m. ?BV. !x i j. abs(V m x$i$j) <= BV) /\
     (!e. &0 < e ==> ?M. !m x i j. M <= m ==> abs(V m x$i$j) < e)
     ==> ((\m. integral (:real^(N,1)finite_sum) (\x. lift(p2bw_bil (V m) (u m) (w m) x))) -->
          vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m:num. integral (:real^(N,1)finite_sum)
              (\x. lift(p2bw_bil ((V:num->real^(N,1)finite_sum->real^N^N) m)
                          ((u:num->real^(N,1)finite_sum->real) m)
                          ((w:num->real^(N,1)finite_sum->real) m) x)) =
        vsum(1..dimindex(:N))
          (\i. vsum(1..dimindex(:N))
                 (\j. integral (:real^(N,1)finite_sum)
                        (\x. lift(drop(frechet_derivative (\y. lift(u m y)) (at x)
                                         (pastecart (basis i) (vec 0))) *
                                  (V m x$i$j * p2bw_trd (w m) (pastecart (basis j) (vec 0)) x)))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `m:num` THEN
    FIRST_ASSUM(X_CHOOSE_TAC `BV:real` o SPEC `m:num`) THEN
    MP_TAC(ISPECL [`(u:num->real^(N,1)finite_sum->real) m`;
                   `(w:num->real^(N,1)finite_sum->real) m`;
                   `L:real`; `(V:num->real^(N,1)finite_sum->real^N^N) m`; `BV:real`;
                   `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BW_LIM_VSUM2_0 THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real^(N,1)finite_sum->real`; `L:real`;
                 `\m x. (V:num->real^(N,1)finite_sum->real^N^N) m x$i$j *
                        p2bw_trd ((w:num->real^(N,1)finite_sum->real) m)
                                 (pastecart (basis j:real^N) (vec 0:real^1)) x`;
                 `k:real^(N,1)finite_sum->bool`; `pastecart (basis i:real^N) (vec 0:real^1)`]
                P2BW_DERIV_SMALL_WEIGHT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO] THEN CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(w:num->real^(N,1)finite_sum->real) m`; `L:real`;
                   `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_TRD_FACTS) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `c = L * norm(pastecart (basis j:real^N) (vec 0:real^1)) + &1` THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / c` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real`)) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    EXISTS_TAC `M:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BW_ARITH_SMALLPROD THEN EXISTS_TAC `c:real` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`(w:num->real^(N,1)finite_sum->real) m`; `L:real`;
                   `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_TRD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^(N,1)finite_sum` o CONJUNCT1 o CONJUNCT2) THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC]);;

let P2BW_INT_SMALL = prove
 (`!(X:real^M->real) k e.
     compact k /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (!x. abs(X x) <= e)
     ==> abs(drop(integral (:real^M) (\x. lift(X x)))) <= e * measure k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^M->real`; `e:real`; `k:real^M->bool`] WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^M->real`; `k:real^M->bool`; `e:real`] P2BW_INT_ABS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_LE_REFL] THEN
  UNDISCH_TAC `(\x. lift((X:real^M->real) x)) absolutely_integrable_on (:real^M)` THEN
  REWRITE_TAC[absolutely_integrable_on; NORM_LIFT] THEN SIMP_TAC[]);;

let P2BW_LIMIT_LOCLIP = prove
 (`!(om:real^M->bool) (l:num->real^M->real) l0.
     (!k. compact k /\ k SUBSET om
          ==> ?L. !n z w. z IN k /\ w IN k ==> abs(l n z - l n w) <= L * norm(z - w)) /\
     (!k e. compact k /\ k SUBSET om /\ &0 < e
            ==> ?M. !n z. M <= n /\ z IN k ==> abs(l n z - l0 z) < e)
     ==> (!n. wan_loclip om (l n)) /\ wan_loclip om l0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UL") (LABEL_TAC "LU")) THEN
  REWRITE_TAC[wan_loclip] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `k:real^M->bool`] THEN DISCH_TAC THEN
    USE_THEN "UL" (MP_TAC o SPEC `k:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
    USE_THEN "UL" (MP_TAC o SPEC `k:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` (LABEL_TAC "L")) THEN EXISTS_TAC `L:real` THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "LU" (MP_TAC o SPECL [`k:real^M->bool`;
      `(abs((l0:real^M->real) x - l0 y) - L * norm(x - y:real^M)) / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (fun th ->
      MP_TAC(MP (SPECL [`M:num`; `x:real^M`] th)
                (CONJ (SPEC `M:num` LE_REFL) (ASSUME `(x:real^M) IN k`))) THEN
      MP_TAC(MP (SPECL [`M:num`; `y:real^M`] th)
                (CONJ (SPEC `M:num` LE_REFL) (ASSUME `(y:real^M) IN k`))))) THEN
    USE_THEN "L" (MP_TAC o SPECL [`M:num`; `x:real^M`; `y:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `L * norm(x - y:real^M) < abs((l0:real^M->real) x - l0 y)` THEN
    REAL_ARITH_TAC]);;

(* s2: Claim 9.22 for one index in global form (cutoff weights, global   *)
(* Lipschitz extensions). *)

let P2BW_CONT_PROD = prove
 (`!(f:real^M->real) g s.
     (\x. lift(f x)) continuous_on s /\ (\x. lift(g x)) continuous_on s
     ==> (\x. lift(f x * g x)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_REWRITE_TAC[o_DEF]);;

let P2BW_CONT_LINC = prove
 (`!(f:real^M->real) g c s.
     (\x. lift(f x)) continuous_on s /\ (\x. lift(g x)) continuous_on s
     ==> (\x. lift(f x - g x + c)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[]);;

let P2BW_BIL_TEST_ZERO = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) l phi k x.
     wan_test om phi /\ compact k /\ (!z. ~(z IN k) ==> phi z = &0) /\ ~(x IN k)
     ==> p2bw_bil A l phi x = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_xder j (phi:real^(N,1)finite_sum->real) x = &0` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_xder] THEN
    MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`;
                   `pastecart (basis j:real^N) (vec 0:real^1)`; `x:real^(N,1)finite_sum`]
                  WAN_TEST_DERIV_ZERO) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[wan_test]; SIMP_TAC[DROP_VEC]];
    ASM_REWRITE_TAC[p2bw_bil; REAL_MUL_RZERO; SUM_0]]);;

let P2BW_CLAIM922_GLOBAL = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l l0 phi ep k
    uu lg lg0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_loclip om l0 /\ p2bw_t2 om A rho R l /\
     wan_test om phi /\ (!z. &0 <= phi z) /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> phi z = &0) /\ (!z. z IN k ==> abs(l z - l0 z) <= ep) /\
     open uu /\ k SUBSET uu /\ (!x. x IN uu ==> lg x = l x) /\ (!x. x IN uu ==> lg0 x = l0 x)
     ==> drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k then phi x %% A x else mat 0) lg lg x))) <=
         drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k then phi x %% A x else mat 0) lg lg0 x))) +
         drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k then (l0 x - l x + ep) %% A x else mat 0)
                                  lg phi x))) -
         (--drop(integral (:real^(N,1)finite_sum)
                  (\x. lift(p2bw_bil (\x. if x IN k then (phi x * (l0 x - l x + ep)) %% A x
                                          else mat 0) lg lg x))) +
          drop(integral (:real^(N,1)finite_sum)
                  (\x. lift(if x IN k
                            then (phi x * (l0 x - l x + ep)) *
                                 ((R x + (l x - &(dimindex(:N))) / drop(sndcart x)) * rho x)
                            else &0)))) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                 `rho:real^(N,1)finite_sum->real`; `R:real^(N,1)finite_sum->real`;
                 `l:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                 `phi:real^(N,1)finite_sum->real`; `ep:real`; `k:real^(N,1)finite_sum->bool`]
                P2BW_CLAIM922_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `l:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`; `ep:real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_PSI_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `p2bw_ltest om (\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_ltest] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(((phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)) *
              p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z)) integrable_on om /\
    (\z. lift((phi z * (l0 z - l z + ep)) *
              (((R:real^(N,1)finite_sum->real) z + (l z - &(dimindex(:N))) / drop(sndcart z)) *
               rho z))) integrable_on om`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)`;
                     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l`] P2BW_LEBM_LTEST_INT) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)`;
                     `\z. ((R:real^(N,1)finite_sum->real) z +
                           (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z`]
                    P2BW_LEBM_LTEST_INT) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
      MATCH_MP_TAC P2BW_CONT_T2COEFF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\z. lift(((phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)) *
                         (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) +
                          ((R:real^(N,1)finite_sum->real) z +
                           (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z))) =
    --(integral om (\z. lift((phi z * (l0 z - l z + ep)) * p2bw_bil A l l z))) +
    integral om (\z. lift((phi z * (l0 z - l z + ep)) *
                          ((R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(((phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)) *
                (--(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) +
                 ((R:real^(N,1)finite_sum->real) z +
                  (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z))) =
      (\z. --(lift((phi z * (l0 z - l z + ep)) * p2bw_bil A l l z)) +
           lift((phi z * (l0 z - l z + ep)) *
                ((R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_NEG; GSYM LIFT_ADD] THEN GEN_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_NEG; INTEGRABLE_NEG]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`; `uu:real^(N,1)finite_sum->bool`;
     `k:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `\z. (phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)`;
     `l:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
     `lg:real^(N,1)finite_sum->real`; `lg:real^(N,1)finite_sum->real`] P2BW_LOCGLOB)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LZERO]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`;
     `\z. ((phi:real^(N,1)finite_sum->real) z * (l0 z - l z + ep)) *
          (((R:real^(N,1)finite_sum->real) z + (l z - &(dimindex(:N))) / drop(sndcart z)) *
           rho z)`] P2BW_LOCGLOB_F)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LZERO]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `uu:real^(N,1)finite_sum->bool`;
     `k:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `phi:real^(N,1)finite_sum->real`;
     `l:real^(N,1)finite_sum->real`; `l:real^(N,1)finite_sum->real`;
     `lg:real^(N,1)finite_sum->real`; `lg:real^(N,1)finite_sum->real`] P2BW_LOCGLOB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LZERO]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `uu:real^(N,1)finite_sum->bool`;
     `k:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `phi:real^(N,1)finite_sum->real`;
     `l:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
     `lg:real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`] P2BW_LOCGLOB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LZERO]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`; `uu:real^(N,1)finite_sum->bool`;
     `k:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
     `\z. (l0:real^(N,1)finite_sum->real) z - l z + ep`;
     `l:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
     `lg:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`] P2BW_LOCGLOB)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                   `l:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
                   `k:real^(N,1)finite_sum->bool`; `x:real^(N,1)finite_sum`]
                  P2BW_BIL_TEST_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_ADD; DROP_NEG] THEN DISCH_THEN ACCEPT_TAC);;

(* s3: Claim 9.22 as a sequence (the upper-bound hypothesis of           *)
(* P2BW_ENERGY_GLOBAL). *)

let P2BW_ABS_MUL_LE = prove
 (`!a b A B. abs a <= A /\ abs b <= B ==> abs(a * b) <= A * B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let P2BW_ARITH_COMBINE = prove
 (`!x1 x2 a b c e. x1 <= x2 + a - (--b + c) / &2 ==> abs a < e / &2 ==> abs b < e / &2 ==>
                   abs c < e / &2 ==> x1 <= x2 + e`,
  REAL_ARITH_TAC);;

let P2BW_CLAIM922_SEQ = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:num->real^(N,1)finite_sum->real^N^N) rho R l l0 phi k
    uu lg lg0 L ep BA Bphi BQ.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (\z. lift(A m z$i$j)) continuous_on om) /\
     (!m. (\z. lift(rho m z)) continuous_on om /\ (\z. lift(R m z)) continuous_on om) /\
     (!m. wan_loclip om (l m)) /\ wan_loclip om l0 /\
     (!m. p2bw_t2 om (A m) (rho m) (R m) (l m)) /\
     wan_test om phi /\ (!z. &0 <= phi z) /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> phi z = &0) /\
     open uu /\ k SUBSET uu /\
     (!m x. x IN uu ==> lg m x = l m x) /\ (!x. x IN uu ==> lg0 x = l0 x) /\
     &0 <= L /\ (!m x y. abs(lg m x - lg m y) <= L * norm(x - y)) /\
     (!x y. abs(phi x - phi y) <= L * norm(x - y)) /\
     (!m. &0 < ep m) /\ (!m x. x IN k ==> abs(l m x - l0 x) <= ep m) /\
     (!e. &0 < e ==> ?M. !m. M <= m ==> ep m < e) /\
     &0 <= BA /\ (!m x i j. x IN k ==> abs(A m x$i$j) <= BA) /\
     &0 <= Bphi /\ (!x. abs(phi x) <= Bphi) /\
     &0 <= BQ /\
     (!m x. x IN k
            ==> abs((R m x + (l m x - &(dimindex(:N))) / drop(sndcart x)) * rho m x) <= BQ)
     ==> !e. &0 < e
             ==> ?M. !m. M <= m
                   ==> drop(integral (:real^(N,1)finite_sum)
                             (\x. lift(p2bw_bil (\x. if x IN k then phi x %% A m x else mat 0)
                                                (lg m) (lg m) x))) <=
                       drop(integral (:real^(N,1)finite_sum)
                             (\x. lift(p2bw_bil (\x. if x IN k then phi x %% A m x else mat 0)
                                                (lg m) lg0 x))) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. (\x. lift((l:num->real^(N,1)finite_sum->real) m x)) continuous_on k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((l0:real^(N,1)finite_sum->real) x)) continuous_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((phi:real^(N,1)finite_sum->real) x)) continuous_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN
    REWRITE_TAC[OPEN_UNIV; wan_loclip] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\x. lift((A:num->real^(N,1)finite_sum->real^N^N) m x$i$j)) continuous_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (\x. lift(((R:num->real^(N,1)finite_sum->real) m x +
                   ((l:num->real^(N,1)finite_sum->real) m x - &(dimindex(:N))) /
                   drop(sndcart x)) * (rho:num->real^(N,1)finite_sum->real) m x))
        continuous_on k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_CONT_T2COEFF THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  (* Claim 9.22 for each index *)
  SUBGOAL_THEN
   `!m. drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k then (phi:real^(N,1)finite_sum->real) x %%
                                                      (A:num->real^(N,1)finite_sum->real^N^N) m x
                                       else mat 0)
                                  ((lg:num->real^(N,1)finite_sum->real) m) (lg m) x))) <=
        drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k then phi x %% A m x else mat 0) (lg m)
                                  (lg0:real^(N,1)finite_sum->real) x))) +
        drop(integral (:real^(N,1)finite_sum)
               (\x. lift(p2bw_bil (\x. if x IN k
                                       then ((l0:real^(N,1)finite_sum->real) x -
                                             (l:num->real^(N,1)finite_sum->real) m x +
                                             (ep:num->real) m) %% A m x
                                       else mat 0)
                                  (lg m) phi x))) -
        (--drop(integral (:real^(N,1)finite_sum)
                 (\x. lift(p2bw_bil (\x. if x IN k then (phi x * (l0 x - l m x + ep m)) %% A m x
                                         else mat 0) (lg m) (lg m) x))) +
         drop(integral (:real^(N,1)finite_sum)
                 (\x. lift(if x IN k
                           then (phi x * (l0 x - l m x + ep m)) *
                                (((R:num->real^(N,1)finite_sum->real) m x +
                                  (l m x - &(dimindex(:N))) / drop(sndcart x)) *
                                 (rho:num->real^(N,1)finite_sum->real) m x)
                           else &0)))) / &2`
  (LABEL_TAC "STEP") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `(A:num->real^(N,1)finite_sum->real^N^N) m`;
                   `(rho:num->real^(N,1)finite_sum->real) m`;
                   `(R:num->real^(N,1)finite_sum->real) m`;
                   `(l:num->real^(N,1)finite_sum->real) m`; `l0:real^(N,1)finite_sum->real`;
                   `phi:real^(N,1)finite_sum->real`; `(ep:num->real) m`;
                   `k:real^(N,1)finite_sum->bool`; `uu:real^(N,1)finite_sum->bool`;
                   `(lg:num->real^(N,1)finite_sum->real) m`; `lg0:real^(N,1)finite_sum->real`]
                  P2BW_CLAIM922_GLOBAL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the weight of E1 *)
  SUBGOAL_THEN
   `!m. (!i j. (\x. lift((if x IN k
                          then ((l0:real^(N,1)finite_sum->real) x -
                                (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m) %%
                               (A:num->real^(N,1)finite_sum->real^N^N) m x
                          else mat 0)$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
        (!x i j. abs((if x IN k then (l0 x - l m x + ep m) %% A m x else mat 0)$i$j) <=
                 (&2 * ep m) * BA)`
  (LABEL_TAC "V1") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. ((l0:real^(N,1)finite_sum->real) x - (l:num->real^(N,1)finite_sum->real) m x +
             (ep:num->real) m) %% (A:num->real^(N,1)finite_sum->real^N^N) m x`;
       `k:real^(N,1)finite_sum->bool`; `(&2 * (ep:num->real) m) * BA`] P2BW_CUT_MAT)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_LINC];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[] THEN
        MP_TAC(MP (SPECL [`m:num`; `x:real^(N,1)finite_sum`]
                     (ASSUME `!m x. x IN k ==> abs((l:num->real^(N,1)finite_sum->real) m x -
                                                  l0 x) <= ep m`))
                  (ASSUME `(x:real^(N,1)finite_sum) IN k`)) THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the weight of F2 *)
  SUBGOAL_THEN
   `!m. (!i j. (\x. lift((if x IN k
                          then ((phi:real^(N,1)finite_sum->real) x *
                                ((l0:real^(N,1)finite_sum->real) x -
                                 (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m)) %%
                               (A:num->real^(N,1)finite_sum->real^N^N) m x
                          else mat 0)$i$j)) measurable_on (:real^(N,1)finite_sum)) /\
        (!x i j. abs((if x IN k then (phi x * (l0 x - l m x + ep m)) %% A m x else mat 0)$i$j) <=
                 (Bphi * (&2 * ep m)) * BA)`
  (LABEL_TAC "V2") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. ((phi:real^(N,1)finite_sum->real) x *
             ((l0:real^(N,1)finite_sum->real) x - (l:num->real^(N,1)finite_sum->real) m x +
              (ep:num->real) m)) %% (A:num->real^(N,1)finite_sum->real^N^N) m x`;
       `k:real^(N,1)finite_sum->bool`; `(Bphi * (&2 * (ep:num->real) m)) * BA`] P2BW_CUT_MAT)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_LINC];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(MP (SPECL [`m:num`; `x:real^(N,1)finite_sum`]
                     (ASSUME `!m x. x IN k ==> abs((l:num->real^(N,1)finite_sum->real) m x -
                                                  l0 x) <= ep m`))
                  (ASSUME `(x:real^(N,1)finite_sum) IN k`)) THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* E1 tends to 0 *)
  SUBGOAL_THEN
   `((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil (\x. if x IN k
                                    then ((l0:real^(N,1)finite_sum->real) x -
                                          (l:num->real^(N,1)finite_sum->real) m x +
                                          (ep:num->real) m) %%
                                         (A:num->real^(N,1)finite_sum->real^N^N) m x
                                    else mat 0)
                               ((lg:num->real^(N,1)finite_sum->real) m) phi x))) --> vec 0)
    sequentially`
  (LABEL_TAC "E1") THENL
   [MP_TAC(ISPECL [`lg:num->real^(N,1)finite_sum->real`; `\m:num. (phi:real^(N,1)finite_sum->real)`;
                   `L:real`;
                   `\m x. if x IN k
                          then ((l0:real^(N,1)finite_sum->real) x -
                                (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m) %%
                               (A:num->real^(N,1)finite_sum->real^N^N) m x
                          else mat 0`;
                   `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SMALL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SIMP_TAC[MAT_0_COMPONENT];
      USE_THEN "V1" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `m:num` THEN EXISTS_TAC `(&2 * (ep:num->real) m) * BA` THEN
      USE_THEN "V1" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e / (&2 * BA + &1)`
        (ASSUME `!e. &0 < e ==> ?M. !m. M <= m ==> (ep:num->real) m < e`)) THEN
      ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`; `i:num`; `j:num`] THEN
      DISCH_TAC THEN MATCH_MP_TAC P2BW_ARITH_DIV THEN
      MAP_EVERY EXISTS_TAC [`&2 * BA`; `(ep:num->real) m`] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[];
        USE_THEN "V1" (MP_TAC o SPECL [`x:real^(N,1)finite_sum`; `i:num`; `j:num`] o
                       CONJUNCT2 o SPEC `m:num`) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* F2 tends to 0 *)
  SUBGOAL_THEN
   `((\m. integral (:real^(N,1)finite_sum)
            (\x. lift(p2bw_bil (\x. if x IN k
                                    then ((phi:real^(N,1)finite_sum->real) x *
                                          ((l0:real^(N,1)finite_sum->real) x -
                                           (l:num->real^(N,1)finite_sum->real) m x +
                                           (ep:num->real) m)) %%
                                         (A:num->real^(N,1)finite_sum->real^N^N) m x
                                    else mat 0)
                               ((lg:num->real^(N,1)finite_sum->real) m) (lg m) x))) --> vec 0)
    sequentially`
  (LABEL_TAC "F2") THENL
   [MP_TAC(ISPECL [`lg:num->real^(N,1)finite_sum->real`; `lg:num->real^(N,1)finite_sum->real`;
                   `L:real`;
                   `\m x. if x IN k
                          then ((phi:real^(N,1)finite_sum->real) x *
                                ((l0:real^(N,1)finite_sum->real) x -
                                 (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m)) %%
                               (A:num->real^(N,1)finite_sum->real^N^N) m x
                          else mat 0`;
                   `k:real^(N,1)finite_sum->bool`] P2BW_BIL_SMALL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SIMP_TAC[MAT_0_COMPONENT];
      USE_THEN "V2" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `m:num` THEN EXISTS_TAC `(Bphi * (&2 * (ep:num->real) m)) * BA` THEN
      USE_THEN "V2" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e / (&2 * Bphi * BA + &1)`
        (ASSUME `!e. &0 < e ==> ?M. !m. M <= m ==> (ep:num->real) m < e`)) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`; `i:num`; `j:num`] THEN
      DISCH_TAC THEN MATCH_MP_TAC P2BW_ARITH_DIV THEN
      MAP_EVERY EXISTS_TAC [`&2 * Bphi * BA`; `(ep:num->real) m`] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[];
        USE_THEN "V2" (MP_TAC o SPECL [`x:real^(N,1)finite_sum`; `i:num`; `j:num`] o
                       CONJUNCT2 o SPEC `m:num`) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* G2 is bounded by a multiple of ep m *)
  SUBGOAL_THEN
   `!m. abs(drop(integral (:real^(N,1)finite_sum)
                  (\x. lift(if x IN k
                            then ((phi:real^(N,1)finite_sum->real) x *
                                  ((l0:real^(N,1)finite_sum->real) x -
                                   (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m)) *
                                 (((R:num->real^(N,1)finite_sum->real) m x +
                                   (l m x - &(dimindex(:N))) / drop(sndcart x)) *
                                  (rho:num->real^(N,1)finite_sum->real) m x)
                            else &0)))) <=
        (&2 * Bphi * BQ * measure(k:real^(N,1)finite_sum->bool)) * ep m`
  (LABEL_TAC "G2B") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. if x IN k
            then ((phi:real^(N,1)finite_sum->real) x *
                  ((l0:real^(N,1)finite_sum->real) x -
                   (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m)) *
                 (((R:num->real^(N,1)finite_sum->real) m x +
                   (l m x - &(dimindex(:N))) / drop(sndcart x)) *
                  (rho:num->real^(N,1)finite_sum->real) m x)
            else &0`;
       `k:real^(N,1)finite_sum->bool`; `(Bphi * (&2 * (ep:num->real) m)) * BQ`]
      P2BW_INT_SMALL)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        SIMP_TAC[];
        MATCH_MP_TAC P2BW_CUT_MEAS THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_LINC];
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN COND_CASES_TAC THENL
         [MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[] THEN
          MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(MP (SPECL [`m:num`; `x:real^(N,1)finite_sum`]
                       (ASSUME `!m x. x IN k ==> abs((l:num->real^(N,1)finite_sum->real) m x -
                                                    l0 x) <= ep m`))
                    (ASSUME `(x:real^(N,1)finite_sum) IN k`)) THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC]];
      MATCH_MP_TAC(REAL_ARITH `!a b c. b = c ==> a <= b ==> a <= c`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* combine *)
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "E1" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop; DROP_VEC;
                                       REAL_SUB_RZERO]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "F2" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop; DROP_VEC;
                                       REAL_SUB_RZERO]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  SUBGOAL_THEN `&0 <= &2 * Bphi * BQ * measure(k:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MP_TAC(SPEC `e / &2 / (&2 * Bphi * BQ * measure(k:real^(N,1)finite_sum->bool) + &1)`
    (ASSUME `!e. &0 < e ==> ?M. !m. M <= m ==> (ep:num->real) m < e`)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= m /\ N2 <= m /\ N3 <= m:num` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(drop(integral (:real^(N,1)finite_sum)
                  (\x. lift(if x IN k
                            then ((phi:real^(N,1)finite_sum->real) x *
                                  ((l0:real^(N,1)finite_sum->real) x -
                                   (l:num->real^(N,1)finite_sum->real) m x + (ep:num->real) m)) *
                                 (((R:num->real^(N,1)finite_sum->real) m x +
                                   (l m x - &(dimindex(:N))) / drop(sndcart x)) *
                                  (rho:num->real^(N,1)finite_sum->real) m x)
                            else &0)))) < e / &2`
  MP_TAC THENL
   [MATCH_MP_TAC P2BW_ARITH_DIV THEN
    MAP_EVERY EXISTS_TAC [`&2 * Bphi * BQ * measure(k:real^(N,1)finite_sum->bool)`;
                          `(ep:num->real) m`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `m:num` (ASSUME `!m. &0 < (ep:num->real) m`)) THEN REAL_ARITH_TAC;
      USE_THEN "N3" (MP_TAC o C MP (ASSUME `N3 <= m:num`) o SPEC `m:num`) THEN
      REWRITE_TAC[];
      USE_THEN "G2B" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "N2" (MP_TAC o C MP (ASSUME `N2 <= m:num`) o SPEC `m:num`) THEN
  USE_THEN "N1" (MP_TAC o C MP (ASSUME `N1 <= m:num`) o SPEC `m:num`) THEN
  USE_THEN "STEP" (MP_TAC o SPEC `m:num`) THEN
  MATCH_ACCEPT_TAC P2BW_ARITH_COMBINE);;

(* s4: MT Lemma 9.21, the local energy convergence (P2BW_ENERGY_LOCAL). *)

let P2BW_UNIF_M_ALL = prove
 (`!(A:num->real^M->real^N^N) (A0:real^M->real^N^N) k.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> !e. &0 < e ==> ?N. !m x. N <= m /\ x IN k ==> abs(A m x$i$j - A0 x$i$j) < e)
     ==> !e. &0 < e ==> ?N. !m x i j. N <= m /\ x IN k ==> abs(A m x$i$j - A0 x$i$j) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?N. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> !m x. N <= m /\ x IN k
                        ==> abs((A:num->real^M->real^N^N) m x$i$j -
                                (A0:real^M->real^N^N) x$i$j) < e`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `NN:num->num->num` (LABEL_TAC "NN"))] THEN
  MP_TAC(ISPECL [`\p:num#num. (NN:num->num->num) (FST p) (SND p)`;
                 `(1..dimindex(:N)) CROSS (1..dimindex(:N))`] UPPER_BOUND_FINITE_SET) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (LABEL_TAC "A")) THEN EXISTS_TAC `a:num` THEN
  REPEAT GEN_TAC THEN P2BW_IJ_TAC THEN STRIP_TAC THEN
  USE_THEN "NN" (MP_TAC o SPECL [`i':num`; `j':num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "A" (MP_TAC o SPECL [`i':num`; `j':num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC]);;

let P2BW_CONT_BOUND = prove
 (`!(f:real^M->real) k.
     compact k /\ (\x. lift(f x)) continuous_on k
     ==> ?B. &0 <= B /\ !x. x IN k ==> abs(f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((f:real^M->real) x)`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let P2BW_ARITH_QB = prove
 (`!R l s r c BR Bl Bt Br.
     abs R <= BR /\ abs l <= Bl /\ abs(inv s) <= Bt /\ abs r <= Br
     ==> abs((R + (l - c) / s) * r) <= (BR + (Bl + abs c) * Bt) * Br`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b A B. abs a <= A /\ abs b <= B ==> abs(a + b) <= A + B`) THEN
  ASM_REWRITE_TAC[real_div] THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P2BW_CUTW_PSD = prove
 (`!(A:real^M->real^N^N) phi k.
     (!x. x IN k ==> transp(A x) = A x /\ (!v. &0 <= v dot (A x ** v))) /\ (!x. &0 <= phi x)
     ==> !x. transp(if x IN k then phi x %% A x else mat 0) =
             (if x IN k then phi x %% A x else mat 0) /\
             (!v. &0 <= v dot ((if x IN k then phi x %% A x else mat 0) ** v))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; REAL_LE_REFL;
               MATRIX_VECTOR_LMUL; DOT_RMUL; REAL_LE_MUL]);;

let P2BW_ENERGY_LOCAL = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:num->real^(N,1)finite_sum->real^N^N) rho R l
    (A0:real^(N,1)finite_sum->real^N^N) rho0 R0 l0 phi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!m. p2bw_coeff om (A m) (rho m) /\ (\z. lift(R m z)) continuous_on om) /\
     (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A0 z)) continuous_on om /\
     p2bw_locunif_m om A A0 /\ p2bw_locunif om rho rho0 /\ p2bw_locunif om R R0 /\
     p2bw_unilip om l /\ p2bw_locunif om l l0 /\
     (!m. p2bw_t2 om (A m) (rho m) (R m) (l m)) /\
     wan_test om phi /\ (!z. &0 <= phi z)
     ==> ((\m. integral om (\z. lift(phi z * p2bw_bil (A m) (l m) (l m) z))) -->
          integral om (\z. lift(phi z * p2bw_bil A0 l0 l0 z))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP P2BW_LIMIT_LOCLIP
    (CONJ (REWRITE_RULE[p2bw_unilip]
             (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`))
          (REWRITE_RULE[p2bw_locunif]
             (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\z. lift((A:num->real^(N,1)finite_sum->real^N^N) m z$i$j)) continuous_on om) /\
    (!m. (\z. lift((rho:num->real^(N,1)finite_sum->real) m z)) continuous_on om) /\
    (!m z. z IN om ==> transp(A m z) = A m z /\ (!v. &0 <= v dot (A m z ** v)) /\
                       &0 <= rho m z) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((A0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((A0:real^(N,1)finite_sum->real^N^N) z)) continuous_on om` THEN
    UNDISCH_TAC `!m. p2bw_coeff om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m) /\
                     (\z. lift((R:num->real^(N,1)finite_sum->real) m z)) continuous_on om` THEN
    REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* localization *)
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `l:num->real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`] P2BW_LOCALIZE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[p2bw_unilip]
        (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`)) THEN MESON_TAC[];
      MP_TAC(REWRITE_RULE[p2bw_locunif]
        (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)) THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `lg:num->real^(N,1)finite_sum->real`
    (X_CHOOSE_THEN `lg0:real^(N,1)finite_sum->real` (X_CHOOSE_THEN `L:real`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(!m x. x IN {x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}
           ==> (lg:num->real^(N,1)finite_sum->real) m x = l m x) /\
    (!x. x IN {x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}
         ==> (lg0:real^(N,1)finite_sum->real) x = l0 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  (* phi is globally Lipschitz *)
  MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bp:real`) THEN
  SUBGOAL_THEN
   `&0 <= L + abs Bp /\
    (!m x y. abs((lg:num->real^(N,1)finite_sum->real) m x - lg m y) <=
             (L + abs Bp) * norm(x - y)) /\
    (!x y. abs((lg0:real^(N,1)finite_sum->real) x - lg0 y) <= (L + abs Bp) * norm(x - y)) /\
    (!x y. abs((phi:real^(N,1)finite_sum->real) x - phi y) <= (L + abs Bp) * norm(x - y))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Bp * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity on k *)
  SUBGOAL_THEN
   `(!m. (\x. lift((l:num->real^(N,1)finite_sum->real) m x)) continuous_on k) /\
    (\x. lift((l0:real^(N,1)finite_sum->real) x)) continuous_on k /\
    (\x. lift((phi:real^(N,1)finite_sum->real) x)) continuous_on k /\
    (!m. (\x. lift((rho:num->real^(N,1)finite_sum->real) m x)) continuous_on k) /\
    (!m. (\x. lift((R:num->real^(N,1)finite_sum->real) m x)) continuous_on k) /\
    (\x. lift(inv(drop(sndcart x)))) continuous_on k /\
    (!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\x. lift((A:num->real^(N,1)finite_sum->real^N^N) m x$i$j)) continuous_on k) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\x. lift((A0:real^(N,1)finite_sum->real^N^N) x$i$j)) continuous_on k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
     [EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX];
      EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN REWRITE_TAC[OPEN_UNIV; wan_loclip] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the vanishing bound sequence *)
  MP_TAC(ISPECL [`l:num->real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_SUP_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ep:num->real` STRIP_ASSUME_TAC)] THEN
  (* bounds on k *)
  MP_TAC(ISPECL [`A:num->real^(N,1)finite_sum->real^N^N`; `A0:real^(N,1)finite_sum->real^N^N`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED_M) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif_m; p2bw_locunif]
      (ASSUME `p2bw_locunif_m om (A:num->real^(N,1)finite_sum->real^N^N) A0`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e:real`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `BA:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`R:num->real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (R:num->real^(N,1)finite_sum->real) R0`)) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`rho:num->real^(N,1)finite_sum->real`; `rho0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (rho:num->real^(N,1)finite_sum->real) rho0`)) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Brho:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`l:num->real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Bl:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`\x:real^(N,1)finite_sum. inv(drop(sndcart x))`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bt:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bphi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. abs((phi:real^(N,1)finite_sum->real) x) <= Bphi` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(N,1)finite_sum` THEN ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN k` THEN
    ASM_SIMP_TAC[REAL_ABS_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m x. x IN k
          ==> abs(((R:num->real^(N,1)finite_sum->real) m x +
                   ((l:num->real^(N,1)finite_sum->real) m x - &(dimindex(:N))) /
                   drop(sndcart x)) * (rho:num->real^(N,1)finite_sum->real) m x) <=
              (BR + (Bl + abs(&(dimindex(:N)))) * Bt) * Brho`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ARITH_QB THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (BR + (Bl + abs(&(dimindex(:N)))) * Bt) * Brho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  (* the cut-off weights *)
  SUBGOAL_THEN
   `!m. (!x i j. ~(x IN k)
                 ==> (if x IN k then (phi:real^(N,1)finite_sum->real) x %%
                                     (A:num->real^(N,1)finite_sum->real^N^N) m x
                      else mat 0)$i$j = &0) /\
        (!i j. (\x. lift((if x IN k then phi x %% A m x else mat 0)$i$j))
               measurable_on (:real^(N,1)finite_sum)) /\
        (!x i j. abs((if x IN k then phi x %% A m x else mat 0)$i$j) <= Bphi * BA)`
  (LABEL_TAC "W") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. (phi:real^(N,1)finite_sum->real) x %% (A:num->real^(N,1)finite_sum->real^N^N) m x`;
       `k:real^(N,1)finite_sum->bool`; `Bphi * BA`] P2BW_CUT_MAT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x i j. ~(x IN k)
             ==> (if x IN k then (phi:real^(N,1)finite_sum->real) x %%
                                 (A0:real^(N,1)finite_sum->real^N^N) x
                  else mat 0)$i$j = &0) /\
    (!i j. (\x. lift((if x IN k then phi x %% A0 x else mat 0)$i$j))
           measurable_on (:real^(N,1)finite_sum)) /\
    (!x i j. abs((if x IN k then phi x %% A0 x else mat 0)$i$j) <= Bphi * BA)`
  (LABEL_TAC "W0") THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`\x. (phi:real^(N,1)finite_sum->real) x %% (A0:real^(N,1)finite_sum->real^N^N) x`;
       `k:real^(N,1)finite_sum->bool`; `Bphi * BA`] P2BW_CUT_MAT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* back to om *)
  SUBGOAL_THEN
   `!m. integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                              p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m) (l m) (l m) z)) =
        integral (:real^(N,1)finite_sum)
          (\z. lift(p2bw_bil (\x. if x IN k then phi x %% A m x else mat 0) (lg m) (lg m) z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BW_LOCGLOB THEN
    EXISTS_TAC `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}` THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                          p2bw_bil (A0:real^(N,1)finite_sum->real^N^N) l0 l0 z)) =
    integral (:real^(N,1)finite_sum)
      (\z. lift(p2bw_bil (\x. if x IN k then phi x %% A0 x else mat 0) lg0 lg0 z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BW_LOCGLOB THEN
    EXISTS_TAC `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}` THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  (* the global energy convergence *)
  MP_TAC(ISPECL [`lg:num->real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`;
                 `L + abs Bp`;
                 `\m x. if x IN k then (phi:real^(N,1)finite_sum->real) x %%
                                       (A:num->real^(N,1)finite_sum->real^N^N) m x
                        else mat 0`;
                 `\x. if x IN k then (phi:real^(N,1)finite_sum->real) x %%
                                     (A0:real^(N,1)finite_sum->real^N^N) x
                      else mat 0`;
                 `Bphi * BA`; `k:real^(N,1)finite_sum->bool`;
                 `{x + y:real^(N,1)finite_sum | x IN k /\ y IN cball(vec 0,d)}`; `d:real`]
                P2BW_ENERGY_GLOBAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_REFL];
    ASM_REWRITE_TAC[];
    USE_THEN "W" (fun th -> REWRITE_TAC[th]);
    USE_THEN "W0" (fun th -> REWRITE_TAC[th]);
    USE_THEN "W" (fun th -> REWRITE_TAC[th]);
    USE_THEN "W0" (fun th -> REWRITE_TAC[th]);
    USE_THEN "W" (fun th -> REWRITE_TAC[th]);
    USE_THEN "W0" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`A:num->real^(N,1)finite_sum->real^N^N`; `A0:real^(N,1)finite_sum->real^N^N`;
                   `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_M_ALL) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(REWRITE_RULE[p2bw_locunif_m; p2bw_locunif]
        (ASSUME `p2bw_locunif_m om (A:num->real^(N,1)finite_sum->real^N^N) A0`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e':real`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / (Bphi + &1)`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NA")) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`; `i:num`; `j:num`] THEN
    DISCH_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[MATRIX_CMUL_COMPONENT; GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      MATCH_MP_TAC P2BW_ARITH_DIV THEN
      MAP_EVERY EXISTS_TAC [`Bphi:real`;
                            `abs((A:num->real^(N,1)finite_sum->real^N^N) m x$i$j -
                                 (A0:real^(N,1)finite_sum->real^N^N) x$i$j)`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_ABS_POS];
        USE_THEN "NA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
      ASM_REWRITE_TAC[MAT_0_COMPONENT; REAL_SUB_REFL; REAL_ABS_NUM]];
    X_GEN_TAC `m:num` THEN MATCH_MP_TAC P2BW_CUTW_PSD THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^(N,1)finite_sum) IN om` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                   `rho:num->real^(N,1)finite_sum->real`; `R:num->real^(N,1)finite_sum->real`;
                   `l:num->real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`;
                   `phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`;
                   `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}`;
                   `lg:num->real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`;
                   `L + abs Bp`; `ep:num->real`; `BA:real`; `Bphi:real`;
                   `(BR + (Bl + abs(&(dimindex(:N)))) * Bt) * Brho`] P2BW_CLAIM922_SEQ) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* MT Lemma 9.23 (P2BW_T1_LIMIT: t1 passes to the limit) and the limit      *)
(* of the weak identity (P2BW_TID_LIMIT).  Tools: limits of continuous      *)
(* terms against a test function, local uniform convergence algebra,        *)
(* integrability of bilinear terms; P2BW_DERIV_PIECES (the time-derivative *)
(* term and the bilinear term with the test function converge).            *)
(* ------------------------------------------------------------------------- *)

(* s5: limits of the continuous terms, local uniform convergence algebra, *)
(* integrability of bilinear terms with a test function. *)

let P2BW_UNIF_INT_CONV = prove
 (`!(g:num->real^M->real) g0 k.
     compact k /\ (!m x. ~(x IN k) ==> g m x = &0) /\ (!x. ~(x IN k) ==> g0 x = &0) /\
     (!m. (\x. lift(g m x)) measurable_on (:real^M)) /\
     (\x. lift(g0 x)) measurable_on (:real^M) /\
     (!m. ?B. !x. abs(g m x) <= B) /\ (?B. !x. abs(g0 x) <= B) /\
     (!e. &0 < e ==> ?N. !m x. N <= m ==> abs(g m x - g0 x) < e)
     ==> ((\m. integral (:real^M) (\x. lift(g m x))) --> integral (:real^M) (\x. lift(g0 x)))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= measure(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (measure(k:real^M->bool) + &1) / &2` o check (fun th ->
    is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real`)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `Bm:real` o SPEC `m:num` o check (fun th ->
    is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  MP_TAC(ISPECL [`(g:num->real^M->real) m`; `Bm:real`; `k:real^M->bool`]
                WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ETA_AX]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g0:real^M->real`; `B:real`; `k:real^M->bool`]
                WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^M) (\x. lift((g:num->real^M->real) m x))) -
    drop(integral (:real^M) (\x. lift((g0:real^M->real) x))) =
    drop(integral (:real^M) (\x. lift(g m x - g0 x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_SUB; GSYM DROP_SUB] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BW_ARITH_DIV THEN
  MAP_EVERY EXISTS_TAC [`measure(k:real^M->bool)`;
                        `e / (measure(k:real^M->bool) + &1) / &2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC P2BW_INT_SMALL THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; LIFT_SUB] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let P2BW_CONT_TERM_LIMIT = prove
 (`!(om:real^M->bool) (phi:real^M->real) (Fm:num->real^M->real) F0 k.
     compact k /\ k SUBSET om /\ (!x. ~(x IN k) ==> phi x = &0) /\
     (\x. lift(phi x)) continuous_on k /\
     (!m. (\x. lift(Fm m x)) continuous_on k) /\ (\x. lift(F0 x)) continuous_on k /\
     (!e. &0 < e ==> ?N. !m x. N <= m /\ x IN k ==> abs(Fm m x - F0 x) < e)
     ==> ((\m. integral om (\z. lift(phi z * Fm m z))) --> integral om (\z. lift(phi z * F0 z)))
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. integral om (\z. lift((phi:real^M->real) z * (Fm:num->real^M->real) m z)) =
        integral (:real^M) (\z. lift(if z IN k then phi z * Fm m z else &0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BW_LOCGLOB_F THEN ASM_SIMP_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om (\z. lift((phi:real^M->real) z * (F0:real^M->real) z)) =
    integral (:real^M) (\z. lift(if z IN k then phi z * F0 z else &0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BW_LOCGLOB_F THEN ASM_SIMP_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bp:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Fm:num->real^M->real`; `F0:real^M->real`; `k:real^M->bool`]
                P2BW_UNIF_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `BF:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2BW_UNIF_INT_CONV THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2BW_CUT_MEAS THEN ASM_SIMP_TAC[P2BW_CONT_PROD];
    MATCH_MP_TAC P2BW_CUT_MEAS THEN ASM_SIMP_TAC[P2BW_CONT_PROD];
    GEN_TAC THEN EXISTS_TAC `Bp * BF:real` THEN GEN_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `Bp * BF:real` THEN GEN_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (Bp + &1)` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:real`)) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NF")) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `x:real^M`] THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      MATCH_MP_TAC P2BW_ARITH_DIV THEN
      MAP_EVERY EXISTS_TAC [`Bp:real`;
                            `abs((Fm:num->real^M->real) m x - (F0:real^M->real) x)`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_ABS_POS];
        USE_THEN "NF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_ABS_POS]];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]]]);;

let P2BW_CONT_TERM_LIMIT_OM = prove
 (`!(om:real^(N,1)finite_sum->bool) phi (Fm:num->real^(N,1)finite_sum->real) F0.
     open om /\ wan_test om phi /\
     (!m. (\z. lift(Fm m z)) continuous_on om) /\ (\z. lift(F0 z)) continuous_on om /\
     p2bw_locunif om Fm F0
     ==> ((\m. integral om (\z. lift(phi z * Fm m z))) --> integral om (\z. lift(phi z * F0 z)))
         sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC P2BW_CONT_TERM_LIMIT THEN EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (Fm:num->real^(N,1)finite_sum->real) F0`)) THEN
    ASM_MESON_TAC[]]);;

let P2BW_ARITH_PROD_CONV = prove
 (`!a b a0 b0 A B e.
     &0 <= A /\ &0 <= B /\ &0 < e /\ abs a <= A /\ abs b0 <= B /\
     abs(b - b0) < e / &2 / (A + &1) /\ abs(a - a0) < e / &2 / (B + &1)
     ==> abs(a * b - a0 * b0) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs a * abs(b - b0) < e / &2 /\ abs b0 * abs(a - a0) < e / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BW_ARITH_DIV THENL
     [MAP_EVERY EXISTS_TAC [`A:real`; `abs(b - b0)`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]; ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
      MAP_EVERY EXISTS_TAC [`B:real`; `abs(a - a0)`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]; ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * b - a0 * b0 = a * (b - b0) + b0 * (a - a0)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y u v e. abs x <= u /\ abs y <= v /\ u < e / &2 /\ v < e / &2
                                       ==> abs(x + y) < e`) THEN
  MAP_EVERY EXISTS_TAC [`abs a * abs(b - b0)`; `abs b0 * abs(a - a0)`] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_LE_REFL]);;

let P2BW_LOCUNIF_SUB = prove
 (`!(om:real^(N,1)finite_sum->bool) f f0 g g0.
     p2bw_locunif om f f0 /\ p2bw_locunif om g g0
     ==> p2bw_locunif om (\m z. f m z - g m z) (\z. f0 z - g0 z)`,
  REWRITE_TAC[p2bw_locunif] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e / &2`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:num` (LABEL_TAC "M1")) THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:num` (LABEL_TAC "M2")) THEN
  EXISTS_TAC `M1 + M2:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `M1 <= n /\ M2 <= n:num` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "M1" (MP_TAC o C MP (CONJ (ASSUME `M1 <= n:num`)
    (ASSUME `(z:real^(N,1)finite_sum) IN k`)) o SPECL [`n:num`; `z:real^(N,1)finite_sum`]) THEN
  USE_THEN "M2" (MP_TAC o C MP (CONJ (ASSUME `M2 <= n:num`)
    (ASSUME `(z:real^(N,1)finite_sum) IN k`)) o SPECL [`n:num`; `z:real^(N,1)finite_sum`]) THEN
  REAL_ARITH_TAC);;

let P2BW_LOCUNIF_CONSTFN = prove
 (`!(om:real^(N,1)finite_sum->bool) (h:real^(N,1)finite_sum->real).
     p2bw_locunif om (\m:num z. h z) h`,
  REWRITE_TAC[p2bw_locunif; REAL_SUB_REFL; REAL_ABS_NUM] THEN MESON_TAC[]);;

let P2BW_LOCUNIF_MUL = prove
 (`!(om:real^(N,1)finite_sum->bool) f f0 g g0.
     (!m. (\z. lift(f m z)) continuous_on om) /\ (\z. lift(g0 z)) continuous_on om /\
     p2bw_locunif om f f0 /\ p2bw_locunif om g g0
     ==> p2bw_locunif om (\m z. f m z * g m z) (\z. f0 z * g0 z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_locunif] THEN
  MAP_EVERY X_GEN_TAC [`k:real^(N,1)finite_sum->bool`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^(N,1)finite_sum->real`; `f0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(REWRITE_RULE[p2bw_locunif]
        (ASSUME `p2bw_locunif om (f:num->real^(N,1)finite_sum->real) f0`)) THEN
      ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `Bf:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`g0:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                P2BW_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Bg:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`k:real^(N,1)finite_sum->bool`; `e / &2 / (Bf + &1)`]
    (REWRITE_RULE[p2bw_locunif]
       (ASSUME `p2bw_locunif om (g:num->real^(N,1)finite_sum->real) g0`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `M1:num` (LABEL_TAC "M1"))] THEN
  MP_TAC(SPECL [`k:real^(N,1)finite_sum->bool`; `e / &2 / (Bg + &1)`]
    (REWRITE_RULE[p2bw_locunif]
       (ASSUME `p2bw_locunif om (f:num->real^(N,1)finite_sum->real) f0`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `M2:num` (LABEL_TAC "M2"))] THEN
  EXISTS_TAC `M1 + M2:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `M1 <= n /\ M2 <= n:num` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BW_ARITH_PROD_CONV THEN MAP_EVERY EXISTS_TAC [`Bf:real`; `Bg:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    USE_THEN "M1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "M2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BW_BIL_TEST_INT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) l phi c.
     open om /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     wan_loclip om l /\ wan_test om phi /\ p2bw_lebm om c
     ==> (\z. lift(c z * p2bw_bil A l phi z)) integrable_on om`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[P2BW_BIL_PAIR] THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `\z. (c:real^(N,1)finite_sum->real) z *
                      sum(1..dimindex(:N))
                         (\i. (A:real^(N,1)finite_sum->real^N^N) z$i$j * wan_xder i l z)`;
                 `pastecart (basis j:real^N) (vec 0:real^1)`] P2BW_LEBM_TEST_INT) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BW_LEBM_MUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC P2BW_LEBM_SUM THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_SIMP_TAC[ETA_AX];
    REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* s6: the limits of the time-derivative term and of the bilinear term     *)
(* with the test function (Lemma 9.23 and the limit of the identity).     *)

let P2BW_DERIV_PIECES = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:num->real^(N,1)finite_sum->real^N^N) rho l
    (A0:real^(N,1)finite_sum->real^N^N) rho0 l0 phi.
     open om /\
     (!m. p2bw_coeff om (A m) (rho m)) /\ p2bw_coeff om A0 rho0 /\
     p2bw_locunif_m om A A0 /\ p2bw_locunif om rho rho0 /\
     p2bw_unilip om l /\ p2bw_locunif om l l0 /\
     wan_test om phi
     ==> ((\m. integral om (\z. lift(phi z * wan_tder (l m) z * rho m z))) -->
          integral om (\z. lift(phi z * wan_tder l0 z * rho0 z))) sequentially /\
         ((\m. integral om (\z. lift(p2bw_bil (A m) (l m) phi z))) -->
          integral om (\z. lift(p2bw_bil A0 l0 phi z))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP P2BW_LIMIT_LOCLIP
    (CONJ (REWRITE_RULE[p2bw_unilip]
             (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`))
          (REWRITE_RULE[p2bw_locunif]
             (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\z. lift((A:num->real^(N,1)finite_sum->real^N^N) m z$i$j)) continuous_on om) /\
    (!m. (\z. lift((rho:num->real^(N,1)finite_sum->real) m z)) continuous_on om) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((A0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om) /\
    (\z. lift((rho0:real^(N,1)finite_sum->real) z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bw_coeff om (A0:real^(N,1)finite_sum->real^N^N) rho0` THEN
    UNDISCH_TAC `!m. p2bw_coeff om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m)` THEN
    REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `l:num->real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`] P2BW_LOCALIZE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[p2bw_unilip]
        (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`)) THEN MESON_TAC[];
      MP_TAC(REWRITE_RULE[p2bw_locunif]
        (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)) THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `lg:num->real^(N,1)finite_sum->real`
    (X_CHOOSE_THEN `lg0:real^(N,1)finite_sum->real` (X_CHOOSE_THEN `L:real`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(!m x. x IN {x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}
           ==> (lg:num->real^(N,1)finite_sum->real) m x = l m x) /\
    (!x. x IN {x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}
         ==> (lg0:real^(N,1)finite_sum->real) x = l0 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bp:real`) THEN
  SUBGOAL_THEN
   `&0 <= L + abs Bp /\
    (!m x y. abs((lg:num->real^(N,1)finite_sum->real) m x - lg m y) <=
             (L + abs Bp) * norm(x - y)) /\
    (!x y. abs((lg0:real^(N,1)finite_sum->real) x - lg0 y) <= (L + abs Bp) * norm(x - y)) /\
    (!x y. abs((phi:real^(N,1)finite_sum->real) x - phi y) <= (L + abs Bp) * norm(x - y))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Bp * norm(x - y:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^(N,1)finite_sum->real) x)) continuous_on k /\
    (!m. (\x. lift((rho:num->real^(N,1)finite_sum->real) m x)) continuous_on k) /\
    (\x. lift((rho0:real^(N,1)finite_sum->real) x)) continuous_on k /\
    (!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\x. lift((A:num->real^(N,1)finite_sum->real^N^N) m x$i$j)) continuous_on k) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\x. lift((A0:real^(N,1)finite_sum->real^N^N) x$i$j)) continuous_on k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
     [EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->real^(N,1)finite_sum->real^N^N`; `A0:real^(N,1)finite_sum->real^N^N`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED_M) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif_m; p2bw_locunif]
      (ASSUME `p2bw_locunif_m om (A:num->real^(N,1)finite_sum->real^N^N) A0`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e:real`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `BA:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`rho:num->real^(N,1)finite_sum->real`; `rho0:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[p2bw_locunif]
      (ASSUME `p2bw_locunif om (rho:num->real^(N,1)finite_sum->real) rho0`)) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Brho:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bphi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. abs((phi:real^(N,1)finite_sum->real) x) <= Bphi` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(N,1)finite_sum` THEN ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN k` THEN
    ASM_SIMP_TAC[REAL_ABS_NUM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the time-derivative term *)
    SUBGOAL_THEN
     `!m. integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                                wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                                (rho:num->real^(N,1)finite_sum->real) m z)) =
          integral (:real^(N,1)finite_sum)
            (\z. lift(drop(frechet_derivative (\y. lift((lg:num->real^(N,1)finite_sum->real) m y))
                             (at z) (pastecart (vec 0:real^N) (lift(&1)))) *
                      ((if z IN k then phi z * rho m z else &0) * &1)))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN
       `(\z. lift((phi:real^(N,1)finite_sum->real) z *
                  wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                  (rho:num->real^(N,1)finite_sum->real) m z)) =
        (\z. lift((phi z * rho m z) *
                  drop(frechet_derivative (\w. lift(l m w)) (at z)
                         (pastecart (vec 0:real^N) (lift(&1))))))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; wan_tder] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC P2BW_LOCGLOB_D THEN
      EXISTS_TAC `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}` THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                            wan_tder (l0:real^(N,1)finite_sum->real) z *
                            (rho0:real^(N,1)finite_sum->real) z)) =
      integral (:real^(N,1)finite_sum)
        (\z. lift(drop(frechet_derivative (\y. lift((lg0:real^(N,1)finite_sum->real) y))
                         (at z) (pastecart (vec 0:real^N) (lift(&1)))) *
                  ((if z IN k then phi z * rho0 z else &0) * &1)))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `(\z. lift((phi:real^(N,1)finite_sum->real) z *
                  wan_tder (l0:real^(N,1)finite_sum->real) z *
                  (rho0:real^(N,1)finite_sum->real) z)) =
        (\z. lift((phi z * rho0 z) *
                  drop(frechet_derivative (\w. lift(l0 w)) (at z)
                         (pastecart (vec 0:real^N) (lift(&1))))))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; wan_tder] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC P2BW_LOCGLOB_D THEN
      EXISTS_TAC `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}` THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lg:num->real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`;
                   `L + abs Bp`;
                   `\m x. if x IN k then (phi:real^(N,1)finite_sum->real) x *
                                         (rho:num->real^(N,1)finite_sum->real) m x
                          else &0`;
                   `\x. if x IN k then (phi:real^(N,1)finite_sum->real) x *
                                       (rho0:real^(N,1)finite_sum->real) x
                        else &0`;
                   `\x:real^(N,1)finite_sum. &1`; `&1`; `Bphi * Brho`;
                   `k:real^(N,1)finite_sum->bool`;
                   `{x + y:real^(N,1)finite_sum | x IN k /\ y IN cball(vec 0,d)}`; `d:real`;
                   `pastecart (vec 0:real^N) (lift(&1))`] P2BW_WEAK_PRODUCT_CONV) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET_REFL];
      ASM_REWRITE_TAC[];
      SIMP_TAC[];
      SIMP_TAC[];
      GEN_TAC THEN MATCH_MP_TAC P2BW_CUT_MEAS THEN ASM_SIMP_TAC[P2BW_CONT_PROD];
      MATCH_MP_TAC P2BW_CUT_MEAS THEN ASM_SIMP_TAC[P2BW_CONT_PROD];
      REPEAT GEN_TAC THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC P2BW_ABS_MUL_LE THEN ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`k:real^(N,1)finite_sum->bool`; `e / (Bphi + &1)`]
        (REWRITE_RULE[p2bw_locunif]
           (ASSUME `p2bw_locunif om (rho:num->real^(N,1)finite_sum->real) rho0`))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NR")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`] THEN DISCH_TAC THEN
      COND_CASES_TAC THENL
       [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN MATCH_MP_TAC P2BW_ARITH_DIV THEN
        MAP_EVERY EXISTS_TAC
         [`Bphi:real`;
          `abs((rho:num->real^(N,1)finite_sum->real) m x - (rho0:real^(N,1)finite_sum->real) x)`] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_ABS_POS];
          USE_THEN "NR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_ABS_POS]];
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]];
      REWRITE_TAC[MEASURABLE_ON_CONST];
      REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL]];
    (* the bilinear term with the test function *)
    SUBGOAL_THEN
     `!m. (!x i j. ~(x IN k)
                   ==> (if x IN k then (A:num->real^(N,1)finite_sum->real^N^N) m x
                        else mat 0)$i$j = &0) /\
          (!i j. (\x. lift((if x IN k then A m x else mat 0)$i$j))
                 measurable_on (:real^(N,1)finite_sum)) /\
          (!x i j. abs((if x IN k then A m x else mat 0)$i$j) <= BA)`
    (LABEL_TAC "WA") THENL
     [X_GEN_TAC `m:num` THEN
      MP_TAC(ISPECL [`(A:num->real^(N,1)finite_sum->real^N^N) m`;
                     `k:real^(N,1)finite_sum->bool`; `BA:real`] P2BW_CUT_MAT) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!x i j. ~(x IN k)
               ==> (if x IN k then (A0:real^(N,1)finite_sum->real^N^N) x else mat 0)$i$j = &0) /\
      (!i j. (\x. lift((if x IN k then A0 x else mat 0)$i$j))
             measurable_on (:real^(N,1)finite_sum)) /\
      (!x i j. abs((if x IN k then A0 x else mat 0)$i$j) <= BA)`
    (LABEL_TAC "WA0") THENL
     [MP_TAC(ISPECL [`A0:real^(N,1)finite_sum->real^N^N`;
                     `k:real^(N,1)finite_sum->bool`; `BA:real`] P2BW_CUT_MAT) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m. integral om (\z. lift(p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m)
                                         ((l:num->real^(N,1)finite_sum->real) m)
                                         (phi:real^(N,1)finite_sum->real) z)) =
          integral (:real^(N,1)finite_sum)
            (\z. lift(p2bw_bil (\x. if x IN k then A m x else mat 0)
                               ((lg:num->real^(N,1)finite_sum->real) m) phi z))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(BETA_RULE(ISPECL
        [`om:real^(N,1)finite_sum->bool`;
         `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}`;
         `k:real^(N,1)finite_sum->bool`; `(A:num->real^(N,1)finite_sum->real^N^N) m`;
         `\z:real^(N,1)finite_sum. &1`; `(l:num->real^(N,1)finite_sum->real) m`;
         `phi:real^(N,1)finite_sum->real`; `(lg:num->real^(N,1)finite_sum->real) m`;
         `phi:real^(N,1)finite_sum->real`] P2BW_LOCGLOB)) THEN
      REWRITE_TAC[REAL_MUL_LID; MATRIX_CMUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_BIL_TEST_ZERO THEN
      MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integral om (\z. lift(p2bw_bil (A0:real^(N,1)finite_sum->real^N^N)
                                     (l0:real^(N,1)finite_sum->real)
                                     (phi:real^(N,1)finite_sum->real) z)) =
      integral (:real^(N,1)finite_sum)
        (\z. lift(p2bw_bil (\x. if x IN k then A0 x else mat 0)
                           (lg0:real^(N,1)finite_sum->real) phi z))`
    SUBST1_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
        [`om:real^(N,1)finite_sum->bool`;
         `{x + y:real^(N,1)finite_sum | x IN k /\ y IN ball(vec 0,d)}`;
         `k:real^(N,1)finite_sum->bool`; `A0:real^(N,1)finite_sum->real^N^N`;
         `\z:real^(N,1)finite_sum. &1`; `l0:real^(N,1)finite_sum->real`;
         `phi:real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`;
         `phi:real^(N,1)finite_sum->real`] P2BW_LOCGLOB)) THEN
      REWRITE_TAC[REAL_MUL_LID; MATRIX_CMUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_BIL_TEST_ZERO THEN
      MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lg:num->real^(N,1)finite_sum->real`; `lg0:real^(N,1)finite_sum->real`;
                   `phi:real^(N,1)finite_sum->real`; `L + abs Bp`;
                   `\m x. if x IN k then (A:num->real^(N,1)finite_sum->real^N^N) m x else mat 0`;
                   `\x. if x IN k then (A0:real^(N,1)finite_sum->real^N^N) x else mat 0`;
                   `BA:real`; `k:real^(N,1)finite_sum->bool`;
                   `{x + y:real^(N,1)finite_sum | x IN k /\ y IN cball(vec 0,d)}`; `d:real`]
                  P2BW_BIL_CONV) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET_REFL];
      ASM_REWRITE_TAC[];
      USE_THEN "WA" (fun th -> REWRITE_TAC[th]);
      USE_THEN "WA0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "WA" (fun th -> REWRITE_TAC[th]);
      USE_THEN "WA0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "WA" (fun th -> REWRITE_TAC[th]);
      USE_THEN "WA0" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`A:num->real^(N,1)finite_sum->real^N^N`; `A0:real^(N,1)finite_sum->real^N^N`;
                     `k:real^(N,1)finite_sum->bool`] P2BW_UNIF_M_ALL) THEN
      ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC(REWRITE_RULE[p2bw_locunif_m; p2bw_locunif]
          (ASSUME `p2bw_locunif_m om (A:num->real^(N,1)finite_sum->real^N^N) A0`)) THEN
        DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`k:real^(N,1)finite_sum->bool`; `e':real`]) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NA")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `x:real^(N,1)finite_sum`; `i:num`; `j:num`] THEN
      DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
       [USE_THEN "NA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[MAT_0_COMPONENT; REAL_SUB_REFL; REAL_ABS_NUM]]]]);;

(* s7: MT Lemma 9.23 (p2bw_t1 passes to the limit). *)

let P2BW_CONT_NTAU = prove
 (`!(om:real^(N,1)finite_sum->bool) c.
     (!z. z IN om ==> &0 < drop(sndcart z))
     ==> (\z. lift(c / (&2 * drop(sndcart z)))) continuous_on om`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV]);;

let P2BW_CONT_T1COEFF = prove
 (`!(om:real^(N,1)finite_sum->bool) rho R.
     (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om
     ==> (\z. lift((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z)) continuous_on om`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  ASM_SIMP_TAC[P2BW_CONT_NTAU]);;

let P2BW_T1_PIECES_INT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l phi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_test om phi
     ==> (\z. lift((phi:real^(N,1)finite_sum->real) z * wan_tder l z * rho z)) integrable_on om /\
    (\z. lift(phi z * p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z)) integrable_on om /\
    (\z. lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                        (R:real^(N,1)finite_sum->real) z) * rho z))) integrable_on om /\
    (\z. lift(p2bw_bil A l phi z)) integrable_on om`,
  REPEAT STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `\z. wan_tder (l:real^(N,1)finite_sum->real) z *
                          (rho:real^(N,1)finite_sum->real) z`;
                     `vec 0:real^(N,1)finite_sum`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[ETA_AX]];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l`;
                     `vec 0:real^(N,1)finite_sum`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `\z. (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                           (R:real^(N,1)finite_sum->real) z) * (rho:real^(N,1)finite_sum->real) z`;
                     `vec 0:real^(N,1)finite_sum`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN MATCH_MP_TAC P2BW_CONT_T1COEFF THEN
      ASM_REWRITE_TAC[];
      MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                               `l:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`;
                               `\z:real^(N,1)finite_sum. &1`] P2BW_BIL_TEST_INT)) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_CONT THEN REWRITE_TAC[CONTINUOUS_ON_CONST]]);;

let P2BW_T1_SPLIT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l phi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_test om phi
     ==> integral om (\z. lift(phi z * (wan_tder l z * rho z + p2bw_bil A l l z +
                                          (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) *
                                          rho z) +
                                p2bw_bil A l phi z)) =
         integral om (\z. lift(phi z * wan_tder l z * rho z)) +
         integral om (\z. lift(phi z * p2bw_bil A l l z)) +
         integral om (\z. lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) *
                                        rho z))) +
         integral om (\z. lift(p2bw_bil A l phi z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2BW_T1_PIECES_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^(N,1)finite_sum->real) z *
              (wan_tder l z * rho z + p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z +
               (&(dimindex(:N)) / (&2 * drop(sndcart z)) - (R:real^(N,1)finite_sum->real) z) *
               rho z) +
              p2bw_bil A l phi z)) =
    (\z. lift(phi z * wan_tder l z * rho z) +
         (lift(phi z * p2bw_bil A l l z) +
          (lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z)) +
           lift(p2bw_bil A l phi z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_ADD]]);;

let P2BW_T1_LIMIT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:num->real^(N,1)finite_sum->real^N^N) rho R l
    (A0:real^(N,1)finite_sum->real^N^N) rho0 R0 l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!m. p2bw_coeff om (A m) (rho m) /\ (\z. lift(R m z)) continuous_on om) /\
     p2bw_coeff om A0 rho0 /\ (\z. lift(R0 z)) continuous_on om /\
     p2bw_locunif_m om A A0 /\ p2bw_locunif om rho rho0 /\ p2bw_locunif om R R0 /\
     p2bw_unilip om l /\ p2bw_locunif om l l0 /\
     (!m. p2bw_t1 om (A m) (rho m) (R m) (l m) /\ p2bw_t2 om (A m) (rho m) (R m) (l m))
     ==> p2bw_t1 om A0 rho0 R0 l0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_t1] THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BW_LIMIT_LOCLIP
    (CONJ (REWRITE_RULE[p2bw_unilip]
             (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`))
          (REWRITE_RULE[p2bw_locunif]
             (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\z. lift((A:num->real^(N,1)finite_sum->real^N^N) m z$i$j)) continuous_on om) /\
    (!m. (\z. lift((rho:num->real^(N,1)finite_sum->real) m z)) continuous_on om) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((A0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om) /\
    (\z. lift((rho0:real^(N,1)finite_sum->real) z)) continuous_on om /\
    (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A0 z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bw_coeff om (A0:real^(N,1)finite_sum->real^N^N) rho0` THEN
    UNDISCH_TAC `!m. p2bw_coeff om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m) /\
                     (\z. lift((R:num->real^(N,1)finite_sum->real) m z)) continuous_on om` THEN
    REWRITE_TAC[p2bw_coeff] THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                 `rho:num->real^(N,1)finite_sum->real`; `l:num->real^(N,1)finite_sum->real`;
                 `A0:real^(N,1)finite_sum->real^N^N`; `rho0:real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2BW_DERIV_PIECES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                 `rho:num->real^(N,1)finite_sum->real`; `R:num->real^(N,1)finite_sum->real`;
                 `l:num->real^(N,1)finite_sum->real`; `A0:real^(N,1)finite_sum->real^N^N`;
                 `rho0:real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2BW_ENERGY_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `\m z. (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                         (R:num->real^(N,1)finite_sum->real) m z) *
                        (rho:num->real^(N,1)finite_sum->real) m z`;
                 `\z. (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                       (R0:real^(N,1)finite_sum->real) z) * (rho0:real^(N,1)finite_sum->real) z`]
                P2BW_CONT_TERM_LIMIT_OM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BW_CONT_T1COEFF THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BW_CONT_T1COEFF THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\m z. &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                            (R:num->real^(N,1)finite_sum->real) m z`;
                     `\z. &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                          (R0:real^(N,1)finite_sum->real) z`;
                     `rho:num->real^(N,1)finite_sum->real`; `rho0:real^(N,1)finite_sum->real`]
                    P2BW_LOCUNIF_MUL) THEN
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        ASM_SIMP_TAC[P2BW_CONT_NTAU];
        MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                       `\m:num (z:real^(N,1)finite_sum). &(dimindex(:N)) / (&2 * drop(sndcart z))`;
                       `\z:real^(N,1)finite_sum. &(dimindex(:N)) / (&2 * drop(sndcart z))`;
                       `R:num->real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`]
                      P2BW_LOCUNIF_SUB) THEN
        REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                       `\z:real^(N,1)finite_sum. &(dimindex(:N)) / (&2 * drop(sndcart z))`]
                      P2BW_LOCUNIF_CONSTFN) THEN
        REWRITE_TAC[]]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!m. integral om
          (\z. lift((phi:real^(N,1)finite_sum->real) z *
                    (wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                     (rho:num->real^(N,1)finite_sum->real) m z +
                     p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m) (l m) (l m) z +
                     (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                      (R:num->real^(N,1)finite_sum->real) m z) * rho m z) +
                    p2bw_bil (A m) (l m) phi z)) =
        integral om (\z. lift(phi z * wan_tder (l m) z * rho m z)) +
        integral om (\z. lift(phi z * p2bw_bil (A m) (l m) (l m) z)) +
        integral om (\z. lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R m z) *
                                       rho m z))) +
        integral om (\z. lift(p2bw_bil (A m) (l m) phi z))`
  (LABEL_TAC "SPm") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BW_T1_SPLIT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral om
      (\z. lift((phi:real^(N,1)finite_sum->real) z *
                (wan_tder (l0:real^(N,1)finite_sum->real) z * (rho0:real^(N,1)finite_sum->real) z +
                 p2bw_bil (A0:real^(N,1)finite_sum->real^N^N) l0 l0 z +
                 (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                  (R0:real^(N,1)finite_sum->real) z) * rho0 z) +
                p2bw_bil A0 l0 phi z)) =
    integral om (\z. lift(phi z * wan_tder l0 z * rho0 z)) +
    integral om (\z. lift(phi z * p2bw_bil A0 l0 l0 z)) +
    integral om (\z. lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R0 z) *
                                   rho0 z))) +
    integral om (\z. lift(p2bw_bil A0 l0 phi z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BW_T1_SPLIT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
  EXISTS_TAC
   `\m. integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                              wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                              (rho:num->real^(N,1)finite_sum->real) m z)) +
        integral om (\z. lift(phi z * p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m)
                                               (l m) (l m) z)) +
        integral om (\z. lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                                        (R:num->real^(N,1)finite_sum->real) m z) *
                                       rho m z))) +
        integral om (\z. lift(p2bw_bil (A m) (l m) phi z))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
    USE_THEN "SPm" (fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `!m. p2bw_t1 om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m) (R m) (l m) /\
                     p2bw_t2 om (A m) (rho m) (R m) (l m)` THEN
    REWRITE_TAC[p2bw_t1] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `m:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real`) THEN ASM_REWRITE_TAC[]]);;

(* s8: the limit of the weak identity (MT Section 2.6: Cor 6.51 for l_n *)
(* passes to l0 against nonnegative tests). *)

let P2BW_CONT_FC = prove
 (`!(om:real^(N,1)finite_sum->bool) rho R l.
     (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     (\z. lift(l z)) continuous_on om
     ==> (\z. lift((R z * rho z - l z * (inv(drop(sndcart z)) * rho z)) * inv(&2)))
           continuous_on om`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_CONT_PROD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV] THEN
  MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV]);;

let P2BW_LOCUNIF_FC = prove
 (`!(om:real^(N,1)finite_sum->bool) rho rho0 R R0 l l0.
     (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!m. (\z. lift(rho m z)) continuous_on om) /\ (\z. lift(rho0 z)) continuous_on om /\
     (!m. (\z. lift(R m z)) continuous_on om) /\ (!m. (\z. lift(l m z)) continuous_on om) /\
     p2bw_locunif om rho rho0 /\ p2bw_locunif om R R0 /\ p2bw_locunif om l l0
     ==> p2bw_locunif om
           (\m z. (R m z * rho m z - l m z * (inv(drop(sndcart z)) * rho m z)) * inv(&2))
           (\z. (R0 z * rho0 z - l0 z * (inv(drop(sndcart z)) * rho0 z)) * inv(&2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p2bw_locunif om (\m z. inv(drop(sndcart z)) * (rho:num->real^(N,1)finite_sum->real) m z)
                    (\z. inv(drop(sndcart z)) * (rho0:real^(N,1)finite_sum->real) z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\m:num (z:real^(N,1)finite_sum). inv(drop(sndcart z))`;
                   `\z:real^(N,1)finite_sum. inv(drop(sndcart z))`;
                   `rho:num->real^(N,1)finite_sum->real`; `rho0:real^(N,1)finite_sum->real`]
                  P2BW_LOCUNIF_MUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z:real^(N,1)finite_sum. inv(drop(sndcart z))`] P2BW_LOCUNIF_CONSTFN) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_locunif om
      (\m z. (R:num->real^(N,1)finite_sum->real) m z * (rho:num->real^(N,1)finite_sum->real) m z -
             (l:num->real^(N,1)finite_sum->real) m z * (inv(drop(sndcart z)) * rho m z))
      (\z. (R0:real^(N,1)finite_sum->real) z * (rho0:real^(N,1)finite_sum->real) z -
           (l0:real^(N,1)finite_sum->real) z * (inv(drop(sndcart z)) * rho0 z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\m z. (R:num->real^(N,1)finite_sum->real) m z *
                          (rho:num->real^(N,1)finite_sum->real) m z`;
                   `\z. (R0:real^(N,1)finite_sum->real) z * (rho0:real^(N,1)finite_sum->real) z`;
                   `\m z. (l:num->real^(N,1)finite_sum->real) m z *
                          (inv(drop(sndcart z)) * (rho:num->real^(N,1)finite_sum->real) m z)`;
                   `\z. (l0:real^(N,1)finite_sum->real) z *
                        (inv(drop(sndcart z)) * (rho0:real^(N,1)finite_sum->real) z)`]
                  P2BW_LOCUNIF_SUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `R:num->real^(N,1)finite_sum->real`;
                     `R0:real^(N,1)finite_sum->real`; `rho:num->real^(N,1)finite_sum->real`;
                     `rho0:real^(N,1)finite_sum->real`] P2BW_LOCUNIF_MUL) THEN
      ASM_REWRITE_TAC[ETA_AX];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `l:num->real^(N,1)finite_sum->real`;
                     `l0:real^(N,1)finite_sum->real`;
                     `\m z. inv(drop(sndcart z)) * (rho:num->real^(N,1)finite_sum->real) m z`;
                     `\z. inv(drop(sndcart z)) * (rho0:real^(N,1)finite_sum->real) z`]
                    P2BW_LOCUNIF_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                 `\m z. (R:num->real^(N,1)finite_sum->real) m z *
                        (rho:num->real^(N,1)finite_sum->real) m z -
                        (l:num->real^(N,1)finite_sum->real) m z * (inv(drop(sndcart z)) * rho m z)`;
                 `\z. (R0:real^(N,1)finite_sum->real) z * (rho0:real^(N,1)finite_sum->real) z -
                      (l0:real^(N,1)finite_sum->real) z * (inv(drop(sndcart z)) * rho0 z)`;
                 `\m:num (z:real^(N,1)finite_sum). inv(&2)`; `\z:real^(N,1)finite_sum. inv(&2)`]
                P2BW_LOCUNIF_MUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV] THEN
    MATCH_MP_TAC P2BW_CONT_PROD THEN ASM_SIMP_TAC[P2BW_CONT_TAU_INV];
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. inv(&2)`]
                  P2BW_LOCUNIF_CONSTFN) THEN
    REWRITE_TAC[]]);;

let P2BW_TID_STEP = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l phi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_test om phi
     ==> integral om (\z. lift(phi z * ((R z * rho z - p2bw_bil A l l z) / &2 -
                                        l z / (&2 * drop(sndcart z)) * rho z))) =
         integral om (\z. lift(phi z * ((R z * rho z - l z * (inv(drop(sndcart z)) * rho z)) *
                                        inv(&2)))) +
         --(inv(&2)) % integral om (\z. lift(phi z * p2bw_bil A l l z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^(N,1)finite_sum->real) z *
              (((R:real^(N,1)finite_sum->real) z * rho z -
                l z * (inv(drop(sndcart z)) * rho z)) * inv(&2)))) integrable_on om /\
    (\z. lift(phi z * p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z)) integrable_on om`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `\z. ((R:real^(N,1)finite_sum->real) z * (rho:real^(N,1)finite_sum->real) z -
                           (l:real^(N,1)finite_sum->real) z * (inv(drop(sndcart z)) * rho z)) *
                          inv(&2)`;
                     `vec 0:real^(N,1)finite_sum`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN MATCH_MP_TAC P2BW_CONT_FC THEN
      ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX];
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l`;
                     `vec 0:real^(N,1)finite_sum`] P2BW_LEBM_TEST_INT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^(N,1)finite_sum->real) z *
              (((R:real^(N,1)finite_sum->real) z * rho z -
                p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) / &2 -
               l z / (&2 * drop(sndcart z)) * rho z))) =
    (\z. lift(phi z * ((R z * rho z - l z * (inv(drop(sndcart z)) * rho z)) * inv(&2))) +
         --(inv(&2)) % lift(phi z * p2bw_bil A l l z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL]]);;

let P2BW_TID_LIMIT = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:num->real^(N,1)finite_sum->real^N^N) rho R l
    (A0:real^(N,1)finite_sum->real^N^N) rho0 R0 l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!m. p2bw_coeff om (A m) (rho m) /\ (\z. lift(R m z)) continuous_on om) /\
     p2bw_coeff om A0 rho0 /\ (\z. lift(R0 z)) continuous_on om /\
     p2bw_locunif_m om A A0 /\ p2bw_locunif om rho rho0 /\ p2bw_locunif om R R0 /\
     p2bw_unilip om l /\ p2bw_locunif om l l0 /\
     (!m. p2bw_t2 om (A m) (rho m) (R m) (l m) /\ p2bw_tid om (A m) (rho m) (R m) (l m))
     ==> !phi. wan_test om phi /\ (!z. &0 <= phi z)
               ==> integral om (\z. lift(phi z * wan_tder l0 z * rho0 z)) =
                   integral om (\z. lift(phi z * ((R0 z * rho0 z - p2bw_bil A0 l0 l0 z) / &2 -
                                                  l0 z / (&2 * drop(sndcart z)) * rho0 z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BW_LIMIT_LOCLIP
    (CONJ (REWRITE_RULE[p2bw_unilip]
             (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`))
          (REWRITE_RULE[p2bw_locunif]
             (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (\z. lift((A:num->real^(N,1)finite_sum->real^N^N) m z$i$j)) continuous_on om) /\
    (!m. (\z. lift((rho:num->real^(N,1)finite_sum->real) m z)) continuous_on om) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((A0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om) /\
    (\z. lift((rho0:real^(N,1)finite_sum->real) z)) continuous_on om /\
    (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A0 z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bw_coeff om (A0:real^(N,1)finite_sum->real^N^N) rho0` THEN
    UNDISCH_TAC `!m. p2bw_coeff om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m) /\
                     (\z. lift((R:num->real^(N,1)finite_sum->real) m z)) continuous_on om` THEN
    REWRITE_TAC[p2bw_coeff] THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m. (\z. lift((l:num->real^(N,1)finite_sum->real) m z)) continuous_on om) /\
    (\z. lift((l0:real^(N,1)finite_sum->real) z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                 `rho:num->real^(N,1)finite_sum->real`; `l:num->real^(N,1)finite_sum->real`;
                 `A0:real^(N,1)finite_sum->real^N^N`; `rho0:real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2BW_DERIV_PIECES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "P1" o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                 `rho:num->real^(N,1)finite_sum->real`; `R:num->real^(N,1)finite_sum->real`;
                 `l:num->real^(N,1)finite_sum->real`; `A0:real^(N,1)finite_sum->real^N^N`;
                 `rho0:real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2BW_ENERGY_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "EN")] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `\m z. ((R:num->real^(N,1)finite_sum->real) m z *
                         (rho:num->real^(N,1)finite_sum->real) m z -
                         (l:num->real^(N,1)finite_sum->real) m z *
                         (inv(drop(sndcart z)) * rho m z)) * inv(&2)`;
                 `\z. ((R0:real^(N,1)finite_sum->real) z * (rho0:real^(N,1)finite_sum->real) z -
                       (l0:real^(N,1)finite_sum->real) z * (inv(drop(sndcart z)) * rho0 z)) *
                      inv(&2)`]
                P2BW_CONT_TERM_LIMIT_OM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BW_CONT_FC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BW_CONT_FC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BW_LOCUNIF_FC THEN ASM_SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "FC")] THEN
  SUBGOAL_THEN
   `!m. integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                              wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                              (rho:num->real^(N,1)finite_sum->real) m z)) =
        integral om (\z. lift(phi z * (((R:num->real^(N,1)finite_sum->real) m z * rho m z -
                                        l m z * (inv(drop(sndcart z)) * rho m z)) * inv(&2)))) +
        --(inv(&2)) % integral om (\z. lift(phi z *
                                            p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m)
                                                     (l m) (l m) z))`
  (LABEL_TAC "IDm") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `(A:num->real^(N,1)finite_sum->real^N^N) m`;
                   `(rho:num->real^(N,1)finite_sum->real) m`;
                   `(R:num->real^(N,1)finite_sum->real) m`;
                   `(l:num->real^(N,1)finite_sum->real) m`; `phi:real^(N,1)finite_sum->real`]
                  P2BW_TID_STEP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{z | z IN om /\
                     ~(wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                       (rho:num->real^(N,1)finite_sum->real) m z =
                       ((R:num->real^(N,1)finite_sum->real) m z * rho m z -
                        p2bw_bil ((A:num->real^(N,1)finite_sum->real^N^N) m) (l m) (l m) z) / &2 -
                       l m z / (&2 * drop(sndcart z)) * rho m z)}` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `m:num` (ASSUME
        `!m. p2bw_t2 om ((A:num->real^(N,1)finite_sum->real^N^N) m) (rho m) (R m) (l m) /\
             p2bw_tid om (A m) (rho m) (R m) (l m)`)) THEN
      REWRITE_TAC[p2bw_tid] THEN SIMP_TAC[];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A0:real^(N,1)finite_sum->real^N^N`;
                 `rho0:real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`;
                 `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2BW_TID_STEP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\m. integral om (\z. lift((phi:real^(N,1)finite_sum->real) z *
                                        wan_tder ((l:num->real^(N,1)finite_sum->real) m) z *
                                        (rho:num->real^(N,1)finite_sum->real) m z))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [USE_THEN "P1" ACCEPT_TAC;
    USE_THEN "IDm" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [USE_THEN "FC" ACCEPT_TAC;
      MATCH_MP_TAC LIM_CMUL THEN USE_THEN "EN" ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* MT Cor 9.24 (P2BW_CSUB_FROM_T1: U = p2bw_uof l0 is a weak               *)
(* subsolution of the conjugate heat equation, from t1 for l0 by the       *)
(* Lipschitz-test extension P2BW_BILFORM_LIP with the test U psi), its      *)
(* tools (P2BW_UOF_DERIV, P2BW_UOF_LOCLIP, P2BW_CSUB_POINT), and the        *)
(* main theorem P2BW_LIMIT.                                                  *)
(* ------------------------------------------------------------------------- *)

(* s9: MT Cor 9.24: U = tau^(-n/2) e^(-l0) is a weak subsolution of the   *)
(* conjugate heat equation (p2bw_csub), from p2bw_t1 for l0. *)

let P2BW_EXP_LIP = prove
 (`!M x y. abs x <= M /\ abs y <= M ==> abs(exp x - exp y) <= exp M * abs(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`M:real`; `Cx x`; `Cx y`] CEXP_LIPSCHITZ_BOUNDED) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_EXP; GSYM CX_SUB]);;

let P2BW_LOG_DIFF = prove
 (`!a b. &0 < a /\ a <= b ==> &0 <= log b - log a /\ log b - log a <= inv a * (b - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log b - log a = log(&1 + inv a * (b - a))` SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 + inv a * (b - a) = b / a` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[LOG_DIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv a * (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_LE] THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC);;

let P2BW_LOG_LIP = prove
 (`!a b B. &0 < a /\ &0 < b /\ inv a <= B /\ inv b <= B
           ==> abs(log a - log b) <= B * abs(a - b)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
   [MP_TAC(SPECL [`a:real`; `b:real`] P2BW_LOG_DIFF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv a * (b - a)` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `abs(a - b) = b - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`b:real`; `a:real`] P2BW_LOG_DIFF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv b * (a - b)` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `abs(a - b) = a - b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]);;

let P2BW_LOGTAU_DERIV = prove
 (`!z:real^(N,1)finite_sum.
     &0 < drop(sndcart z)
     ==> ((\y. lift(log(drop(sndcart y)))) has_derivative
          (\v. inv(drop(sndcart z)) % sndcart v)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^(N,1)finite_sum. lift(log(drop(sndcart y)))) =
                (lift o log o drop) o (\y. sndcart y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\v:real^(N,1)finite_sum. inv(drop(sndcart(z:real^(N,1)finite_sum))) % sndcart v) =
                (\x. inv(drop(sndcart z)) % x) o (\v. sndcart v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[ETA_AX; LINEAR_SNDCART];
    MP_TAC(SPEC `drop(sndcart(z:real^(N,1)finite_sum))` HAS_REAL_DERIVATIVE_LOG) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP]]);;

let P2BW_UOF_DERIV = prove
 (`!(l0:real^(N,1)finite_sum->real) z.
     &0 < drop(sndcart z) /\ (\w. lift(l0 w)) differentiable at z
     ==> (\w. lift(p2bw_uof l0 w)) differentiable at z /\
         !v. drop(frechet_derivative (\w. lift(p2bw_uof l0 w)) (at z) v) =
             --(p2bw_uof l0 z) *
             (drop(frechet_derivative (\w. lift(l0 w)) (at z) v) +
              &(dimindex(:N)) / &2 * inv(drop(sndcart z)) * drop(sndcart v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\w. lift(p2bw_uof (l0:real^(N,1)finite_sum->real) w)) has_derivative
     (\v. exp(--(l0 z + &(dimindex(:N)) / &2 * log(drop(sndcart z)))) %
          --(frechet_derivative (\w. lift(l0 w)) (at z) v +
             &(dimindex(:N)) / &2 % (inv(drop(sndcart z)) % sndcart v)))) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift(p2bw_uof (l0:real^(N,1)finite_sum->real) w)) =
      (lift o exp o drop) o
      (\w. --(lift(l0 w) + &(dimindex(:N)) / &2 % lift(log(drop(sndcart w)))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bw_uof; GSYM LIFT_CMUL; GSYM LIFT_ADD; GSYM LIFT_NEG;
                  LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. exp(--((l0:real^(N,1)finite_sum->real) z +
                  &(dimindex(:N)) / &2 * log(drop(sndcart z)))) %
           --(frechet_derivative (\w. lift(l0 w)) (at z) v +
              &(dimindex(:N)) / &2 % (inv(drop(sndcart z)) % sndcart v))) =
      (\x. exp(--(l0 z + &(dimindex(:N)) / &2 * log(drop(sndcart z)))) % x) o
      (\v. --(frechet_derivative (\w. lift(l0 w)) (at z) v +
              &(dimindex(:N)) / &2 % (inv(drop(sndcart z)) % sndcart v)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC P2BW_LOGTAU_DERIV THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[] THEN
      MP_TAC(SPEC `--((l0:real^(N,1)finite_sum->real) z +
                      &(dimindex(:N)) / &2 * log(drop(sndcart z)))` HAS_REAL_DERIVATIVE_EXP) THEN
      REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_NEG; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  X_GEN_TAC `v:real^(N,1)finite_sum` THEN
  REWRITE_TAC[DROP_CMUL; DROP_NEG; DROP_ADD; p2bw_uof] THEN REAL_ARITH_TAC);;

let P2BW_UOF_POS = prove
 (`!(l0:real^(N,1)finite_sum->real) z. &0 < p2bw_uof l0 z`,
  REWRITE_TAC[p2bw_uof; REAL_EXP_POS_LT]);;

let P2BW_UOF_LOCLIP = prove
 (`!(om:real^(N,1)finite_sum->bool) l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\ wan_loclip om l0
     ==> wan_loclip om (p2bw_uof l0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_loclip] THEN
  X_GEN_TAC `k:real^(N,1)finite_sum->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:real^(N,1)finite_sum->bool` o GEN_REWRITE_RULE I [wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `L0:real` (LABEL_TAC "L0")) THEN
  SUBGOAL_THEN
   `(\x. lift((l0:real^(N,1)finite_sum->real) x)) continuous_on k /\
    (\x. lift(inv(drop(sndcart x)))) continuous_on k /\
    (\x:real^(N,1)finite_sum. lift(log(drop(sndcart x)))) continuous_on k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
      ASM_SIMP_TAC[P2BW_CONT_TAU_INV];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\v:real^(N,1)finite_sum. inv(drop(sndcart(x:real^(N,1)finite_sum))) % sndcart v` THEN
      MATCH_MP_TAC P2BW_LOGTAU_DERIV THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `k:real^(N,1)finite_sum->bool`]
                P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bl:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^(N,1)finite_sum. inv(drop(sndcart x))`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bt:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^(N,1)finite_sum. log(drop(sndcart x))`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_CONT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bg:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  EXISTS_TAC `exp(Bl + &(dimindex(:N)) / &2 * Bg) * (abs L0 + &(dimindex(:N)) / &2 * Bt)` THEN
  MAP_EVERY X_GEN_TAC [`x:real^(N,1)finite_sum`; `y:real^(N,1)finite_sum`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^(N,1)finite_sum) IN om /\ (y:real^(N,1)finite_sum) IN om`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2bw_uof; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(Bl + &(dimindex(:N)) / &2 * Bg) *
              abs(--((l0:real^(N,1)finite_sum->real) x +
                     &(dimindex(:N)) / &2 * log(drop(sndcart x))) -
                  --(l0 y + &(dimindex(:N)) / &2 * log(drop(sndcart y))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_EXP_LIP THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!a b A B. abs a <= A /\ abs b <= B ==> abs(--(a + b)) <= A + B`) THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_LE_DIV; REAL_POS];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((l0:real^(N,1)finite_sum->real) x - l0 y) +
                &(dimindex(:N)) / &2 * abs(log(drop(sndcart x)) - log(drop(sndcart y)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `--(a + c * b) - --(a' + c * b') = (a' - a) + c * (b' - b)`] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b A B. abs a <= A /\ abs b <= B ==> abs(a + b) <= A + B`) THEN
      CONJ_TAC THENL
       [REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((l0:real^(N,1)finite_sum->real) x - l0 y) <= abs L0 * norm(x - y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L0 * norm(x - y:real^(N,1)finite_sum)` THEN
      CONJ_TAC THENL
       [USE_THEN "L0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(log(drop(sndcart(x:real^(N,1)finite_sum))) -
          log(drop(sndcart(y:real^(N,1)finite_sum)))) <= Bt * norm(x - y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Bt * abs(drop(sndcart(x:real^(N,1)finite_sum)) -
                           drop(sndcart(y:real^(N,1)finite_sum)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LOG_LIP THEN ASM_SIMP_TAC[] THEN CONJ_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `!a b. abs a <= b ==> a <= b`) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM DROP_SUB; GSYM SNDCART_SUB; GSYM NORM_1; NORM_SNDCART]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(abs L0 + &(dimindex(:N)) / &2 * Bt) * norm(x - y:real^(N,1)finite_sum) =
      abs L0 * norm(x - y) + &(dimindex(:N)) / &2 * (Bt * norm(x - y))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let P2BW_BIL_UOF_ID = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) l0 psi U z.
     (!i. wan_xder i U z = --(U z) * wan_xder i l0 z) /\
     (!j. wan_xder j (\y. U y * psi y) z = U z * wan_xder j psi z + psi z * wan_xder j U z)
     ==> p2bw_bil A U psi z = --(U z) * p2bw_bil A l0 psi z /\
         p2bw_bil A l0 (\y. U y * psi y) z =
         U z * p2bw_bil A l0 psi z - psi z * U z * p2bw_bil A l0 l0 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_bil] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2BW_CSUB_POINT = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) rho R l0 psi z.
     &0 < drop(sndcart z) /\ (\w. lift(l0 w)) differentiable at z /\
     (\w. lift(psi w)) differentiable at z
     ==> psi z * (wan_tder (p2bw_uof l0) z + R z * p2bw_uof l0 z) * rho z +
         p2bw_bil A (p2bw_uof l0) psi z =
         (p2bw_uof l0 z * psi z) *
         --(wan_tder l0 z * rho z + p2bw_bil A l0 l0 z +
            (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z) +
         --(&1) * p2bw_bil A l0 (\y. p2bw_uof l0 y * psi y) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UOF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^(N,1)finite_sum->real^N^N`; `l0:real^(N,1)finite_sum->real`;
                 `psi:real^(N,1)finite_sum->real`; `p2bw_uof (l0:real^(N,1)finite_sum->real)`;
                 `z:real^(N,1)finite_sum`] P2BW_BIL_UOF_ID) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[wan_xder] THENL
     [ASM_REWRITE_TAC[SNDCART_PASTECART; DROP_VEC] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`p2bw_uof (l0:real^(N,1)finite_sum->real)`; `psi:real^(N,1)finite_sum->real`;
                     `z:real^(N,1)finite_sum`; `pastecart (basis j:real^N) (vec 0:real^1)`]
                    P2BW_DER_MUL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `wan_tder (p2bw_uof (l0:real^(N,1)finite_sum->real)) z =
    --(p2bw_uof l0 z) * (wan_tder l0 z + &(dimindex(:N)) / &2 * inv(drop(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_tder] THEN ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

(* s10: Cor 9.24 from t1, and the assembly of P2BW_LIMIT. *)

let P2BW_T1_INTEGRABLE = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l phi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l /\ wan_test om phi
     ==> (\z. lift(phi z * (wan_tder l z * rho z + p2bw_bil A l l z +
                            (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z) +
                  p2bw_bil A l phi z)) integrable_on om`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL P2BW_T1_PIECES_INT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^(N,1)finite_sum->real) z *
              (wan_tder l z * rho z + p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z +
               (&(dimindex(:N)) / (&2 * drop(sndcart z)) - (R:real^(N,1)finite_sum->real) z) *
               rho z) +
              p2bw_bil A l phi z)) =
    (\z. lift(phi z * wan_tder l z * rho z) +
         (lift(phi z * p2bw_bil A l l z) +
          (lift(phi z * ((&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z)) +
           lift(p2bw_bil A l phi z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRABLE_ADD]]);;

let P2BW_BIL_ZERO_OUTSIDE = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u w k z.
     closed k /\ (!y. ~(y IN k) ==> w y = &0) /\ ~(z IN k)
     ==> p2bw_bil A u w z = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_xder j (w:real^(N,1)finite_sum->real) z = &0` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_xder] THEN
    MP_TAC(ISPECL [`\y. lift((w:real^(N,1)finite_sum->real) y)`; `k:real^(N,1)finite_sum->bool`;
                   `z:real^(N,1)finite_sum`] WAN_FRECHET_ZERO_OUTSIDE) THEN
    ASM_SIMP_TAC[LIFT_NUM; DROP_VEC];
    ASM_REWRITE_TAC[p2bw_bil; REAL_MUL_RZERO; SUM_0]]);;

let P2BW_CSUB_FROM_T1 = prove
 (`!(om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) rho R l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on om) /\
     (\z. lift(rho z)) continuous_on om /\ (\z. lift(R z)) continuous_on om /\
     wan_loclip om l0 /\ p2bw_t1 om A rho R l0
     ==> p2bw_csub om A rho R (p2bw_uof l0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`om:real^(N,1)finite_sum->bool`;
     `\z. --(wan_tder (l0:real^(N,1)finite_sum->real) z * (rho:real^(N,1)finite_sum->real) z +
             p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l0 l0 z +
             (&(dimindex(:N)) / (&2 * drop(sndcart z)) - (R:real^(N,1)finite_sum->real) z) *
             rho z)`;
     `--(&1)`; `A:real^(N,1)finite_sum->real^N^N`; `l0:real^(N,1)finite_sum->real`]
    P2BW_BILFORM_LIP)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_NEG THEN MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN
          ASM_REWRITE_TAC[ETA_AX];
          MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[ETA_AX]];
        MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
         [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2BW_LEBM_CONT THEN BETA_TAC THEN
          MATCH_MP_TAC P2BW_CONT_T1COEFF THEN ASM_REWRITE_TAC[]]];
      X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                     `rho:real^(N,1)finite_sum->real`; `R:real^(N,1)finite_sum->real`;
                     `l0:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                    P2BW_T1_INTEGRABLE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `p2bw_t1 om (A:real^(N,1)finite_sum->real^N^N) rho R l0` THEN
      REWRITE_TAC[p2bw_t1] THEN DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(\z. lift((phi:real^(N,1)finite_sum->real) z *
                  --(wan_tder (l0:real^(N,1)finite_sum->real) z *
                     (rho:real^(N,1)finite_sum->real) z +
                     p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l0 l0 z +
                     (&(dimindex(:N)) / (&2 * drop(sndcart z)) -
                      (R:real^(N,1)finite_sum->real) z) * rho z) +
                  --(&1) * p2bw_bil A l0 phi z)) =
        (\z. --(lift(phi z * (wan_tder l0 z * rho z + p2bw_bil A l0 l0 z +
                              (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) * rho z) +
                     p2bw_bil A l0 phi z)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_NEG] THEN GEN_TAC THEN AP_TERM_TAC THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[INTEGRAL_NEG; DROP_NEG] THEN REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  REWRITE_TAC[p2bw_csub] THEN X_GEN_TAC `psi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bw_ltest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `p2bw_ltest om (\z. p2bw_uof (l0:real^(N,1)finite_sum->real) z * psi z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_ltest] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_SIMP_TAC[P2BW_UOF_LOCLIP; ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[P2BW_UOF_POS; REAL_LT_IMP_LE];
      EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\z. p2bw_uof (l0:real^(N,1)finite_sum->real) z * psi z` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_ltest")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b. a = b ==> a <= &0 ==> b <= &0`) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{z | z IN k /\ ~((\w. lift((l0:real^(N,1)finite_sum->real) w)) differentiable at z)}
              UNION
              {z | z IN k /\ ~((\w. lift((psi:real^(N,1)finite_sum->real) w)) differentiable at z)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN MATCH_MP_TAC P2BW_LOCLIP_AE_ON THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN k` THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THENL
   [STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC P2BW_CSUB_POINT THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) (p2bw_uof (l0:real^(N,1)finite_sum->real))
               psi z = &0 /\
      p2bw_bil A l0 (\z. p2bw_uof l0 z * psi z) z = &0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2BW_BIL_ZERO_OUTSIDE THEN
      EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; REAL_MUL_RZERO];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID]]);;

let P2BW_LIMIT = prove
 (`!n:N->bool. P2BW_LIMIT_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[P2BW_LIMIT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`om:real^(N,1)finite_sum->bool`; `A:num->real^(N,1)finite_sum->real^N^N`;
                       `rho:num->real^(N,1)finite_sum->real`; `R:num->real^(N,1)finite_sum->real`;
                       `l:num->real^(N,1)finite_sum->real`; `A0:real^(N,1)finite_sum->real^N^N`;
                       `rho0:real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`;
                       `l0:real^(N,1)finite_sum->real`] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BW_LIMIT_LOCLIP
    (CONJ (REWRITE_RULE[p2bw_unilip]
             (ASSUME `p2bw_unilip om (l:num->real^(N,1)finite_sum->real)`))
          (REWRITE_RULE[p2bw_locunif]
             (ASSUME `p2bw_locunif om (l:num->real^(N,1)finite_sum->real) l0`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((A0:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on om) /\
    (\z. lift((rho0:real^(N,1)finite_sum->real) z)) continuous_on om /\
    (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A0 z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bw_coeff om (A0:real^(N,1)finite_sum->real^N^N) rho0` THEN
    REWRITE_TAC[p2bw_coeff] THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_t1 om (A0:real^(N,1)finite_sum->real^N^N) rho0 R0 l0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_T1_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`A:num->real^(N,1)finite_sum->real^N^N`;
                          `rho:num->real^(N,1)finite_sum->real`;
                          `R:num->real^(N,1)finite_sum->real`;
                          `l:num->real^(N,1)finite_sum->real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BW_ENERGY_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`rho:num->real^(N,1)finite_sum->real`;
                          `R:num->real^(N,1)finite_sum->real`;
                          `rho0:real^(N,1)finite_sum->real`; `R0:real^(N,1)finite_sum->real`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BW_CSUB_FROM_T1 THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BW_TID_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`A:num->real^(N,1)finite_sum->real^N^N`;
                          `rho:num->real^(N,1)finite_sum->real`;
                          `R:num->real^(N,1)finite_sum->real`;
                          `l:num->real^(N,1)finite_sum->real`] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The divergence form of the Laplacian: P2BW_LLAP_DIV, the theorem          *)
(* |- !n. WAN_LLAP_DIV_STATEMENT n.                                          *)
(* ------------------------------------------------------------------------- *)

(* s11: the divergence form of the Laplacian, WAN_LLAP_DIV_STATEMENT       *)
(* (theorem P2BW_LLAP_DIV).  Route: llap G phi = ldiv G (G^-1 grad phi)    *)
(* (the raised-covector formula RFU_LDIV_RAISE of pc_rf_unique, reproduced  *)
(* below as P2BW_LDIV_RAISE with its two helpers, since the closure of that *)
(* unit, 22 further units of the Ricci flow analysis layer, is not needed   *)
(* otherwise), and ldiv G Z sqrt(det G) = trace D(sqrt(det G) Z)           *)
(* (GRGT_LDIV_DENSITY of pc_grg_divthm).                                     *)

needs "src/pc_grg_divthm.ml";;

let P2BW_FRECHET_COMPONENT = prove
 (`!(w:real^M->real^N) y h a.
        w differentiable at y /\ 1 <= a /\ a <= dimindex(:N)
        ==> drop(frechet_derivative (\z. lift(w z$a)) (at y) h) =
            (frechet_derivative w (at y) h)$a`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP]);;

let P2BW_SUM3_SWAP23 = prove
 (`!n (f:num->num->num->real).
        sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d. f b c d))) =
        sum(1..n) (\b. sum(1..n) (\d. sum(1..n) (\c. f b c d)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  DISCH_TAC THEN BETA_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[]);;

let P2BW_TRACE_LINEAR = prove
 (`!f:real^N->real^N. trace(matrix f) = sum(1..dimindex(:N)) (\i. f(basis i)$i)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[MATRIX_COMPONENT]);;

let P2BW_LDIV_RAISE = prove
 (`!U (G:real^N->real^N^N) (w:real^N->real^N) y.
    metric_field U G /\ y IN U /\ w differentiable at y
    ==> ldiv G (\z. matrix_inv(G z) ** w z) y =
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          ((frechet_derivative w (at y) (basis b))$a -
           sum(1..dimindex(:N)) (\c. (christoffel G y (basis b) (basis a))$c * w y$c))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `((\z. matrix_inv((G:real^N->real^N^N) z) ** (w:real^N->real^N) z) has_derivative
     (\h. --(matrix_inv(G y) ** mderiv G y h ** matrix_inv(G y)) ** w y +
          matrix_inv(G y) ** frechet_derivative w (at y) h)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `y:real^N`]
                  LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; DISCH_TAC] THEN
    MP_TAC(ISPECL
     [`\z. matrix_inv((G:real^N->real^N^N) z)`;
      `\h. (vectorize:real^N^N->real^(N,N)finite_prod)
             (--(matrix_inv((G:real^N->real^N^N) y) **
                 matrify(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                            (at y) h) ** matrix_inv(G y)))`;
      `w:real^N->real^N`; `frechet_derivative (w:real^N->real^N) (at y)`; `y:real^N`]
     LRG_HAS_DERIVATIVE_MATVEC) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; MATRIFY_VECTORIZE; GSYM mderiv];
    ALL_TAC] THEN
  REWRITE_TAC[ldiv] THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)) THEN
                        ASSUME_TAC(MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR th)) THEN
  REWRITE_TAC[P2BW_TRACE_LINEAR] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CL") THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. christoffel (G:real^N->real^N^N) y (basis i)
             (matrix_inv (G y) ** (w:real^N->real^N) y)$i) =
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
       matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "CL" (MP_TAC o SPEC `basis b:real^N` o CONJUNCT1) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL
      [`matrix_inv((G:real^N->real^N^N) y) ** (w:real^N->real^N) y`; `b:num`]
      (MATCH_MP LINEAR_COMPONENTWISE_EXPANSION th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (--(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y (basis i) **
                matrix_inv (G y)) ** (w:real^N->real^N) y +
             matrix_inv (G y) ** frechet_derivative w (at y) (basis i))$i =
            sum(1..dimindex(:N))
              (\a. matrix_inv(G y)$i$a * (frechet_derivative w (at y) (basis i))$a) -
            (sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
               matrix_inv(G y)$i$d * (christoffel G y (basis i) (basis d))$c * w y$c)) +
             sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
               matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG] THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT;
                 MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\j. (matrix_inv((G:real^N->real^N^N) y) ** mderiv G y (basis i) **
              matrix_inv (G y))$i$j * (w:real^N->real^N) y$j) =
      sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
        matrix_inv(G y)$i$d * (christoffel G y (basis i) (basis d))$c * w y$c)) +
      sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
        matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `basis i:real^N`; `i:num`; `c:num`] LRG_GINV_MDERIV_GINV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SUM_ADD_NUMSEG];
      REWRITE_TAC[REAL_ARITH `!a b c:real. --(a + b) + c = c - (a + b)`]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SUM_EQ_NUMSEG) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
       (\a. matrix_inv((G:real^N->real^N^N) y)$i$a *
             (frechet_derivative (w:real^N->real^N) (at y) (basis i))$a)) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b * (frechet_derivative w (at y) (basis b))$a))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[LRG_MATRIX_INV_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
       matrix_inv((G:real^N->real^N^N) y)$i$d * (christoffel G y (basis i) (basis d))$c *
       (w:real^N->real^N) y$c))) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b *
       sum(1..dimindex(:N)) (\c. (christoffel G y (basis b) (basis a))$c * w y$c)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [P2BW_SUM3_SWAP23] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y)$d$i = matrix_inv(G y)$i$d`
    SUBST1_TAC THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG] THEN REAL_ARITH_TAC);;

let P2BW_LLAP_DIV = prove
 (`!n:N->bool. WAN_LLAP_DIV_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_LLAP_DIV_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G:real^N->real^N^N`; `phi:real^N->real`;
                       `x:real^N`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `!c. smooth_map_on (:real^N)
          (\z. frechet_derivative (\v. lift((phi:real^N->real) v)) (at z) (basis c))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w:real^N->real^N.
      !z c. 1 <= c /\ c <= dimindex(:N)
            ==> w z$c = drop(frechet_derivative (\v. lift((phi:real^N->real) v)) (at z) (basis c))`
  (X_CHOOSE_THEN `w:real^N->real^N` (LABEL_TAC "w")) THENL
   [EXISTS_TAC `\z. (lambda c. drop(frechet_derivative (\v. lift((phi:real^N->real) v)) (at z)
                                       (basis c))):real^N` THEN
    SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. 1 <= c /\ c <= dimindex(:N)
        ==> (\z. lift((w:real^N->real^N) z$c)) =
            (\z. frechet_derivative (\v. lift((phi:real^N->real) v)) (at z) (basis c))`
  (LABEL_TAC "wc") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    USE_THEN "w" (fun th -> ASM_SIMP_TAC[th; LIFT_DROP]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (w:real^N->real^N) differentiable at y` ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC I [DIFFERENTIABLE_COMPONENTWISE_AT] THEN
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    USE_THEN "wc" (fun th -> ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  (* llap as the divergence of the raised gradient *)
  SUBGOAL_THEN `llap G (phi:real^N->real) x = ldiv G (\z. matrix_inv(G z) ** (w:real^N->real^N) z) x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `w:real^N->real^N`; `x:real^N`]
                  P2BW_LDIV_RAISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[llap] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) x)$j$i = matrix_inv(G x)$i$j` SUBST1_TAC THENL
     [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; ALL_TAC] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [MP_TAC(ISPECL [`w:real^N->real^N`; `x:real^N`; `basis i:real^N`; `j:num`]
                    P2BW_FRECHET_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "wc" (fun th -> ASM_SIMP_TAC[th]);
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
      AP_TERM_TAC THEN USE_THEN "w" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  (* the raised gradient is differentiable *)
  SUBGOAL_THEN `(\z. matrix_inv((G:real^N->real^N^N) z) ** (w:real^N->real^N) z) differentiable at x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^N->real^N^N`; `s:real^N->bool`; `x:real^N`]
                  LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; DISCH_TAC] THEN
    REWRITE_TAC[differentiable] THEN
    MP_TAC(ISPECL
     [`\z. matrix_inv((G:real^N->real^N^N) z)`;
      `\h. (vectorize:real^N^N->real^(N,N)finite_prod)
             (--(matrix_inv((G:real^N->real^N^N) x) **
                 matrify(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                            (at x) h) ** matrix_inv(G x)))`;
      `w:real^N->real^N`; `frechet_derivative (w:real^N->real^N) (at x)`; `x:real^N`]
     LRG_HAS_DERIVATIVE_MATVEC) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`;
                 `\z. matrix_inv((G:real^N->real^N^N) z) ** (w:real^N->real^N) z`; `x:real^N`]
                GRGT_LDIV_DENSITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[P2BW_TRACE_LINEAR] THEN
  SUBGOAL_THEN
   `(\z. sqrt(det((G:real^N->real^N^N) z)) % (matrix_inv(G z) ** (w:real^N->real^N) z))
    differentiable at x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN ASM_REWRITE_TAC[o_DEF] THEN
    REWRITE_TAC[differentiable] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`]
                  GRGT_SQRT_DET_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\z. sqrt(det((G:real^N->real^N^N) z)) % (matrix_inv(G z) ** (w:real^N->real^N) z)`;
                 `x:real^N`; `basis i:real^N`; `i:num`] P2BW_FRECHET_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[wan_dpart] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN BETA_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN USE_THEN "w" (fun th -> ASM_SIMP_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The final step of MT Prop 9.20 (MT p. 198): P2BW_REG.  U is smooth        *)
(* (WAN_CONJ_HEAT_REG), hence l0; the weak equation tested with psi / U and *)
(* integrated by parts gives (9.4) through the divergence form of llap on   *)
(* the time slices (P2BW_LLAP_DIV_LOCAL, P2BW_SLICE_LLAP); the weak         *)
(* identity gives the first-order relation, and (9.5) follows.              *)
(* ------------------------------------------------------------------------- *)

(* s12: tools for the final step (P2BW_REG): integration by parts against   *)
(* coefficients smooth on the open set, slices at fixed time, local form   *)
(* of the divergence identity for llap. *)

let P2BW_TEST_IBP_OPEN = prove
 (`!(om:real^M->bool) psi H i.
     open om /\ wan_test om psi /\ smooth_map_on om (\x. lift(H x))
     ==> (\x. lift(wan_dpart i psi x * H x)) integrable_on om /\
         (\x. lift(psi x * wan_dpart i H x)) integrable_on om /\
         integral om (\x. lift(wan_dpart i psi x * H x)) =
         --(integral om (\x. lift(psi x * wan_dpart i H x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `psi:real^M->real`; `H:real^M->real`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(wan_dpart i (psi:real^M->real) x * H x)) integrable_on om /\
    (\x. lift(psi x * wan_dpart i (H:real^M->real) x)) integrable_on om`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN
      ASM_SIMP_TAC[WAN_TEST_DPART_OPEN; ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[wan_dpart; LIFT_DROP] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `integral om (\x. lift(wan_dpart i (\x. (psi:real^M->real) x * H x) x)) = vec 0`
  MP_TAC THENL
   [MP_TAC(ISPECL [`om:real^M->bool`; `\x. (psi:real^M->real) x * H x`; `\x:real^M. &1`;
                   `basis i:real^M`] WAN_TEST_IBP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID; FRECHET_DERIVATIVE_CONST_AT; DROP_VEC;
                REAL_MUL_RZERO; LIFT_NUM; INTEGRAL_0; VECTOR_NEG_0] THEN
    REWRITE_TAC[GSYM wan_dpart] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_ADD] THEN ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

let P2BW_SLICE_DPART = prove
 (`!(H:real^(N,1)finite_sum->real) x t i.
     (\w. lift(H w)) differentiable at (pastecart x t)
     ==> wan_dpart i (\y. H(pastecart y t)) x = wan_xder i H (pastecart x t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; wan_xder] THEN
  SUBGOAL_THEN
   `((\y:real^N. lift((H:real^(N,1)finite_sum->real)(pastecart y t))) has_derivative
     (frechet_derivative (\w. lift(H w)) (at (pastecart x t)) o (\v. pastecart v (vec 0))))
    (at x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y:real^N. lift((H:real^(N,1)finite_sum->real)(pastecart y t))) =
      (\w. lift(H w)) o (\y. pastecart y t)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

let P2BW_SLICE_OPEN = prove
 (`!(om:real^(N,1)finite_sum->bool) t.
     open om ==> open {x:real^N | pastecart x t IN om}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N | pastecart x (t:real^1) IN (om:real^(N,1)finite_sum->bool)} =
                {x | x IN (:real^N) /\ (\y. pastecart y t) x IN om}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let P2BW_SLICE_SMOOTH = prove
 (`!(om:real^(N,1)finite_sum->bool) (f:real^(N,1)finite_sum->real^K) t.
     open om /\ smooth_map_on om f
     ==> smooth_map_on {x:real^N | pastecart x t IN om} (\x. f(pastecart x t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. (f:real^(N,1)finite_sum->real^K)(pastecart x t)) =
                f o (\x. pastecart x t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN
  ASM_SIMP_TAC[P2BW_SLICE_OPEN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_SIMP_TAC[P2BW_SLICE_OPEN; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let P2BW_SLICE_METRIC_FIELD = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) t.
     open om /\ smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v))
     ==> metric_field {x:real^N | pastecart x t IN om} (\x. G(pastecart x t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field] THEN
  ASM_SIMP_TAC[P2BW_SLICE_OPEN; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^(N,1)finite_sum->real^N^N)`;
                 `t:real^1`] P2BW_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let P2BW_TEST_BUMP1 = prove
 (`!(s:real^N->bool) x0.
     open s /\ x0 IN s
     ==> ?chi e. &0 < e /\ ball(x0,e) SUBSET s /\ wan_test s chi /\
                 !x. x IN ball(x0,e) ==> chi x = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. smooth_bump (e / &2) e (x - x0)` THEN EXISTS_TAC `e / &2` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^N,e)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[wan_test] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^N. lift(smooth_bump (e / &2) e (x - x0))) =
                    (\x. lift(smooth_bump (e / &2) e x)) o (\x. x - x0)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
        MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
      EXISTS_TAC `cball(x0:real^N,e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_BUMP_0 THEN
      MP_TAC(ISPECL [`x0:real^N`; `x:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    MP_TAC(ISPECL [`x0:real^N`; `x:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC]);;

let P2BW_LLAP_DIV_LOCAL = prove
 (`!(s:real^N->bool) (G:real^N->real^N^N) (f:real^N->real) s' x.
     metric_field s G /\ open s' /\ s' SUBSET s /\ x IN s' /\
     smooth_map_on s' (\y. lift(f y))
     ==> llap G f x * sqrt(det(G x)) =
         sum(1..dimindex(:N))
            (\i. wan_dpart i
                   (\y. sqrt(det(G y)) *
                        sum(1..dimindex(:N))
                           (\j. matrix_inv(G y)$i$j * wan_dpart j f y)) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^N->bool`; `x:real^N`] P2BW_TEST_BUMP1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s':real^N->bool`; `chi:real^N->real`; `f:real^N->real`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN ball(x:real^N,e) ==> (chi:real^N->real) y * f y = f y`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LID]; ALL_TAC] THEN
  MP_TAC(SPEC `(:N)` P2BW_LLAP_DIV) THEN REWRITE_TAC[WAN_LLAP_DIV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `G:real^N->real^N^N`;
                             `\y:real^N. (chi:real^N->real) y * f y`; `x:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `wan_test (s':real^N->bool) (\x. (chi:real^N->real) x * f x)` THEN
      SIMP_TAC[wan_test];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!a b c d:real. a = b /\ c = d ==> a = c ==> b = d`) THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LLAP_LOCAL THEN
    EXISTS_TAC `ball(x:real^N,e)` THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[wan_dpart] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `ball(x:real^N,e)` THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `ball(x:real^N,e)` THEN ASM_SIMP_TAC[OPEN_BALL]]);;

(* s13: smoothness bookkeeping and slice identities for P2BW_REG. *)

let P2BW_SM_MUL = prove
 (`!(s:real^M->bool) f g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`; `\x. lift((g:real^M->real) x)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2BW_SM_SUB = prove
 (`!(s:real^M->bool) f g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`; `\x. lift((g:real^M->real) x)`]
                SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2BW_SM_SUM = prove
 (`!(s:real^M->bool) (f:num->real^M->real) n.
     open s /\ (!j. 1 <= j /\ j <= n ==> smooth_map_on s (\x. lift(f j x)))
     ==> smooth_map_on s (\x. lift(sum(1..n) (\j. f j x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\j x. lift((f:num->real^M->real) j x)`; `1..n`]
                SMOOTH_MAP_ON_LIFT_SUM) THEN
  ASM_SIMP_TAC[LIFT_DROP; FINITE_NUMSEG; IN_NUMSEG; ETA_AX]);;

let P2BW_SM_FDER = prove
 (`!(s:real^M->bool) u v.
     open s /\ smooth_map_on s (\x. lift(u x))
     ==> smooth_map_on s (\x. lift(drop(frechet_derivative (\w. lift(u w)) (at x) v)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let P2BW_SQRTDET_SMOOTH = prove
 (`!(om:real^M->bool) (G:real^M->real^N^N).
     open om /\ smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v))
     ==> smooth_map_on om (\z. lift(sqrt(det(G z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on om (\z. lift(det((G:real^M->real^N^N) z)))` ASSUME_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`om:real^M->bool`; `G:real^M->real^N^N`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[smooth_map_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`om:real^M->bool`; `\z. lift(det((G:real^M->real^N^N) z))`]
                          SMOOTH_MAP_ON_LIFT_SQRT)) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[]);;

let P2BW_INV_ENTRY_SMOOTH = prove
 (`!(om:real^M->bool) (G:real^M->real^N^N) i j.
     open om /\ smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> smooth_map_on om (\z. lift(matrix_inv(G z)$i$j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `\z. matrix_inv((G:real^M->real^N^N) z)`]
                LRG_SMOOTH_VECTORIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. &0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[]]);;

(* The coefficient field B_i = sqrt(det G) sum_j (G^-1)_ij d_j l of the      *)
(* divergence form, and its smoothness. *)

let P2BW_BCOEF_SMOOTH = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) l0 i.
     open om /\ smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(l0 z)) /\ 1 <= i /\ i <= dimindex(:N)
     ==> smooth_map_on om
           (\w. lift(sqrt(det(G w)) *
                     sum(1..dimindex(:N)) (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SM_MUL THEN ASM_SIMP_TAC[P2BW_SQRTDET_SMOOTH] THEN
  MATCH_MP_TAC P2BW_SM_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BW_SM_MUL THEN ASM_SIMP_TAC[P2BW_INV_ENTRY_SMOOTH] THEN
  REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_SM_FDER THEN ASM_REWRITE_TAC[]);;

(* Slice identities at z = pastecart (fstcart z) (sndcart z). *)

let P2BW_SLICE_LLAP = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) l0 z.
     open om /\ smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(l0 z)) /\ z IN om
     ==> llap (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) * sqrt(det(G z)) =
         sum(1..dimindex(:N))
           (\i. wan_xder i (\w. sqrt(det(G w)) *
                                sum(1..dimindex(:N)) (\j. matrix_inv(G w)$i$j * wan_xder j l0 w))
                  z) /\
         lgrad2 (p2bw_slice G z) (p2bw_fslice l0 z) (fstcart z) =
         sum(1..dimindex(:N))
           (\i. sum(1..dimindex(:N))
                  (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2bw_slice; p2bw_fslice] THEN
  ABBREV_TAC `t = sndcart(z:real^(N,1)finite_sum)` THEN
  ABBREV_TAC `x0 = fstcart(z:real^(N,1)finite_sum)` THEN
  SUBGOAL_THEN `pastecart (x0:real^N) (t:real^1) = z` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x0"; "t"] THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN {x | pastecart x (t:real^1) IN om} /\
                pastecart (x0:real^N) (t:real^1) IN om`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN om ==> (\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y j. pastecart y (t:real^1) IN om
          ==> wan_dpart j (\x. (l0:real^(N,1)finite_sum->real)(pastecart x t)) y =
              wan_xder j l0 (pastecart y t)`
  (LABEL_TAC "SD") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BW_SLICE_DPART THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^N | pastecart x (t:real^1) IN om}`;
                   `\x. (G:real^(N,1)finite_sum->real^N^N)(pastecart x t)`;
                   `\x. (l0:real^(N,1)finite_sum->real)(pastecart x t)`;
                   `{x:real^N | pastecart x (t:real^1) IN om}`; `x0:real^N`]
                  P2BW_LLAP_DIV_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P2BW_SLICE_METRIC_FIELD; P2BW_SLICE_OPEN; SUBSET_REFL] THEN
      MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                     `\w. lift((l0:real^(N,1)finite_sum->real) w)`; `t:real^1`]
                    P2BW_SLICE_SMOOTH) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`\w. sqrt(det((G:real^(N,1)finite_sum->real^N^N) w)) *
                        sum(1..dimindex(:N)) (\j. matrix_inv(G w)$i$j *
                                                  wan_xder j (l0:real^(N,1)finite_sum->real) w)`;
                   `x0:real^N`; `t:real^1`; `i:num`] P2BW_SLICE_DPART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[P2BW_BCOEF_SMOOTH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[wan_dpart] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `{x:real^N | pastecart x (t:real^1) IN om}` THEN
    ASM_SIMP_TAC[P2BW_SLICE_OPEN] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM wan_dpart] THEN USE_THEN "SD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[lgrad2] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM wan_dpart] THEN
    USE_THEN "SD" (fun th -> REWRITE_TAC
      [MP (SPECL [`x0:real^N`; `i:num`] th) (ASSUME `pastecart (x0:real^N) (t:real^1) IN om`);
       MP (SPECL [`x0:real^N`; `j:num`] th) (ASSUME `pastecart (x0:real^N) (t:real^1) IN om`)]) THEN
    ASM_REWRITE_TAC[]]);;

(* s14: the final step of MT Prop 9.20 (P2BW_REG). *)

let P2BW_UINV_DERIV = prove
 (`!(l0:real^(N,1)finite_sum->real) z.
     &0 < drop(sndcart z) /\ (\w. lift(l0 w)) differentiable at z /\
     (\y. lift(inv(p2bw_uof l0 y))) differentiable at z
     ==> !v. drop(frechet_derivative (\y. lift(inv(p2bw_uof l0 y))) (at z) v) =
             inv(p2bw_uof l0 z) *
             (drop(frechet_derivative (\w. lift(l0 w)) (at z) v) +
              &(dimindex(:N)) / &2 * inv(drop(sndcart z)) * drop(sndcart v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^(N,1)finite_sum` THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UOF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. inv(p2bw_uof (l0:real^(N,1)finite_sum->real) y)`;
                 `p2bw_uof (l0:real^(N,1)finite_sum->real)`; `z:real^(N,1)finite_sum`;
                 `v:real^(N,1)finite_sum`] P2BW_DER_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `!y. inv(p2bw_uof (l0:real^(N,1)finite_sum->real) y) * p2bw_uof l0 y = &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `y:real^(N,1)finite_sum`] P2BW_UOF_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_RING `!u v x k:real. v * u = &1 /\ &0 = v * (--u * k) + u * x ==> x = v * k`) THEN
  EXISTS_TAC `p2bw_uof (l0:real^(N,1)finite_sum->real) z` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UOF_POS) THEN
  REAL_ARITH_TAC);;

let P2BW_REG_ALG = prove
 (`!n (g:num->num->real) (xl:num->real) (xps:num->real) psi U Ui tl0 ct R sg.
     U * Ui = &1 /\ (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> g i j = g j i)
     ==> ((psi * Ui) * (--U * (tl0 + ct)) + R * (psi * Ui) * U +
          sum(1..n) (\i. sum(1..n) (\j. g i j * (--U * xl i) * (xps j * Ui + psi * (Ui * xl j))))) *
         sg =
         psi * ((R - tl0 - ct - sum(1..n) (\i. sum(1..n) (\j. g i j * xl i * xl j))) * sg) -
         sum(1..n) (\i. xps i * (sg * sum(1..n) (\j. g i j * xl j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. sum(1..n) (\j. (g:num->num->real) i j * (--U * (xl:num->real) i) *
                                  ((xps:num->real) j * Ui + psi * (Ui * xl j)))) =
    --(sum(1..n) (\i. sum(1..n) (\j. g i j * xl i * xps j))) -
    psi * sum(1..n) (\i. sum(1..n) (\j. g i j * xl i * xl j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    UNDISCH_TAC `U * Ui = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. (xps:num->real) i * (sg * sum(1..n) (\j. (g:num->num->real) i j * xl j))) =
    sg * sum(1..n) (\i. sum(1..n) (\j. g i j * (xl:num->real) i * xps j))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `g:num->num->real`; `xl:num->real`; `xps:num->real`]
                  WAN_SUM_SWAP_SYM) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `U * Ui = &1` THEN CONV_TAC REAL_RING);;

(* s15: P2BW_REG. *)

let P2BW_REG_SMOOTH = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) R l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(R z)) /\ wan_loclip om l0 /\
     (!phi. wan_test om phi
            ==> integral om
                  (\z. lift((phi z * wan_tder (p2bw_uof l0) z + R z * phi z * p2bw_uof l0 z +
                             sum(1..dimindex(:N))
                                (\i. sum(1..dimindex(:N))
                                       (\j. matrix_inv(G z)$i$j * wan_xder i (p2bw_uof l0) z *
                                            wan_xder j phi z))) *
                            sqrt(det(G z)))) = vec 0)
     ==> smooth_map_on om (\z. lift(p2bw_uof l0 z)) /\ smooth_map_on om (\z. lift(l0 z)) /\
         smooth_map_on om (\z. lift(inv(p2bw_uof l0 z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on om (\z. lift(p2bw_uof (l0:real^(N,1)finite_sum->real) z))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `(:N)` WAN_CONJ_HEAT_REG) THEN REWRITE_TAC[WAN_CONJ_HEAT_REG_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G:real^(N,1)finite_sum->real^N^N`; `R:real^(N,1)finite_sum->real`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2BW_UOF_LOCLIP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. lift(--log(p2bw_uof (l0:real^(N,1)finite_sum->real) z) -
                         &(dimindex(:N)) / &2 * log(drop(sndcart z)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[p2bw_uof; LOG_EXP] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`;
                                 `\z. lift(p2bw_uof (l0:real^(N,1)finite_sum->real) z)`]
                                SMOOTH_MAP_ON_LIFT_LOG)) THEN
        ASM_REWRITE_TAC[LIFT_DROP; P2BW_UOF_POS];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. sndcart z`]
                      SMOOTH_MAP_ON_LIFT_LOG) THEN
        ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[ETA_AX] THEN
        MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. z`]
                      SMOOTH_MAP_ON_SNDCART_OPEN) THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]]];
    MP_TAC(BETA_RULE(ISPECL [`om:real^(N,1)finite_sum->bool`;
                             `\z. lift(p2bw_uof (l0:real^(N,1)finite_sum->real) z)`]
                            SMOOTH_MAP_ON_LIFT_INV)) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `y:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `y:real^(N,1)finite_sum`] P2BW_UOF_POS) THEN
    REAL_ARITH_TAC]);;

(* The pointwise form of the weak equation tested with psi / U. *)

let P2BW_REG_POINT = prove
 (`!(G:real^(N,1)finite_sum->real^N^N) R l0 psi z.
     &0 < drop(sndcart z) /\ (\w. lift(l0 w)) differentiable at z /\
     (\y. lift(inv(p2bw_uof l0 y))) differentiable at z /\
     (\y. lift(psi y)) differentiable at z /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> matrix_inv(G z)$i$j = matrix_inv(G z)$j$i) /\
     (!j. wan_dpart j (\x. psi x * inv(p2bw_uof l0 x)) z =
          wan_dpart j psi z * inv(p2bw_uof l0 z) +
          psi z * wan_dpart j (\x. inv(p2bw_uof l0 x)) z)
     ==> ((\x. psi x * inv(p2bw_uof l0 x)) z * wan_tder (p2bw_uof l0) z +
          R z * (\x. psi x * inv(p2bw_uof l0 x)) z * p2bw_uof l0 z +
          sum(1..dimindex(:N))
             (\i. sum(1..dimindex(:N))
                    (\j. matrix_inv(G z)$i$j * wan_xder i (p2bw_uof l0) z *
                         wan_xder j (\x. psi x * inv(p2bw_uof l0 x)) z))) *
         sqrt(det(G z)) =
         psi z * ((R z - wan_tder l0 z - &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                   sum(1..dimindex(:N))
                      (\i. sum(1..dimindex(:N))
                             (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z))) *
                  sqrt(det(G z))) -
         sum(1..dimindex(:N))
            (\i. wan_xder i psi z *
                 (sqrt(det(G z)) *
                  sum(1..dimindex(:N)) (\j. matrix_inv(G z)$i$j * wan_xder j l0 z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UOF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UINV_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_xder j (\x. (psi:real^(N,1)finite_sum->real) x * inv(p2bw_uof l0 x)) z =
            wan_xder j psi z * inv(p2bw_uof l0 z) + psi z * (inv(p2bw_uof l0 z) * wan_xder j l0 z)`
  (LABEL_TAC "XP") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_xder j (\x. (psi:real^(N,1)finite_sum->real) x * inv(p2bw_uof l0 x)) z =
      wan_dpart j (\x. psi x * inv(p2bw_uof l0 x)) z /\
      wan_xder j psi z = wan_dpart j psi z`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC[WAN_XDER_DPART]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[wan_dpart; wan_xder] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM TEXT_PASTECART_BASIS_LOW; SNDCART_PASTECART; DROP_VEC; REAL_MUL_RZERO;
                 REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_xder i (p2bw_uof (l0:real^(N,1)finite_sum->real)) z =
            --(p2bw_uof l0 z) * wan_xder i l0 z`
  (LABEL_TAC "XU") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_xder] THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_tder (p2bw_uof (l0:real^(N,1)finite_sum->real)) z =
    --(p2bw_uof l0 z) * (wan_tder l0 z + &(dimindex(:N)) / (&2 * drop(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_tder] THEN ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                  wan_xder i (p2bw_uof (l0:real^(N,1)finite_sum->real)) z *
                  wan_xder j (\x. (psi:real^(N,1)finite_sum->real) x * inv(p2bw_uof l0 x)) z)) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. matrix_inv(G z)$i$j * (--(p2bw_uof l0 z) * wan_xder i l0 z) *
                  (wan_xder j psi z * inv(p2bw_uof l0 z) +
                   psi z * (inv(p2bw_uof l0 z) * wan_xder j l0 z))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "XU" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "XP" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `\i j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j`;
                 `\i. wan_xder i (l0:real^(N,1)finite_sum->real) z`;
                 `\i. wan_xder i (psi:real^(N,1)finite_sum->real) z`; `(psi:real^(N,1)finite_sum->real) z`;
                 `p2bw_uof (l0:real^(N,1)finite_sum->real) z`; `inv(p2bw_uof (l0:real^(N,1)finite_sum->real) z)`;
                 `wan_tder (l0:real^(N,1)finite_sum->real) z`;
                 `&(dimindex(:N)) / (&2 * drop(sndcart(z:real^(N,1)finite_sum)))`;
                 `(R:real^(N,1)finite_sum->real) z`;
                 `sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))`] P2BW_REG_ALG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    MP_TAC(ISPECL [`l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_UOF_POS) THEN
    REAL_ARITH_TAC;
    DISCH_THEN ACCEPT_TAC]);;

(* s16: P2BW_REG, the assembly. *)

(* Smoothness of the scalar terms of the two pointwise equations. *)

let P2BW_REG_TERMS_SMOOTH = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) R l0.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(R z)) /\ smooth_map_on om (\z. lift(l0 z))
     ==> smooth_map_on om (\z. lift(wan_tder l0 z)) /\
         smooth_map_on om (\z. lift(&(dimindex(:N)) / (&2 * drop(sndcart z)))) /\
         smooth_map_on om (\z. lift(l0 z / (&2 * drop(sndcart z)))) /\
         smooth_map_on om (\z. lift(sqrt(det(G z)))) /\
         smooth_map_on om
           (\z. lift(sum(1..dimindex(:N))
                       (\i. sum(1..dimindex(:N))
                              (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z)))) /\
         smooth_map_on om
           (\z. lift(sum(1..dimindex(:N))
                       (\i. wan_xder i (\w. sqrt(det(G w)) *
                                            sum(1..dimindex(:N))
                                               (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on om (\z:real^(N,1)finite_sum. lift(&2 * drop(sndcart z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL; LIFT_DROP] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. z`]
                  SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_SM_FDER THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z:real^(N,1)finite_sum. lift(&(dimindex(:N)))`;
                   `\z:real^(N,1)finite_sum. lift(&2 * drop(sndcart z))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!t. &0 < t ==> ~(&2 * t = &0)`) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`;
                   `\z:real^(N,1)finite_sum. lift((l0:real^(N,1)finite_sum->real) z)`;
                   `\z:real^(N,1)finite_sum. lift(&2 * drop(sndcart z))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!t. &0 < t ==> ~(&2 * t = &0)`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BW_SQRTDET_SMOOTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_SM_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BW_SM_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BW_SM_MUL THEN ASM_SIMP_TAC[P2BW_INV_ENTRY_SMOOTH] THEN
    MATCH_MP_TAC P2BW_SM_MUL THEN ASM_REWRITE_TAC[wan_xder] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2BW_SM_FDER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BW_SM_SUM THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2BW_SM_FDER THEN
    ASM_REWRITE_TAC[GSYM wan_xder] THEN MATCH_MP_TAC P2BW_BCOEF_SMOOTH THEN
    ASM_REWRITE_TAC[]]);;

(* The weak equation tested with psi / U, integrated by parts. *)

let P2BW_REG_E1_INT = prove
 (`!(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N) R l0 psi.
     open om /\ (!z. z IN om ==> &0 < drop(sndcart z)) /\
     smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
     smooth_map_on om (\z. lift(R z)) /\ smooth_map_on om (\z. lift(l0 z)) /\
     smooth_map_on om (\z. lift(inv(p2bw_uof l0 z))) /\
     (!phi. wan_test om phi
            ==> integral om
                  (\z. lift((phi z * wan_tder (p2bw_uof l0) z + R z * phi z * p2bw_uof l0 z +
                             sum(1..dimindex(:N))
                                (\i. sum(1..dimindex(:N))
                                       (\j. matrix_inv(G z)$i$j * wan_xder i (p2bw_uof l0) z *
                                            wan_xder j phi z))) *
                            sqrt(det(G z)))) = vec 0) /\
     wan_test om psi
     ==> integral om
           (\z. lift(((R z - wan_tder l0 z - &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                       sum(1..dimindex(:N))
                          (\i. sum(1..dimindex(:N))
                                 (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z))) *
                      sqrt(det(G z)) +
                      sum(1..dimindex(:N))
                         (\i. wan_xder i (\w. sqrt(det(G w)) *
                                              sum(1..dimindex(:N))
                                                 (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)) *
                     psi z)) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `R:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`]
                P2BW_REG_TERMS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`;
                 `\x. inv(p2bw_uof (l0:real^(N,1)finite_sum->real) x)`] WAN_TEST_SMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x. (psi:real^(N,1)finite_sum->real) x *
                                   inv(p2bw_uof (l0:real^(N,1)finite_sum->real) x)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_tder")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w. w IN om ==> (\y. lift((l0:real^(N,1)finite_sum->real) y)) differentiable at w /\
                                (\y. lift(inv(p2bw_uof l0 y))) differentiable at w /\
                                (\y. lift((psi:real^(N,1)finite_sum->real) y)) differentiable at w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `om:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      ASM_MESON_TAC[wan_test]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z i j. z IN om /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j = matrix_inv(G z)$j$i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `transp(matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)) = matrix_inv(G z)`
    MP_TAC THENL
     [REWRITE_TAC[TRANSP_MATRIX_INV] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[TRANSP_COMPONENT];
    ALL_TAC] THEN
  (* rewrite the integrand pointwise on om *)
  SUBGOAL_THEN
   `integral om
      (\z. lift((((psi:real^(N,1)finite_sum->real) z *
                  inv(p2bw_uof (l0:real^(N,1)finite_sum->real) z)) *
                 wan_tder (p2bw_uof l0) z +
                 (R:real^(N,1)finite_sum->real) z * (psi z * inv(p2bw_uof l0 z)) *
                 p2bw_uof l0 z +
                 sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N))
                           (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                                wan_xder i (p2bw_uof l0) z *
                                wan_xder j (\x. psi x * inv(p2bw_uof l0 x)) z))) *
                sqrt(det(G z)))) =
    integral om
      (\z. lift(psi z * ((R z - wan_tder l0 z - &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                          sum(1..dimindex(:N))
                             (\i. sum(1..dimindex(:N))
                                    (\j. matrix_inv(G z)$i$j * wan_xder i l0 z *
                                         wan_xder j l0 z))) *
                         sqrt(det(G z))) -
                sum(1..dimindex(:N))
                   (\i. wan_xder i psi z *
                        (sqrt(det(G z)) *
                         sum(1..dimindex(:N)) (\j. matrix_inv(G z)$i$j * wan_xder j l0 z)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(BETA_RULE(SPECL [`G:real^(N,1)finite_sum->real^N^N`; `R:real^(N,1)finite_sum->real`;
                            `l0:real^(N,1)finite_sum->real`; `psi:real^(N,1)finite_sum->real`;
                            `z:real^(N,1)finite_sum`] P2BW_REG_POINT)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  (* integrability and integration by parts *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\z. lift(wan_xder i (psi:real^(N,1)finite_sum->real) z *
                      (sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) *
                       sum(1..dimindex(:N))
                          (\j. matrix_inv(G z)$i$j *
                               wan_xder j (l0:real^(N,1)finite_sum->real) z)))) integrable_on om /\
            (\z. lift(psi z * wan_xder i (\w. sqrt(det(G w)) *
                                              sum(1..dimindex(:N))
                                                 (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z))
              integrable_on om /\
            integral om (\z. lift(wan_xder i psi z *
                                  (sqrt(det(G z)) *
                                   sum(1..dimindex(:N))
                                      (\j. matrix_inv(G z)$i$j * wan_xder j l0 z)))) =
            --(integral om (\z. lift(psi z * wan_xder i (\w. sqrt(det(G w)) *
                                              sum(1..dimindex(:N))
                                                 (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)))`
  (LABEL_TAC "IBP") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `psi:real^(N,1)finite_sum->real`;
                   `\w. sqrt(det((G:real^(N,1)finite_sum->real^N^N) w)) *
                        sum(1..dimindex(:N))
                           (\j. matrix_inv(G w)$i$j * wan_xder j (l0:real^(N,1)finite_sum->real) w)`;
                   `i:num`] P2BW_TEST_IBP_OPEN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[P2BW_BCOEF_SMOOTH]; ALL_TAC] THEN
    ASM_SIMP_TAC[WAN_XDER_DPART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((psi:real^(N,1)finite_sum->real) z *
              ((R z - wan_tder (l0:real^(N,1)finite_sum->real) z -
                &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                               wan_xder i l0 z * wan_xder j l0 z))) *
               sqrt(det(G z))))) integrable_on om`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC P2BW_SM_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB; LIFT_SUM; o_DEF] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_VSUM; INTEGRAL_VSUM; FINITE_NUMSEG; IN_NUMSEG] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(((R z - wan_tder (l0:real^(N,1)finite_sum->real) z -
                &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                               wan_xder i l0 z * wan_xder j l0 z))) *
               sqrt(det(G z)) +
               sum(1..dimindex(:N))
                  (\i. wan_xder i (\w. sqrt(det(G w)) *
                                       sum(1..dimindex(:N))
                                          (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)) *
              (psi:real^(N,1)finite_sum->real) z)) =
    (\z. lift(psi z * ((R z - wan_tder l0 z - &(dimindex(:N)) / (&2 * drop(sndcart z)) -
                        sum(1..dimindex(:N))
                           (\i. sum(1..dimindex(:N))
                                  (\j. matrix_inv(G z)$i$j * wan_xder i l0 z *
                                       wan_xder j l0 z))) *
                       sqrt(det(G z)))) +
         vsum(1..dimindex(:N))
            (\i. lift(psi z * wan_xder i (\w. sqrt(det(G w)) *
                                              sum(1..dimindex(:N))
                                                 (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[o_DEF] LIFT_SUM); GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_VSUM; INTEGRAL_VSUM; FINITE_NUMSEG; IN_NUMSEG] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `vec 0:real^1`)) THEN
  MATCH_MP_TAC(VECTOR_ARITH `!a b c:real^1. b = --c ==> a - b = vec 0 ==> a + c = vec 0`) THEN
  REWRITE_TAC[GSYM VSUM_NEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "IBP" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]);;

(* s17: the main theorem P2BW_REG. *)

let P2BW_SM_ADD = prove
 (`!(s:real^M->bool) f g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. lift((f:real^M->real) x)`; `\x. lift((g:real^M->real) x)`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2BW_BIL_DENSITY = prove
 (`!(G:real^(N,1)finite_sum->real^N^N) l0 z.
     p2bw_bil (\w. sqrt(det(G w)) %% matrix_inv(G w)) l0 l0 z =
     sqrt(det(G z)) *
     sum(1..dimindex(:N))
        (\i. sum(1..dimindex(:N))
               (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z))`,
  REWRITE_TAC[p2bw_bil; MATRIX_CMUL_COMPONENT; GSYM SUM_LMUL; REAL_MUL_ASSOC]);;

let P2BW_INT_DIFF_ZERO = prove
 (`!(om:real^M->bool) phi a b.
     open om /\ wan_test om phi /\
     (\z. lift(a z)) continuous_on om /\ (\z. lift(b z)) continuous_on om /\
     integral om (\z. lift(phi z * a z)) = integral om (\z. lift(phi z * b z))
     ==> integral om (\z. lift((a z - b z) * phi z)) = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((phi:real^M->real) z * a z)) integrable_on om /\
                (\z. lift(phi z * b z)) integrable_on om`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(((a:real^M->real) z - b z) * phi z)) =
                (\z. lift(phi z * a z) - lift(phi z * b z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_SUB; VECTOR_SUB_REFL]]);;

let P2BW_FUND_POS_EQ = prove
 (`!(om:real^M->bool) f.
     open om /\ (\x. lift(f x)) continuous_on om /\
     (!phi. wan_test om phi /\ (!x. &0 <= phi x)
            ==> integral om (\x. lift(f x * phi x)) = vec 0)
     ==> !x. x IN om ==> f x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `f:real^M->real`] WAN_FUNDAMENTAL_CONT_POS) THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `\x. --((f:real^M->real) x)`] WAN_FUNDAMENTAL_CONT_POS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_NEG] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `phi:real^M->real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LNEG; LIFT_NEG] THEN
      SUBGOAL_THEN `(\x. lift((f:real^M->real) x * phi x)) integrable_on om` ASSUME_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[INTEGRAL_NEG; VECTOR_NEG_0; DROP_VEC; REAL_LE_REFL]]];
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DROP_VEC; REAL_LE_REFL];
    DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2BW_REG = prove
 (`!n:N->bool. P2BW_REG_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[P2BW_REG_STATEMENT; P2BW_BIL_DENSITY] THEN
  MAP_EVERY X_GEN_TAC [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                       `R:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `R:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`]
                P2BW_REG_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `R:real^(N,1)finite_sum->real`; `l0:real^(N,1)finite_sum->real`]
                P2BW_REG_TERMS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN om ==> &0 < sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))`
  (LABEL_TAC "SQ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the first equation in divergence form *)
  SUBGOAL_THEN
   `!z. z IN om
        ==> ((R z - wan_tder l0 z - &(dimindex(:N)) / (&2 * drop(sndcart z)) -
              sum(1..dimindex(:N))
                 (\i. sum(1..dimindex(:N))
                        (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                             wan_xder i (l0:real^(N,1)finite_sum->real) z * wan_xder j l0 z))) *
             sqrt(det(G z)) +
             sum(1..dimindex(:N))
                (\i. wan_xder i (\w. sqrt(det(G w)) *
                                     sum(1..dimindex(:N))
                                        (\j. matrix_inv(G w)$i$j * wan_xder j l0 w)) z)) = &0`
  (LABEL_TAC "E1P") THENL
   [MATCH_MP_TAC WAN_FUNDAMENTAL_CONT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC P2BW_SM_ADD THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BW_SM_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BW_SM_SUB THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `psi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2BW_REG_E1_INT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the weak identity, pointwise *)
  SUBGOAL_THEN
   `smooth_map_on om
      (\z. lift(((R:real^(N,1)finite_sum->real) z * sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) -
                 sqrt(det(G z)) *
                 sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N))
                           (\j. matrix_inv(G z)$i$j * wan_xder i (l0:real^(N,1)finite_sum->real) z *
                                wan_xder j l0 z))) / &2 -
                l0 z / (&2 * drop(sndcart z)) * sqrt(det(G z))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_SM_SUB THEN ASM_SIMP_TAC[P2BW_SM_MUL] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC P2BW_SM_MUL THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN MATCH_MP_TAC P2BW_SM_SUB THEN
    ASM_SIMP_TAC[P2BW_SM_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN om
        ==> wan_tder (l0:real^(N,1)finite_sum->real) z *
            sqrt(det((G:real^(N,1)finite_sum->real^N^N) z)) -
            ((R z * sqrt(det(G z)) -
              sqrt(det(G z)) *
              sum(1..dimindex(:N))
                 (\i. sum(1..dimindex(:N))
                        (\j. matrix_inv(G z)$i$j * wan_xder i l0 z * wan_xder j l0 z))) / &2 -
             l0 z / (&2 * drop(sndcart z)) * sqrt(det(G z))) = &0`
  (LABEL_TAC "E2P") THENL
   [MATCH_MP_TAC P2BW_FUND_POS_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC P2BW_SM_SUB THEN
      ASM_SIMP_TAC[P2BW_SM_MUL];
      X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BW_INT_DIFF_ZERO THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[P2BW_SM_MUL];
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "real_le")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_tder")) (concl th))) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `G:real^(N,1)finite_sum->real^N^N`;
                 `l0:real^(N,1)finite_sum->real`; `z:real^(N,1)finite_sum`] P2BW_SLICE_LLAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) SUBST1_TAC) THEN
  USE_THEN "E1P" (MP_TAC o C MP (ASSUME `(z:real^(N,1)finite_sum) IN om`) o
                  SPEC `z:real^(N,1)finite_sum`) THEN
  USE_THEN "E2P" (MP_TAC o C MP (ASSUME `(z:real^(N,1)finite_sum) IN om`) o
                  SPEC `z:real^(N,1)finite_sum`) THEN
  USE_THEN "SQ" (MP_TAC o C MP (ASSUME `(z:real^(N,1)finite_sum) IN om`) o
                 SPEC `z:real^(N,1)finite_sum`) THEN
  SUBGOAL_THEN `&0 < drop(sndcart(z:real^(N,1)finite_sum))` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "llap")) (rand(concl th)))) THEN
  ABBREV_TAC `S = sqrt(det((G:real^(N,1)finite_sum->real^N^N) z))` THEN
  ABBREV_TAC `L = llap (p2bw_slice (G:real^(N,1)finite_sum->real^N^N) z)
                       (p2bw_fslice (l0:real^(N,1)finite_sum->real) z) (fstcart z)` THEN
  ABBREV_TAC `Q = sum(1..dimindex(:N))
                    (\i. sum(1..dimindex(:N))
                           (\j. matrix_inv((G:real^(N,1)finite_sum->real^N^N) z)$i$j *
                                wan_xder i (l0:real^(N,1)finite_sum->real) z * wan_xder j l0 z))` THEN
  ABBREV_TAC `T0 = wan_tder (l0:real^(N,1)finite_sum->real) z` THEN
  ABBREV_TAC `t = drop(sndcart(z:real^(N,1)finite_sum))` THEN
  ABBREV_TAC `nn = &(dimindex(:N))` THEN
  ABBREV_TAC `l = (l0:real^(N,1)finite_sum->real) z` THEN
  ABBREV_TAC `r = (R:real^(N,1)finite_sum->real) z` THEN
  CONV_TAC REAL_FIELD);;

