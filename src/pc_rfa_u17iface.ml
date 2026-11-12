(* ========================================================================= *)
(* Unit pc_rfa_u17iface: the statement constants of the two parts of the     *)
(* proof of Hamilton's trace Harnack inequality                              *)
(* (P2B_REQ_RFA_HARNACK_STATEMENT): the pointwise algebra of the matrix      *)
(* Harnack quadratic (RFA_HARNACK_ALG_STATEMENT, proved in pc_rfa_halg), and *)
(* the barrier at infinity for the maximum principle on complete flows with  *)
(* bounded Ricci curvature (RFA_HARNACK_BARRIER_STATEMENT, proved in         *)
(* pc_rfa_hbar).  Statement constants only, with type checks and cheap       *)
(* sanity theorems.                                                          *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The statements.                                                           *)
(* ========================================================================= *)

(* The algebra.  Hamilton's matrix Harnack quadratic and its reaction term  *)
(* in an orthonormal frame, for arrays indexed by 1..n (CLN, Hamilton's      *)
(* Ricci Flow, (10.57) and (10.63), with the sign convention of CLN): for a  *)
(* 2-form U (antisymmetric array) and a 1-form W,                            *)
(*   Z(U,W) = M_ab W_a W_b + 2 P_abc U_ab W_c + R_abcd U_ab U_dc,           *)
(*   J(U,W) = 2 R_acdb M_cd W_a W_b - 2 P_acd P_bdc W_a W_b                 *)
(*            + 8 R_adec P_dbe U_ab W_c + 4 R_aefc R_befd U_ab U_cd.        *)

let rfa_hz = new_definition
 `rfa_hz (n:num) (R:num->num->num->num->real) (P:num->num->num->real)
         (M:num->num->real) (U:num->num->real) (W:num->real) =
    sum(1..n) (\a. sum(1..n) (\b. M a b * W a * W b)) +
    &2 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c.
           P a b c * U a b * W c))) +
    sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
      R a b c d * U a b * U d c))))`;;

let rfa_hj = new_definition
 `rfa_hj (n:num) (R:num->num->num->num->real) (P:num->num->num->real)
         (M:num->num->real) (U:num->num->real) (W:num->real) =
    &2 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           R a c d b * M c d * W a * W b)))) -
    &2 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           P a c d * P b d c * W a * W b)))) +
    &8 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum(1..n) (\e. R a d e c * P d b e * U a b * W c))))) +
    &4 * sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d.
           sum(1..n) (\e. sum(1..n) (\f.
             R a e f c * R b e f d * U a b * U c d))))))`;;

(* The algebraic lemma (CLN p. 413, the sum-of-squares decomposition         *)
(* (10.64)): if R has the symmetries of a curvature tensor (antisymmetric in *)
(* each pair, pair-symmetric; no Bianchi identity is assumed, so perturbed   *)
(* tensors are allowed), P is antisymmetric in its first two slots and M is  *)
(* symmetric, and Z(U,W) >= 0 for all U, W, then J(U,W) >= 0 for all U, W.   *)
(* Stated for n = dimindex(:N), so that the proof can use matrices over      *)
(* real^N; the Harnack inequality uses N = 3.  The proof (pc_rfa_halg): Z is *)
(* a positive semidefinite form on R^n plus the antisymmetric arrays, so     *)
(* Z(U,W) is a sum over N of the squares of X^N_a W_a + Y^N_ab U_ab with Y^N *)
(* antisymmetric; then R_abcd, P_abc and M_ab are the sums of Y^N_ab Y^N_dc, *)
(* Y^N_ab X^N_c and X^N_a X^N_b, and J is the sum over N, N' of the squares  *)
(* of A(N,N') - A(N',N) + 2 B(N,N'), A(N,N') = W_a Y^N_ac X^N'_c,            *)
(* B(N,N') = U_ab Y^N_ad Y^N'_db.                                            *)

let RFA_HARNACK_ALG_STATEMENT = new_definition
 `RFA_HARNACK_ALG_STATEMENT (u:N->bool) <=>
    !(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
       (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                  R a b c d = R c d a b) /\
       (!a b c. P a b c = --(P b a c)) /\
       (!a b. M a b = M b a) /\
       (!(U:num->num->real) (W:num->real).
          (!a b. U a b = --(U b a)) ==> &0 <= rfa_hz (dimindex(:N)) R P M U W)
       ==> !(U:num->num->real) (W:num->real).
             (!a b. U a b = --(U b a)) ==> &0 <= rfa_hj (dimindex(:N)) R P M U W`;;

(* The barrier.  The barrier at infinity for the maximum principle of        *)
(* pc_rfa_hmax on a complete 3D flow with |Ric| <= K on [t1,t2], on the      *)
(* joinable class of a base point x0.  A function psi >= 1, jointly          *)
(* continuous, proper on the class (sublevel sets lie in compact sets), with *)
(* a backward-in-time growth bound and, at every time and point and in every *)
(* atlas chart at the point, a smooth upper barrier q touching psi there     *)
(* with Lap q and |grad q|^2 at most C psi and C psi^2.  The witness of      *)
(* pc_rfa_hbar: psi t x = 1 + d_g(t)(x0,x)^2, from CMP_LAPLACIAN_BARRIER_SQ  *)
(* (pc_cmp_hess; Ric >= -2 (K/2) g), RFA_METRIC_EQUIV (pc_rfa_shi),          *)
(* MFD_LENGTH_METRIC_COMPARE (pc_grg_dist2), MFD_DIST_CONTINUOUS             *)
(* (pc_grg_distcont), LLAP_PULLBACK and LGRAD2_PULLBACK (pc_lrg_lap) for the *)
(* chart change, and mfd_complete for the compact sublevel sets.             *)

let RFA_HARNACK_BARRIER_STATEMENT = new_definition
 `RFA_HARNACK_BARRIER_STATEMENT (u:A->bool) <=>
    !top atlas (g:real->A->real^3^3) a b t1 t2 K x0.
       hausdorff_space (top:A topology) /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       a < t1 /\ t1 < t2 /\ t2 < b /\
       (!t. t1 <= t /\ t <= t2 ==> mfd_complete (top,atlas) (g t)) /\
       (!t x v. t1 <= t /\ t <= t2 /\ x IN topspace top
                ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v))) /\
       x0 IN topspace top
       ==> ?C (psi:real->A->real).
             (!t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
                    ==> &1 <= psi t x) /\
             continuous_map
               (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                              (subtopology top {x | mfd_joinable (top,atlas) x0 x}),
                euclideanreal)
               (\z. psi (FST z) (SND z)) /\
             (!B. ?S. compact_in top S /\
                      !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
                            psi t x <= B
                            ==> x IN S) /\
             (!t x. t1 < t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
                    ==> ?d. &0 < d /\
                            !s. t1 <= s /\ t - d < s /\ s <= t
                                ==> psi s x <= psi t x + C * (t - s) * psi t x) /\
             (!t x c. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
                      c IN atlas /\ x IN FST c
                      ==> ?W (q:real^3->real).
                            open W /\ SND c x IN W /\ W SUBSET IMAGE (SND c) (FST c) /\
                            smooth_map_on W (\y. lift(q y)) /\
                            (!y. y IN W ==> psi t (chart_inv c y) <= q y) /\
                            q (SND c x) = psi t x /\
                            llap (metric_local atlas c (g t)) q (SND c x) <= C * psi t x /\
                            lgrad2 (metric_local atlas c (g t)) q (SND c x) <=
                            C * psi t x pow 2)`;;


(* ========================================================================= *)
(* Type checks and sanity theorems.                                          *)
(* ========================================================================= *)

let _ =
  if type_of (rator `RFA_HARNACK_ALG_STATEMENT (u:N->bool)`) = `:(N->bool)->bool` &&
     type_of (rator `RFA_HARNACK_BARRIER_STATEMENT (w:A->bool)`) = `:(A->bool)->bool` &&
     type_of `rfa_hz` =
       `:num->(num->num->num->num->real)->(num->num->num->real)->(num->num->real)->
         (num->num->real)->(num->real)->real` &&
     type_of `rfa_hj` = type_of `rfa_hz`
  then print_string "RFA_U17IFACE type check OK\n"
  else failwith "RFA_U17IFACE type check FAILED";;

(* Degenerate case: zero tensors give Z = J = 0.                             *)

let RFA_HZ_HJ_ZERO = prove
 (`!n (U:num->num->real) (W:num->real).
     rfa_hz n (\a b c d. &0) (\a b c. &0) (\a b. &0) U W = &0 /\
     rfa_hj n (\a b c d. &0) (\a b c. &0) (\a b. &0) U W = &0`,
  REWRITE_TAC[rfa_hz; rfa_hj; REAL_MUL_LZERO; SUM_0; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_SUB_REFL]);;

(* Teeth: for n = 2, data with the required symmetries (but Z indefinite)   *)
(* can have J < 0, so the conclusion of the algebraic lemma has content.     *)

let RFA_HARNACK_ALG_TEETH = prove
 (`?(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real)
    (U:num->num->real) (W:num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c)) /\ (!a b. M a b = M b a) /\
     (!a b. U a b = --(U b a)) /\
     rfa_hj (dimindex(:2)) R P M U W < &0`,
  MAP_EVERY EXISTS_TAC
   [`\a:num b:num c:num d:num. &0`;
    `\a b c. if a = 1 /\ b = 2 /\ c = 1 then &1
             else if a = 2 /\ b = 1 /\ c = 1 then --(&1) else &0`;
    `\a:num b:num. &0`; `\a:num b:num. &0`;
    `\a. if a = 2 then &1 else &0`] THEN
  REWRITE_TAC[REAL_NEG_0] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`a = 1`; `a = 2`; `b = 1`; `b = 2`; `c = 1`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hj; DIMINDEX_2; SUM_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Non-vacuity: for n = 2, the curvature-type tensor of the 2-form e1^e2,    *)
(* P = 0 and M = e1 e1 satisfy all hypotheses (Z(U,W) is W_1^2 plus a      *)
(* square), and J at (U,W) = (0,e2) is 2.                                    *)

let RFA_HARNACK_ALG_EXAMPLE = prove
 (`?(R:num->num->num->num->real) (P:num->num->num->real) (M:num->num->real).
     (!a b c d. R a b c d = --(R b a c d) /\ R a b c d = --(R a b d c) /\
                R a b c d = R c d a b) /\
     (!a b c. P a b c = --(P b a c)) /\ (!a b. M a b = M b a) /\
     (!(U:num->num->real) (W:num->real).
        (!a b. U a b = --(U b a)) ==> &0 <= rfa_hz (dimindex(:2)) R P M U W) /\
     rfa_hj (dimindex(:2)) R P M (\a b. &0) (\a. if a = 2 then &1 else &0) = &2`,
  ABBREV_TAC `y = \a b. if a = 1 /\ b = 2 then &1
                        else if a = 2 /\ b = 1 then --(&1) else &0` THEN
  SUBGOAL_THEN `!a b. (y:num->num->real) a b = --(y b a)` (LABEL_TAC "ya") THENL
   [EXPAND_TAC "y" THEN REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`a = 1`; `a = 2`; `b = 1`; `b = 2`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(U:num->num->real) (W:num->real).
      rfa_hz (dimindex(:2)) (\a b c d. (y:num->num->real) a b * y d c) (\a b c. &0)
             (\a b. if a = 1 /\ b = 1 then &1 else &0) U W =
      W 1 pow 2 + (U 1 2 - U 2 1) pow 2`
  (LABEL_TAC "hz") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hz; DIMINDEX_2; SUM_2] THEN
    EXPAND_TAC "y" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\a b c d. (y:num->num->real) a b * y d c`;
    `\a:num b:num c:num. &0`;
    `\a b. if a = 1 /\ b = 1 then &1 else &0`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "ya" (fun th -> MP_TAC(SPECL [`a:num`; `b:num`] th) THEN
                             MP_TAC(SPECL [`c:num`; `d:num`] th)) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_NEG_0]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 1` THEN ASM_CASES_TAC `b = 1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "hz" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hj; DIMINDEX_2; SUM_2] THEN EXPAND_TAC "y" THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

