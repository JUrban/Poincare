(* ========================================================================= *)
(* pc_pde_rdt: the Ricci-DeTurck existence of the PDE layer, part 1 (towards *)
(* the statement M1 of pc_pde_iface).  The iteration ball pde_rdt_ball, the  *)
(* chart form of the Ricci-DeTurck right-hand side, and                      *)
(* PDE_RDT_REMAINDER_SMOOTH: the remainder P_h(g) - tr_g Hess_h g of         *)
(* a family of metrics smooth up to the initial time is again such a family  *)
(* (PDE_LRDT_SYMBOL, PDE_LRDT_PULLBACK, PDE_SEELEY).                         *)
(*                                                                           *)
(* First the ball, locality and the chart form of pde_rdt_rhs.               *)
(* ========================================================================= *)

needs "src/pc_pde_mtor.ml";;
needs "src/pc_pde_mtime.ml";;
needs "src/pc_pde_rdt_symbol.ml";;

prioritize_real();;
type_invention_error := true;;

(* The ball of families with chart bounds and chart-wise H^s bound K on     *)
(* [a,a+tau) starting at g0.                                                *)

let pde_rdt_ball = new_definition
 `pde_rdt_ball (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (n0:num)
               (cs:num->(A->bool)#(A->real^N)) (ks:num->real^N->bool)
               (psi:num->A->real) (s:num) (K:real) (a:real) (tau:real)
               (g0:A->real^N^N) (g:real->A->real^N^N) <=>
    pde_tfam_from atlas a (a + tau) g /\
    (!x. x IN topspace top ==> g a x = g0 x) /\
    (!t. a <= t /\ t < a + tau
         ==> riemannian_metric atlas (g t) /\ pde_cbound atlas n0 cs ks 0 K (g t) /\
             pde_mnorm2 atlas n0 cs psi s (g t) <= K)`;;

(* The local Ricci-DeTurck operator only depends on the fields near y.      *)

let RDT_LDETURCK_LOCAL = prove
 (`!(H1:real^N->real^N^N) H2 G1 G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> H1 z = H2 z /\ G1 z = G2 z)
        ==> pde_ldeturck H1 G1 y = pde_ldeturck H2 G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_ldeturck] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. christoffel (G1:real^N->real^N^N) y u v = christoffel G2 y u v /\
          christoffel (H1:real^N->real^N^N) y u v = christoffel H2 y u v`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let RDT_LRDT_LOCAL = prove
 (`!(H1:real^N->real^N^N) H2 G1 G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> H1 z = H2 z /\ G1 z = G2 z)
        ==> pde_lrdt H1 G1 y = pde_lrdt H2 G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lrdt; pde_lricci_matrix; llie] THEN
  SUBGOAL_THEN `!z. z IN s ==> pde_ldeturck (H1:real^N->real^N^N) G1 z = pde_ldeturck H2 G2 z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_LDETURCK_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pde_ldeturck (H1:real^N->real^N^N) G1 y = pde_ldeturck H2 G2 y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (pde_ldeturck (H1:real^N->real^N^N) G1) (at y) =
    frechet_derivative (pde_ldeturck H2 G2) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. mderiv (G1:real^N->real^N^N) y w = mderiv G2 y w`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[mderiv] THEN GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. lricci (G1:real^N->real^N^N) y u v = lricci G2 y u v`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC LRICCI_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* The chart form of the Ricci-DeTurck right-hand side (naturality).         *)

let RDT_RHS_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N) (g:A->real^N^N) z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ riemannian_metric atlas g /\
     z IN IMAGE (SND c) (FST c)
     ==> metric_local atlas c (pde_rdt_rhs atlas h g) z =
         pde_lrdt (metric_local atlas c h) (metric_local atlas c g) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN FST (c:(A->bool)#(A->real^N)) /\ SND c x = (z:real^N) /\
                      chart_inv c z = x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `diffeomorphism_on (IMAGE (SND c) (FST c INTER FST c0))
                      (IMAGE (SND c0) (FST c INTER FST (c0:(A->bool)#(A->real^N))))
                      (chart_trans c c0) (chart_trans c0 c)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                  CHART_TRANS_DIFFEO) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `!W:A->real^N^N z'.
        z' IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))
        ==> metric_local atlas c W z' =
            mpullback (chart_trans c c0) (metric_local atlas c0 W) z'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_METRIC_LOCAL_TRANS_C THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans c (c0:(A->bool)#(A->real^N)) z = SND c0 x` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `SND (c:(A->bool)#(A->real^N)) (x:A) = (z:real^N)`)) THEN
    MATCH_MP_TAC PDM_CHART_TRANS_AT_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND c0) (FST (c:(A->bool)#(A->real^N)) INTER FST c0) SUBSET
                IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `pde_lrdt (mpullback (chart_trans c (c0:(A->bool)#(A->real^N)))
                          (metric_local atlas c0 (h:A->real^N^N)))
                       (mpullback (chart_trans c c0) (metric_local atlas c0 g)) z` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RDT_LRDT_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                      (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST (c:(A->bool)#(A->real^N)) INTER FST c0)`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
                 `chart_trans c (c0:(A->bool)#(A->real^N))`;
                 `chart_trans (c0:(A->bool)#(A->real^N)) c`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) h`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) g`; `z:real^N`]
                PDE_LRDT_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[riemannian_metric];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pde_rdt_rhs; chart_jac]);;

(* ------------------------------------------------------------------------- *)
(* PDE_RDT_REMAINDER_SMOOTH.  In a chart the remainder is                    *)
(* F(y, G, DG) (PDE_LRDT_SYMBOL); with the space-time extension of the      *)
(* family this is smooth on the open set where det G is nonzero, which     *)
(* contains [a,b) x U, and PDE_SEELEY extends it below a.                   *)
(* ------------------------------------------------------------------------- *)

let RDT_INDEX_SPLIT = prove
 (`!m n k. 1 <= k /\ k <= m * n
           ==> 1 <= 1 + (k - 1) DIV n /\ 1 + (k - 1) DIV n <= m /\
               1 <= 1 + (k - 1) MOD n /\ 1 + (k - 1) MOD n <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(k:num) <= m * n` THEN UNDISCH_TAC `1 <= (k:num)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k - 1) DIV n < m /\ (k - 1) MOD n < n` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ] THEN
    MP_TAC(SPECL [`m:num`; `n:num`] MULT_SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(k:num) <= m * n`; `1 <= (k:num)`] THEN ARITH_TAC;
    ASM_ARITH_TAC]);;

let RDT_MATRIX_ADD_SUB = prove
 (`!A B:real^N^M. (A + B) - A = B`,
  SIMP_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

(* The spatial Jacobian of a space-time map, as a smooth map.                *)

let RDT_SLICE_JAC = prove
 (`!(f:real^(1,N)finite_sum->real^P) w.
        f differentiable (at w)
        ==> matrix(frechet_derivative (\z. f(pastecart (fstcart w) z)) (at (sndcart w))) =
            (lambda i j. (partial_derivative (1 + j) f w)$i):real^N^P`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM partial_derivative] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^P`; `fstcart(w:real^(1,N)finite_sum)`;
                 `sndcart(w:real^(1,N)finite_sum)`; `i':num`] PDE_ST_SLICE_PARTIAL) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND]);;

let RDT_SLICE_JAC_SMOOTH = prove
 (`!S (f:real^(1,N)finite_sum->real^P).
        open S /\ smooth_map_on S f
        ==> smooth_map_on S
              (\w. (vectorize:real^N^P->real^(P,N)finite_prod)
                   (matrix(frechet_derivative (\z. f(pastecart (fstcart w) z))
                                              (at (sndcart w)))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w. (vectorize:real^N^P->real^(P,N)finite_prod)
                  ((lambda i j. (partial_derivative (1 + j) (f:real^(1,N)finite_sum->real^P) w)$i)
                   :real^N^P)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RDT_SLICE_JAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP (INST_TYPE [`:(P,N)finite_prod`,`:N`; `:(1,N)finite_sum`,`:M`]
                                 SMOOTH_MAP_ON_COMPONENTWISE)
    (ASSUME `open(S:real^(1,N)finite_sum->bool)`)] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:P)`; `dimindex(:N)`; `k:num`] RDT_INDEX_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD; LAMBDA_BETA] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* The remainder in a chart: F(y, G, DG).                                    *)

let RDT_REM_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N) (g:A->real^N^N)
    (Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
        ->real^(N,N)finite_prod) z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ riemannian_metric atlas g /\
     (!G y. metric_field (IMAGE (SND c) (FST c)) G /\ y IN IMAGE (SND c) (FST c)
            ==> pde_lrdt (metric_local atlas c h) G y =
                pde_ltrhess G (metric_local atlas c h) G y +
                (matrify:real^(N,N)finite_prod->real^N^N)
                (Fs (pastecart y
                     (pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (G y))
                      ((vectorize:real^N^(N,N)finite_prod->
                                  real^((N,N)finite_prod,N)finite_prod)
                       (matrix(frechet_derivative
                                ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                (at y)))))))) /\
     z IN IMAGE (SND c) (FST c)
     ==> (vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas c (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) z) =
         Fs (pastecart z
              (pastecart ((vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas c g z))
               ((vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
                (matrix(frechet_derivative
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c g)
                         (at z))))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[METRIC_LOCAL_SUB; ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`; `g:A->real^N^N`; `z:real^N`]
    RDT_RHS_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `h:A->real^N^N`; `g:A->real^N^N`;
                 `z:real^N`] PDE_ML_TRHESS_CHART) THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_TENSOR2_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                                `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[riemannian_metric]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RDT_MATRIX_ADD_SUB; VECTORIZE_MATRIFY]);;

(* PDE_RDT_REMAINDER_SMOOTH: the remainder of the Ricci-DeTurck operator is *)
(* a family of tensor fields smooth up to the initial time.                 *)

let PDE_RDT_REMAINDER_SMOOTH = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b h g.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
        (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
        pde_tfam_from atlas a b g
        ==> pde_tfam_from atlas a b
              (\t x. pde_rdt_rhs atlas h (g t) x - pde_trhess atlas (g t) h (g t) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a < b` THENL
   [ALL_TAC;
    REWRITE_TAC[pde_tfam_from] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `\w:real^(1,N)finite_sum. vec 0:real^(N,N)finite_prod`] THEN
    REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST] THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[pde_tfam_from] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (g:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fg:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`]
    PDE_LRDT_SYMBOL) THEN
  ANTS_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
       ->real^(N,N)finite_prod` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sym"))) THEN
  ABBREV_TAC
   `Jg = \w:real^(1,N)finite_sum.
           (vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
           (matrix(frechet_derivative
                    (\z. (Fg:real^(1,N)finite_sum->real^(N,N)finite_prod)
                         (pastecart (fstcart w) z)) (at (sndcart w))))` THEN
  ABBREV_TAC
   `Kg = \w:real^(1,N)finite_sum.
           pastecart (sndcart w)
             (pastecart ((Fg:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                        ((Jg:real^(1,N)finite_sum->real^((N,N)finite_prod,N)finite_prod) w))` THEN
  ABBREV_TAC `S0 = interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
  ABBREV_TAC
   `D = {pastecart y (pastecart P Q) |
           y IN (U:real^N->bool) /\
           ~(det((matrify:real^(N,N)finite_prod->real^N^N) P) = &0) /\
           Q IN (:real^((N,N)finite_prod,N)finite_prod)}` THEN
  ABBREV_TAC
   `Om = {w | w IN (S0:real^(1,N)finite_sum->bool) /\
              (Kg:real^(1,N)finite_sum->
                  real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum)
              w IN D}` THEN
  SUBGOAL_THEN `open (S0:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (S0:real^(1,N)finite_sum->bool)
      (Kg:real^(1,N)finite_sum->
          real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Kg" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`S0:real^(1,N)finite_sum->bool`; `\w:real^(1,N)finite_sum. w`;
                     `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[ETA_AX];
        EXPAND_TAC "Jg" THEN MATCH_MP_TAC RDT_SLICE_JAC_SMOOTH THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (D:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                         finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC PDE_SYM_DOMAIN_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (Om:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (Om:real^(1,N)finite_sum->bool)
      ((Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
           ->real^(N,N)finite_prod) o
       (Kg:real^(1,N)finite_sum->
           real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC
     `D:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Om" THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `S0:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Om" THEN SET_TAC[];
    ALL_TAC] THEN
  (* the half-closed slab lies in Om, with the chart identity *)
  SUBGOAL_THEN
   `!t y. a <= t /\ t < b /\ y IN U
          ==> pastecart (lift t) y IN (Om:real^(1,N)finite_sum->bool) /\
              ((Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum
                   ->real^(N,N)finite_prod) o
               (Kg:real^(1,N)finite_sum->
                   real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)finite_sum))
              (pastecart (lift t) y) =
              (vectorize:real^N^N->real^(N,N)finite_prod)
              (metric_local atlas c
                 (\x. pde_rdt_rhs atlas h ((g:real->A->real^N^N) t) x -
                      pde_trhess atlas (g t) h (g t) x) y)`
  (LABEL_TAC "slab") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field U (metric_local atlas (c:(A->bool)#(A->real^N))
                                   ((g:real->A->real^N^N) t))` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (lift t) y IN (S0:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "S0" THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(Fg:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y) =
      (vectorize:real^N^N->real^(N,N)finite_prod)
      (metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t) y)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(Jg:real^(1,N)finite_sum->real^((N,N)finite_prod,N)finite_prod) (pastecart (lift t) y) =
      (vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
      (matrix(frechet_derivative
               ((vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t))
               (at y)))`
    ASSUME_TAC THENL
     [EXPAND_TAC "Jg" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Om" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Kg" THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[IN_ELIM_THM; SNDCART_PASTECART; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC
       [`y:real^N`;
        `(vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t) y)`;
        `(vectorize:real^N^(N,N)finite_prod->real^((N,N)finite_prod,N)finite_prod)
         (matrix(frechet_derivative
                  ((vectorize:real^N^N->real^(N,N)finite_prod) o
                   metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t))
                  (at y)))`] THEN
      ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                     `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN EXPAND_TAC "Kg" THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RDT_REM_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "sym" MATCH_MP_TAC THEN
      UNDISCH_TAC `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                                (G:real^N->real^N^N)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y':real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Seeley *)
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                 `\t y. ((Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                             finite_sum->real^(N,N)finite_prod) o
                         (Kg:real^(1,N)finite_sum->
                             real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                             finite_sum))
                        (pastecart (lift t) (y:real^N))`] PDE_SEELEY) THEN
  SUBGOAL_THEN
   `(\w:real^(1,N)finite_sum.
       (\t y. ((Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                   finite_sum->real^(N,N)finite_prod) o
               (Kg:real^(1,N)finite_sum->
                   real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                   finite_sum))
              (pastecart (lift t) (y:real^N))) (drop(fstcart w)) (sndcart w)) =
    Fs o Kg`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; PASTECART_FST_SND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{pastecart (lift t) y | a <= t /\ t < b /\ y IN U} SUBSET (Om:real^(1,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[pde_upto_classical] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Om:real^(1,N)finite_sum->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Om:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1] THEN
      MAP_EVERY X_GEN_TAC [`t1:real^1`; `y1:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `pastecart (t1:real^1) (y1:real^N) = pastecart (lift(drop t1)) y1`
      SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
      USE_THEN "slab" (MP_TAC o SPECL [`drop(t1:real^1)`; `y1:real^N`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `drop(lift a) < drop(t1:real^1)` THEN
        UNDISCH_TAC `drop(t1:real^1) < drop(lift b)` THEN
        REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      EXISTS_TAC `iterated_partial l
                   ((Fs:real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                        finite_sum->real^(N,N)finite_prod) o
                    (Kg:real^(1,N)finite_sum->
                        real^(N,((N,N)finite_prod,((N,N)finite_prod,N)finite_prod)finite_sum)
                        finite_sum))` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `Om:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':real` (X_CHOOSE_THEN
    `F':real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e':real`; `F':real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The step of the iteration exists (PDE_MLIN_STATEMENT with                 *)
(* coefficients g, background h, forcing the remainder, initial value h).   *)
(* ------------------------------------------------------------------------- *)

let RDT_STEP_EXISTS = prove
 (`!(u:A->bool) (n:N->bool).
     PDE_MLIN_STATEMENT u n
     ==> !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b h g.
           hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
           a < b /\ riemannian_metric atlas h /\
           (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
           pde_tfam_from atlas a b g
           ==> ?v. pde_rdt_step (top,atlas) a b h g v`,
  REWRITE_TAC[PDE_MLIN_STATEMENT; pde_rdt_step] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RIEMANNIAN_METRIC_TENSOR2_SMOOTH] THEN
  MATCH_MP_TAC PDE_RDT_REMAINDER_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

