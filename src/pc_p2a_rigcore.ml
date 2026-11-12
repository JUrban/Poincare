(* ========================================================================= *)
(* Unit pc_p2a_rigcore: step R1 of the FL5R route.  P2AU_RIGID_R1 proves     *)
(* P2AU_RIGID_R2_STATEMENT u ==> P2AU_RIGID_CORE_STATEMENT u                 *)
(* (pc_p2a_rigstmt): the equality case of the reduced-volume monotonicity    *)
(* along a single L-geodesic.                                                *)
(*                                                                           *)
(* The monotonicity of pc_p2a_lric, pc_p2a_ljac and pc_p2a_lmono rests on    *)
(* the comparison function gw of P2AL_WOK_GW_DERIV, gw' <= 0, which comes    *)
(* from P2AL_RICCATI_BOUND.  Kept as an identity, that bound reads           *)
(*   gw'(s) = -s^2 tr(M^2),   M = S - (I/s - 2 s Ric),   S = B Y^-1 + Gamma(A) *)
(* (P2AU_RICCATI_DEFECT, P2AU_GFUN_DERIV_EQ, P2AU_WOK_GW_DERIV_EQ), and      *)
(* tr(M^2) = |M|^2_G vanishes only for M = 0 (P2AU_TRACE_SQ_EQ0).  Along a  *)
(* geodesic where rvi(s^2) is locally constant, P2AL_WOK_RVI_DERIV gives    *)
(* gw = 0 near s, so M = 0 there (P2AU_WIN_SHAPE, P2AU_SHAPE_FROM_CONST).    *)
(* If rvi(tau0,Z) is the Gaussian then, by P2A_RVI_MONO and the Gaussian     *)
(* bound P2A_T81_RVI_GAUSS, rvi(tau,Z) is the Gaussian for all tau in        *)
(* (0,tau0]; this holds for almost every Z in Smin(tau0) under the CORE      *)
(* hypotheses, which gives the hypotheses of R2 (P2AU_RIGID_R1).             *)
(* Corollary P2AU_FLOW_RV_RIGID_R2: R2 and W3 imply FL5R.                    *)
(* ========================================================================= *)

needs "src/pc_p2a_rigid.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The equality case of the trace inequality, and the defect                 *)
(* identity behind P2AL_RICCATI_BOUND.  With X = I/s - 2 s Ric and M = S - X, *)
(*   s^2 (-tr(S^2) - 4 s tr(Ric S))                                          *)
(*     = -2 s tr S + n - 4 s^2 R + 4 s^4 |Ric|^2 - s^2 tr(M^2),              *)
(* and tr(M^2) = 0 forces M = 0 when G M is symmetric (G positive definite;  *)
(* the square-root argument of P2AL_TRACE_PSD_SQ with TRACE_COVARIANCE_EQ_0).*)
(* ------------------------------------------------------------------------- *)

let P2AU_TRACE_SQ_EQ0 = prove
 (`!G M:real^N^N.
     positive_definite G /\ symmetric_matrix (G ** M) /\ trace(M ** M) = &0
     ==> M = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(G:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[POSITIVE_DEFINITE_IMP_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `positive_semidefinite(matrix_inv(G:real^N^N))` MP_TAC THENL
   [REWRITE_TAC[POSITIVE_SEMIDEFINITE_INV] THEN
    ASM_SIMP_TAC[POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [POSITIVE_SEMIDEFINITE_SQRT_EQ]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `transp(Q:real^N^N) = Q` ASSUME_TAC THENL
   [ASM_MESON_TAC[POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX; symmetric_matrix]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(Q:real^N^N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `G:real^N^N` INVERTIBLE_MATRIX_INV) THEN
    ASM_REWRITE_TAC[INVERTIBLE_MATRIX_MUL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((Q:real^N^N) ** Q) ** (G:real^N^N) ** (M:real^N^N) = M` ASSUME_TAC THENL
   [UNDISCH_TAC `matrix_inv(G:real^N^N) = Q ** Q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K:real^N^N. transp K = K
                 ==> trace((((Q:real^N^N) ** Q) ** K) ** ((Q ** Q) ** K)) =
                     trace(transp(Q ** K ** Q) ** (Q ** K ** Q))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`Q:real^N^N`; `(Q:real^N^N) ** (K:real^N^N) ** Q ** Q ** K`]
                  TRACE_MUL_SYM) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^N^N) ** ((G:real^N^N) ** (M:real^N^N)) ** Q = mat 0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM TRACE_COVARIANCE_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(G:real^N^N) ** (M:real^N^N)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[symmetric_matrix]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!K:real^N^N. (Q:real^N^N) ** K ** Q = mat 0 ==> K = mat 0` MP_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\X:real^N^N. matrix_inv(Q:real^N^N) ** X ** matrix_inv Q`) THEN
    BETA_TAC THEN REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; MATRIX_MUL_ASSOC] THEN
    MP_TAC(MATCH_MP MATRIX_INV (ASSUME `invertible(Q:real^N^N)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; MATRIX_MUL_LID] THEN
                         REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; th; MATRIX_MUL_RID]);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(G:real^N^N) ** (M:real^N^N)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `((Q:real^N^N) ** Q) ** (G:real^N^N) ** (M:real^N^N) = M` THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RZERO] THEN MESON_TAC[]);;

let P2AU_RICCATI_DEFECT = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) s.
     metric_field U G /\ y IN U /\ &0 < s
     ==> s pow 2 * (--trace(S ** S) - &4 * s * trace(matrix(p2a_lricop G y) ** S)) =
         --(&2 * s) * trace S + &(dimindex(:N)) - &4 * s pow 2 * lscalar G y +
         &4 * s pow 4 * trace(matrix(p2a_lricop G y) ** matrix(p2a_lricop G y)) -
         s pow 2 * trace((S - (inv(s) %% mat 1 - (&2 * s) %% matrix(p2a_lricop G y))) **
                         (S - (inv(s) %% mat 1 - (&2 * s) %% matrix(p2a_lricop G y))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_RMUL; MATRIX_MUL_LMUL;
              MATRIX_MUL_LID; MATRIX_MUL_RID; MATRIX_CMUL_ASSOC; TRACE_SUB; TRACE_CMUL;
              TRACE_I] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^N^N`; `matrix(p2a_lricop (G:real^N->real^N^N) y)`] TRACE_MUL_SYM) THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

(* G X is symmetric for X = I/s - 2 s Ric (from P2AL_RICCATI_BOUND).        *)

let P2AU_GX_SYM = prove
 (`!U (G:real^N->real^N^N) y s.
     metric_field U G /\ y IN U
     ==> symmetric_matrix(G y ** (inv(s) %% mat 1 - (&2 * s) %% matrix(p2a_lricop G y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `symmetric_matrix((G:real^N->real^N^N) y ** matrix(p2a_lricop G y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[symmetric_matrix; CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN
  MATCH_MP_TAC SYMMETRIC_MATRIX_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC SYMMETRIC_MATRIX_CMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[symmetric_matrix] THEN ASM_MESON_TAC[metric_field]);;

(* ------------------------------------------------------------------------- *)
(* The comparison function has derivative exactly -s^2 tr(M^2)               *)
(* (P2AL_GFUN_DERIV with the bound kept as an identity; no symmetry needed), *)
(* at chart level and for the window function p2al_gw.                       *)
(* ------------------------------------------------------------------------- *)

let P2AU_GFUN_DERIV_EQ = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) sa sb tt s (y:real^1->real^N) (A:real^1->real^N)
    (Y:real->real^N^N) (B:real->real^N^N) (Lf:real->real).
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s /\ s < sb /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     &0 < s /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)) /\
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize(B s)) (at (lift s)) /\
     ((\v. vectorize(B(drop v))) has_vector_derivative
        vectorize(matrix(frechet_derivative (\z. p2a_lacc Gt tt s z (A(lift s)))
                                            (at (y(lift s)))) ** Y s +
                  matrix(frechet_derivative (\w. p2a_lacc Gt tt s (y(lift s)) w)
                                            (at (A(lift s)))) ** B s)) (at (lift s)) /\
     ~(det(Y s) = &0) /\
     (Lf has_real_derivative p2a_llag Gt tt s (y(lift s)) (A(lift s))) (atreal s)
     ==> ((\x. x pow 2 * (trace(B x ** matrix_inv(Y x)) +
                          p2al_tg (Gt(tt - x pow 2)) (y(lift x)) (A(lift x))) -
               (&(dimindex(:N)) * x - x pow 3 * lscalar (Gt(tt - x pow 2)) (y(lift x)) +
                x * (A(lift x) dot (Gt(tt - x pow 2) (y(lift x)) ** A(lift x))) / &4 -
                Lf x / &2))
          has_real_derivative
          --(s pow 2) *
          trace(((B s ** matrix_inv(Y s) +
                  matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)))) -
                 (inv(s) %% mat 1 -
                  (&2 * s) %% matrix(p2a_lricop (Gt(tt - s pow 2)) (y(lift s))))) **
                ((B s ** matrix_inv(Y s) +
                  matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)))) -
                 (inv(s) %% mat 1 -
                  (&2 * s) %% matrix(p2a_lricop (Gt(tt - s pow 2)) (y(lift s)))))))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `sa:real`; `sb:real`; `tt:real`; `s:real`; `y:real^1->real^N`;
                 `A:real^1->real^N`; `Y:real->real^N^N`; `B:real->real^N^N`] P2AL_RICCATI_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `sa:real`; `sb:real`; `tt:real`; `s:real`; `y:real^1->real^N`;
                 `(A:real^1->real^N)(lift s)`] P2AL_SCALAR_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `s:real`; `y:real^1->real^N`; `A:real^1->real^N`]
                P2AL_ENERGY_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun thE -> FIRST_X_ASSUM(fun thR -> FIRST_X_ASSUM(fun thS ->
    FIRST_X_ASSUM(fun thL ->
      MP_TAC(BETA_RULE(MATCH_MP P2AL_GCOMB_DERIV
        (CONJ thS (CONJ thR (CONJ thE thL))))))))) THEN
  DISCH_THEN(MP_TAC o SPEC `&(dimindex(:N))`) THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC P2AL_HRD_EQ THEN EXISTS_TAC (rand(rator(concl th))) THEN
                       REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `A0 = (A:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `S = (B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s) +
                  matrix(christoffel (G:real^N->real^N^N) y0 A0)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `S:real^N^N`; `s:real`]
                P2AU_RICCATI_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] P2AL_RICM_SQ_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `trace(S:real^N^N) = trace((B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s)) +
                                    p2al_tg (G:real^N->real^N^N) y0 A0`
  SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[TRACE_ADD; P2AL_TG_MATRIX]; ALL_TAC] THEN
  REWRITE_TAC[p2a_llag] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sig = trace((B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s)) +
                    p2al_tg (G:real^N->real^N^N) y0 A0` THEN
  REAL_ARITH_TAC);;

(* The defect matrix M = S - (I/s - 2 s Ric) of a window at (Z,s).          *)

let p2au_wdef = new_definition
 `p2au_wdef (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
            (Z:real^N) (s:real) =
    (p2al_jb V tt s1 r W b' U phi Phi Z s ** matrix_inv(p2al_jy V tt s1 r W b' U phi Phi Z s) +
     matrix(christoffel (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                        (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                        (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))) -
    (inv(s) %% mat 1 -
     (&2 * s) %% matrix(p2a_lricop (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                                   (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))))`;;

let P2AU_WOK_GW_DERIV_EQ = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> ((\s'. p2al_gw V tt x s1 r W b' U phi Phi Z0 s') has_real_derivative
          --(s pow 2) * trace(p2au_wdef V tt s1 r W b' U phi Phi Z0 s **
                              p2au_wdef V tt s1 r W b' U phi Phi Z0 s))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LWIN_JACOBI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `s:real`]
                P2AL_LTIL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_LSINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b':real`;
    `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `s1 - r`; `s1 + r`; `tt:real`;
    `s:real`;
    `\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
    `\v. sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
    `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0`;
    `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0`;
    `\s'. p2a_Ltil (V:p2alv) tt (x:A) (s' pow 2) Z0`] P2AU_GFUN_DERIV_EQ) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2al_gw; p2au_wdef]);;

(* ------------------------------------------------------------------------- *)
(* The soliton shape where rvi is locally constant.  If rvi(s^2,Z) is        *)
(* constant for s near s0, then in every regular window at (Z,s0) the window *)
(* function gw vanishes near s0 (P2AL_WOK_RVI_DERIV: d/ds rvi(s^2) = rvi gw  *)
(* / s^2, rvi > 0), so gw'(s0) = 0 = -s0^2 tr(M^2) and M = 0                 *)
(* (P2AU_TRACE_SQ_EQ0; G M symmetric by P2AL_WOK_SYM and P2AU_GX_SYM).       *)
(* ------------------------------------------------------------------------- *)

let P2AU_QUOT_ZERO = prove
 (`!a g s. &0 < a /\ &0 < s /\ a * g / s pow 2 = &0 ==> g = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0; REAL_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2AU_WIN_SHAPE = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s0 d.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s0 /\ s0 < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s0 /\ Z0 IN p2a_Ldom V tt x b /\ s0 pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s0) = &0) /\ &0 < d /\
     (!s. abs(s - s0) < d ==> p2a_rvi V tt x (s pow 2) Z0 = p2a_rvi V tt x (s0 pow 2) Z0)
     ==> p2au_wdef V tt s1 r W b' U phi Phi Z0 s0 = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s0:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th)) THEN
    X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1"))
      (last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s0:real`]
                P2AL_WIN_DETNZ_NBHD) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E2"))) THEN
  SUBGOAL_THEN `s0 < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `k = min (min e1 e2) (min d (sqrt b - s0)) / &2` THEN
  SUBGOAL_THEN `&0 < k /\ k < e1 /\ k < e2 /\ &2 * k <= d /\ k < sqrt b - s0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* gw vanishes near s0 *)
  SUBGOAL_THEN
   `!s. abs(s - s0) < k
        ==> p2al_gw (V:p2alv) tt (x:A) s1 r W b' U (phi:A->real^N) Phi Z0 s = &0`
  (LABEL_TAC "GW0") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "E1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "E2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_WOK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 <= b` (fun th -> SIMP_TAC[th; SQRT_POW_2; REAL_LE_REFL]) THEN
        MP_TAC(SPEC `s0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                   `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_WOK_RVI_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "RD") THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_WOK_RVI_POS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `((\s'. p2a_rvi (V:p2alv) tt (x:A) (s' pow 2) Z0) has_real_derivative &0) (atreal s)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\s':real. p2a_rvi (V:p2alv) tt (x:A) (s0 pow 2) Z0`; `k:real`] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `s':real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `d:real` (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "RD" (fun th1 -> DISCH_THEN(fun th2 ->
      MP_TAC(MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL (CONJ th1 th2)))) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2AU_QUOT_ZERO THEN
    MAP_EVERY EXISTS_TAC [`p2a_rvi (V:p2alv) tt (x:A) (s pow 2) Z0`; `s:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* hence gw'(s0) = 0 *)
  SUBGOAL_THEN
   `((\s'. p2al_gw (V:p2alv) tt (x:A) s1 r W b' U (phi:A->real^N) Phi Z0 s')
     has_real_derivative &0) (atreal s0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s':real. &0`; `k:real`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "GW0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s0:real`]
                P2AU_WOK_GW_DERIV_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th1 -> DISCH_THEN(fun th2 ->
    MP_TAC(MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL (CONJ th1 th2)))) THEN
  REWRITE_TAC[REAL_ARITH `&0 = --x * t <=> x * t = &0`; REAL_ENTIRE; REAL_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~(s0 = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC P2AU_TRACE_SQ_EQ0 THEN
  EXISTS_TAC `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s0 pow 2)
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s0))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_METRIC_PD THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[lricci_flow];
    REWRITE_TAC[p2au_wdef] THEN ONCE_REWRITE_TAC[MATRIX_SUB_LDISTRIB] THEN
    MATCH_MP_TAC SYMMETRIC_MATRIX_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AL_WOK_SYM THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `b:real`; `a':real`; `N:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2AU_GX_SYM THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[lricci_flow]]]);;

let P2AU_SHAPE_FROM_CONST = prove
 (`!(V:p2alv) tt (x:A) b (Z:real^N) s0 d.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ s0 pow 2 < b /\ &0 < d /\
     (!s. abs(s - s0) < d ==> p2a_rvi V tt x (s pow 2) Z = p2a_rvi V tt x (s0 pow 2) Z)
     ==> p2au_soliton_shape V tt x Z s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2au_soliton_shape] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                       `phi:A->real^N`; `N:real^N->bool`;
                       `Phi:real^N->real^(N,N)finite_sum`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`; `d:real`]
                P2AU_WIN_SHAPE) THEN
  ASM_REWRITE_TAC[p2au_wdef; MATRIX_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* R2 ==> CORE.  For Z in Smin(tau0) with rvi(tau0,Z) equal to the Gaussian, *)
(* rvi(tau,Z) is the Gaussian for every tau in (0,tau0] (P2A_RVI_MONO and    *)
(* P2A_T81_RVI_GAUSS), so rvi(s^2,Z) is locally constant for s^2 < tau0 and  *)
(* the Jacobi data have the soliton shape there (P2AU_RIGID_SHAPE_FLOW).     *)
(* Under the CORE hypotheses these Z form a conull set E inside Smin(tau0),  *)
(* which is the input of R2 (P2AU_RIGID_R1).                                 *)
(* ------------------------------------------------------------------------- *)

let P2AU_RIGID_SHAPE_FLOW = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau0 Z s.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\
     Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
     (!tau1. &0 < tau1 /\ tau1 <= tau0
             ==> p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau1 Z =
                 &8 * exp(--(p2a_znorm2 (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p Z))) /\
     &0 < s /\ s pow 2 < tau0
     ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN
   `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) b) /\
    p2a_bsmooth V p b /\ (Z:real^3) IN p2a_Ldom V b p tau0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC
     `(Z:real^3) IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b p tau0` THEN
    SIMP_TAC[p2a_Smin; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < sqrt tau0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau0` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2AU_SHAPE_FROM_CONST) THEN
  MAP_EVERY EXISTS_TAC [`tau0:real`; `min s (sqrt tau0 - s)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s':real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s' pow 2 /\ s' pow 2 <= tau0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau0 pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 <= tau0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let P2AU_RIGID_R1 = prove
 (`!u:A->bool. P2AU_RIGID_R2_STATEMENT u ==> P2AU_RIGID_CORE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2AU_RIGID_R2_STATEMENT; P2AU_RIGID_CORE_STATEMENT] THEN
  DISCH_THEN(fun r2 -> DISCH_THEN(fun w3 -> ASSUME_TAC(MP r2 w3))) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau0:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* equality at tau0 gives equality for all tau in (0,tau0] *)
  SUBGOAL_THEN
   `!Z tau1.
      Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                    b p tau0 /\
      p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 Z =
      &8 * exp(--(p2a_znorm2 (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z)) /\
      &0 < tau1 /\ tau1 <= tau0
      ==> p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau1 Z =
          &8 * exp(--(p2a_znorm2 (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z))`
  (LABEL_TAC "ALL") THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_T81_RVI_GAUSS THEN EXISTS_TAC `tau0:real` THEN
      REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b])
                                         (g:real->A->real^3^3)) b p tau0 Z` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      MP_TAC(ISPEC `u:A->bool` P2A_RVI_MONO) THEN REWRITE_TAC[P2A_RVI_MONO_STATEMENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `tau0:real` THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `p:A`; `tau0:real`;
    `{Z | Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b])
                                       (g:real->A->real^3^3)) b p tau0 /\
          p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 Z =
          &8 * exp(--(p2a_znorm2 (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z))}`] o
   check (fun th -> can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "p2au_soliton_shape")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC
     `((:real^3) DIFF p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b])
                                              (g:real->A->real^3^3)) b p tau0) UNION
      {Z | Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
           ~(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 Z =
             &8 * exp(--(p2a_znorm2 (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                    b p Z)))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_SIMP_TAC[REAL_LE_REFL];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "ALL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2AU_RIGID_SHAPE_FLOW THEN EXISTS_TAC `tau0:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ALL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Corollary: R2 and W3 imply FL5R (with P2AU_FLOW_RV_RIGID of pc_p2a_rigid). *)

let P2AU_FLOW_RV_RIGID_R2 = prove
 (`!(u:A->bool) (n:3->bool).
     P2AU_RIGID_R2_STATEMENT u
     ==> P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_RV_RIGID_STATEMENT u n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AU_FLOW_RV_RIGID THEN
  MATCH_MP_TAC P2AU_RIGID_R1 THEN ASM_REWRITE_TAC[]);;

