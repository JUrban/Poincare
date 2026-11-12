(* ========================================================================= *)
(* Unit pc_p2a_rigr2: step R2 of the FL5R route, P2AU_RIGID_R2_STATEMENT     *)
(* (pc_p2a_rigstmt), so that FL5R holds from W3.                             *)
(*                                                                           *)
(* Route: instead of MT's diffeomorphisms phi_tau, self-similarity of the    *)
(* pullback metrics P(Z,s) = Lexp_{s^2}^* g(b - s^2).                        *)
(* In a window, with Y = Jacobi matrix and G the chart metric,              *)
(*   d/ds (Y^T G Y) = Y^T (G S + S^T G + 4 s G Ric) Y,                       *)
(* so the soliton shape S = I/s - 2 s Ric gives P' = (2/s) P along each Z in *)
(* the conull set E; by density and continuity P(.,s) = (s/s0)^2 P(.,s0),    *)
(* hence sec(g(b - s0^2)) = (s/s0)^2 sec(g(b - s^2)) at Lexp points, which   *)
(* tends to 0 by the curvature bound.  Minimizers and joint continuity of   *)
(* the curvature give flatness at every point of [b - tau0,b].               *)
(* ========================================================================= *)

needs "src/pc_p2a_rigcore.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Step R2a: the pullback metric along a window curve.  The real             *)
(* function (Y a) . (G (Y c)) has derivative                                 *)
(*   (Y a).(G (Y' c)) + (Y a).(G' (Y c)) + (Y' a).(G (Y c))                  *)
(* (P2AU_QF3_DERIV); along a chart curve of a Ricci flow                     *)
(* G' = 4 s Ric_lower + DG[A] (P2A_METRIC_CURVE_VDERIV).  With the soliton   *)
(* shape B Y^-1 + Gamma(A) = I/s - 2 s Ric the derivative is (2/s) times the *)
(* value (P2AU_PB_SHAPE_ALG; metric compatibility LRG_MDERIV_CHRISTOFFEL).   *)
(* ------------------------------------------------------------------------- *)

let P2AU_QF3_DERIV = prove
 (`!(G:real->real^N^N) G' (Y:real->real^N^N) Y' (a:real^N) (c:real^N) s.
     ((\v. vectorize(G(drop v))) has_vector_derivative vectorize G') (at (lift s)) /\
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize Y') (at (lift s))
     ==> ((\s'. (Y s' ** a) dot (G s' ** (Y s' ** c))) has_real_derivative
          ((Y s ** a) dot (G s ** (Y' ** c)) + (Y s ** a) dot (G' ** (Y s ** c)) +
           (Y' ** a) dot (G s ** (Y s ** c)))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real->real^N^N`; `Y:real->real^N^N`; `G':real^N^N`; `Y':real^N^N`;
                 `s:real`] CMPF_HAS_VD_MATMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t. (G:real->real^N^N) t ** (Y:real->real^N^N) t`;
                 `(G:real->real^N^N) s ** (Y':real^N^N) + (G':real^N^N) ** (Y:real->real^N^N) s`;
                 `c:real^N`; `s:real`] CMPF_HAS_VD_MATVEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Y:real->real^N^N`; `Y':real^N^N`; `a:real^N`; `s:real`]
                CMPF_HAS_VD_MATVEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t. (Y:real->real^N^N) t ** (a:real^N)`;
                 `\t. ((G:real->real^N^N) t ** (Y:real->real^N^N) t) ** (c:real^N)`;
                 `(Y':real^N^N) ** (a:real^N)`;
                 `((G:real->real^N^N) s ** (Y':real^N^N) + (G':real^N^N) ** (Y:real->real^N^N) s) **
                  (c:real^N)`;
                 `s:real`] CMPF_DOT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP; MATRIX_VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC(MESON[] `!(f:real^1->real^1) a b. a = b ==> (f has_vector_derivative a) (at (lift s)) ==>
                                         (f has_vector_derivative b) (at (lift s))`) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD] THEN REAL_ARITH_TAC);;

let P2AU_SYM_DOT = prove
 (`!(M:real^N^N) x z. transp M = M ==> (M ** x) dot z = x dot (M ** z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`M:real^N^N`; `x:real^N`; `z:real^N`] DOT_MATRIX_TRANSP_LMUL) THEN
  ASM_REWRITE_TAC[]);;

let P2AU_PB_SHAPE_ALG = prove
 (`!U (G:real^N->real^N^N) y A0 (Y:real^N^N) (B:real^N^N) s (a:real^N) (c:real^N).
     metric_field U G /\ y IN U /\ &0 < s /\ ~(det Y = &0) /\
     B ** matrix_inv Y + matrix(christoffel G y A0) =
     inv(s) %% mat 1 - (&2 * s) %% matrix(p2a_lricop G y)
     ==> (Y ** a) dot (G y ** (B ** c)) +
         (Y ** a) dot (((&4 * s) %%
                        ((lambda i j. lricci G y (basis i) (basis j)):real^N^N) +
                        mderiv G y A0) ** (Y ** c)) +
         (B ** a) dot (G y ** (Y ** c)) =
         (&2 / s) * ((Y ** a) dot (G y ** (Y ** c)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `symmetric_matrix((G:real^N->real^N^N) y ** matrix(p2a_lricop G y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[symmetric_matrix; CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lambda i j. lricci (G:real^N->real^N^N) y (basis i) (basis j)):real^N^N =
                G y ** matrix(p2a_lricop G y)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AL_RICM_LOWER THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; symmetric_matrix]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `(Y:real^N^N) ** (a:real^N)`;
                 `A0:real^N`; `(Y:real^N^N) ** (c:real^N)`] LRG_MDERIV_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `A0:real^N` o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN DISCH_TAC THEN
  ABBREV_TAC `RM = matrix(p2a_lricop (G:real^N->real^N^N) y)` THEN
  ABBREV_TAC `Ga = matrix(christoffel (G:real^N->real^N^N) y A0)` THEN
  SUBGOAL_THEN `(B:real^N^N) = (inv(s) %% mat 1 - (&2 * s) %% (RM:real^N^N) - (Ga:real^N^N)) **
                             (Y:real^N^N)` SUBST1_TAC THENL
   [SUBGOAL_THEN `invertible(Y:real^N^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `(B:real^N^N) ** matrix_inv(Y:real^N^N) =
                  inv(s) %% mat 1 - (&2 * s) %% (RM:real^N^N) - (Ga:real^N^N)`
    MP_TAC THENL
     [MATCH_MP_TAC(MATRIX_ARITH `!P Q R:real^N^N. P + Q = R ==> P = R - Q`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ABBREV_TAC `u = (Y:real^N^N) ** (a:real^N)` THEN
  ABBREV_TAC `w = (Y:real^N^N) ** (c:real^N)` THEN
  SUBGOAL_THEN
   `((RM:real^N^N) ** (u:real^N)) dot ((G:real^N->real^N^N) y ** (w:real^N)) =
    u dot (G y ** RM ** w) /\
    ((Ga:real^N^N) ** u) dot (G y ** w) = w dot (G y ** Ga ** u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(G:real^N->real^N^N) y ** (RM:real^N^N)`; `u:real^N`; `w:real^N`]
                    P2AU_SYM_DOT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[symmetric_matrix]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AU_SYM_DOT THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN MATCH_MP_TAC P2AU_SYM_DOT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD; DOT_RSUB;
              DOT_LADD; DOT_LSUB; DOT_RMUL; DOT_LMUL; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The window form: along the window flow at a regular point with the       *)
(* soliton shape, (Y a).(G (Y c)) has logarithmic derivative 2/s.            *)

let P2AU_WIN_PB_DERIV = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s (a:real^N) (c:real^N).
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0) /\
     p2au_soliton_shape V tt x Z0 s
     ==> ((\s'. (p2al_jy V tt s1 r W b' U phi Phi Z0 s' ** a) dot
                (p2a_rlocal V W b' (U INTER W,phi) (tt - s' pow 2)
                   (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s')) **
                 (p2al_jy V tt s1 r W b' U phi Phi Z0 s' ** c)))
          has_real_derivative
          (&2 / s) * ((p2al_jy V tt s1 r W b' U phi Phi Z0 s ** a) dot
                      (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                         (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                       (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c))))
         (atreal s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  MP_TAC(ISPECL
   [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b':real`;
    `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
    `\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
    `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`; `s:real`]
   P2A_METRIC_CURVE_VDERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - t pow 2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 t))`;
    `(&4 * s) %% ((lambda i j. lricci (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)
                                          (tt - s pow 2))
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) (basis i) (basis j))
                  :real^N^N) +
     mderiv (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
            (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))`;
    `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0`;
    `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s`;
    `a:real^N`; `c:real^N`; `s:real`] P2AU_QF3_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal s) ==>
                                         (f has_real_derivative b) (atreal s)`) THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W))
                  (p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (phi:A->real^N) (U INTER W)`;
    `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)`;
    `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
    `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
    `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s`;
    `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s`;
    `s:real`; `a:real^N`; `c:real^N`] P2AU_PB_SHAPE_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2au_soliton_shape (V:p2alv) tt (x:A) Z0 s` THEN
    REWRITE_TAC[p2au_soliton_shape] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Step R2b: the pullback metric p2au_pbm V tt x tau Z of the metric at time *)
(* tt - tau by Lexp_tau (rfs_pullback, preferred charts). In a region chart  *)
(* representation phi o Lexp = fstcart o Phi it is D^T G D with G the region *)
(* metric (P2AU_PBM_REGION, as P2A_J_REGION), in a window it is jy^T G jy    *)
(* (P2AU_WOK_PBM, as P2AL_WOK_J), and near every point of Ldom it is         *)
(* continuous (P2AU_PBM_CONT_AT).                                            *)
(* ------------------------------------------------------------------------- *)

let p2au_pbm = new_definition
 `p2au_pbm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) tt (x:A) tau (Z:real^N) =
    rfs_pullback (p2a_vatlas V (tt - tau)) (p2a_Lexp V tt x tau)
                 (p2a_vmetric V (tt - tau)) Z`;;

let P2AU_PBM_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b N Wr a' b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum) Z.
     open N /\ p2a_region V Wr a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - b /\ tt - b <= b' /\ smooth_map_on N Phi /\
     (!Z. Z IN N ==> p2a_Lexp V tt x b Z IN U INTER Wr /\
                     phi(p2a_Lexp V tt x b Z) = fstcart(Phi Z)) /\
     Z IN N
     ==> p2au_pbm V tt x b Z =
         transp(matrix(frechet_derivative (fstcart o Phi) (at Z))) **
         p2a_rlocal V Wr b' (U INTER Wr,phi) (tt - b) (fstcart(Phi Z)) **
         matrix(frechet_derivative (fstcart o Phi) (at Z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `tt - b`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`)) (concl th))) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - b)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - b)`;
                 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b Z`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - b)) (Wr:A->bool)`)) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) (tt - b))
                           (p2a_Lexp V tt x b Z)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `N:real^N->bool`;
                 `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:(A->bool)#(A->real^N)`]
                P2A_LEXP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[p2au_pbm; rfs_pullback; mpullback] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(SND(c:(A->bool)#(A->real^N)) o
     p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) tt x b) =
    (\W. SND c (p2a_Lexp V tt x b W))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  ABBREV_TAC `q = p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b Z` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - b`; `c:(A->bool)#(A->real^N)`; `q:A`]
                P2A_RLOCAL_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) q = fstcart((Phi:real^N->real^(N,N)finite_sum) Z)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - b`; `c:(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h = chart_trans (U INTER Wr:A->bool,phi:A->real^N) c` THEN
  SUBGOAL_THEN `(h:real^N->real^N)(fstcart((Phi:real^N->real^(N,N)finite_sum) Z)) =
                SND(c:(A->bool)#(A->real^N)) q`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(phi:A->real^N) q = fstcart((Phi:real^N->real^(N,N)finite_sum) Z)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `Wr:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (h:real^N->real^N)
             (at (fstcart((Phi:real^N->real^(N,N)finite_sum) Z)))) /\
    linear(frechet_derivative (fstcart o (Phi:real^N->real^(N,N)finite_sum)) (at Z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `IMAGE (phi:A->real^N) ((U INTER Wr) INTER FST(c:(A->bool)#(A->real^N)))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(phi:A->real^N) q = fstcart((Phi:real^N->real^(N,N)finite_sum) Z)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      EXISTS_TAC `N:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P2AU_WOK_PBM = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ p2al_wok V tt x s1 r W a' b' U phi N Phi /\
     Z0 IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> p2au_pbm V tt x (s pow 2) Z0 =
         transp(p2al_jy V tt s1 r W b' U phi Phi Z0 s) **
         p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
         p2al_jy V tt s1 r W b' U phi Phi Z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o MATCH_MP P2AL_WOK_SLICE) THEN STRIP_TAC THEN
  UNDISCH_TAC `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` THEN
  REWRITE_TAC[p2al_lwa] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s pow 2`;
                 `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`;
                 `Z0:real^N`] P2AU_PBM_REGION) THEN
  REWRITE_TAC[p2al_jy; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_LGEO) THEN
    ASM_SIMP_TAC[]]);;

(* Continuity of (D a) . (G (D c)) for a smooth map and a metric field.      *)

let P2AU_QF_CONT_ON = prove
 (`!N Om (Hf:real^N->real^N) (G:real^N->real^N^N) (a:real^N) (c:real^N).
     open N /\ smooth_map_on N Hf /\ metric_field Om G /\ (!Z. Z IN N ==> Hf Z IN Om)
     ==> (\Z. lift((matrix(frechet_derivative Hf (at Z)) ** a) dot
                   (G(Hf Z) ** (matrix(frechet_derivative Hf (at Z)) ** c)))) continuous_on N`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!h. (\Z. frechet_derivative (Hf:real^N->real^N) (at Z) h) continuous_on N`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z h. Z IN N ==> matrix(frechet_derivative (Hf:real^N->real^N) (at Z)) ** h =
                                 frechet_derivative Hf (at Z) h`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `frechet_derivative (Hf:real^N->real^N) (at Z)` MATRIX_WORKS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\Z. lift(frechet_derivative (Hf:real^N->real^N) (at Z) a dot
                       ((G:real^N->real^N^N)(Hf Z) ** frechet_derivative Hf (at Z) c))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\Z. frechet_derivative (Hf:real^N->real^N) (at Z) a`;
                 `\Z. (G:real^N->real^N^N)((Hf:real^N->real^N) Z) **
                      frechet_derivative (Hf:real^N->real^N) (at Z) c`;
                 `\x y:real^N. lift(x dot y)`; `N:real^N->bool`]
                BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\Z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((G:real^N->real^N^N)((Hf:real^N->real^N) Z))`;
                 `\Z. frechet_derivative (Hf:real^N->real^N) (at Z) c`;
                 `\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`;
                 `N:real^N->bool`] BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\Z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((G:real^N->real^N^N)((Hf:real^N->real^N) Z))) =
                (vectorize o G) o Hf` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Om:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[metric_field];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

let P2AU_PBM_CONT_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0 (a:real^N) (c:real^N).
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> (\Z. lift(a dot (p2au_pbm V tt x b Z ** c))) continuous (at Z0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `Wr:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum`
     STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `(\Z. lift((a:real^N) dot (p2au_pbm (V:(real->A topology)#(real->((A->bool)#
                     (A->real^N))->bool)#(real->A->real^N^N)) tt x b Z ** (c:real^N))))
                continuous_on N`
  MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\Z. lift((matrix(frechet_derivative (fstcart o (Phi:real^N->real^(N,N)finite_sum)) (at Z)) **
              (a:real^N)) dot
             (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) Wr b' (U INTER Wr,phi:A->real^N) (tt - b)
                ((fstcart o Phi) Z) **
              (matrix(frechet_derivative (fstcart o Phi) (at Z)) ** (c:real^N))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `N:real^N->bool`;
                   `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`] P2AU_PBM_REGION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_THM; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AU_QF_CONT_ON THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER Wr)` THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`;
                   `(U INTER Wr:A->bool,phi:A->real^N)`; `tt - b`] P2A_RLOCAL_FIELD) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`))
                                  (concl th))) THEN
    REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* Two functions continuous at Z that agree on a conull set agree at Z.     *)

let P2AU_CONULL_AGREE = prove
 (`!(f:real^N->real^1) g E Z.
     negligible((:real^N) DIFF E) /\ f continuous (at Z) /\ g continuous (at Z) /\
     (!Y. Y IN E ==> f Y = g Y)
     ==> f Z = g Z`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\Y. (f:real^N->real^1) Y - g Y`; `Z:real^N`; `vec 0:real^1`]
                CONTINUOUS_AT_AVOID) THEN
  ASM_SIMP_TAC[CONTINUOUS_SUB] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `negligible(ball(Z:real^N,e))` MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `(:real^N) DIFF E` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    ASM_MESON_TAC[VECTOR_SUB_EQ];
    ASM_SIMP_TAC[OPEN_NOT_NEGLIGIBLE; OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Step R2c: along an initial vector Z of Smin(b) with the soliton shape at  *)
(* every s with s^2 < b, the entries of P(Z,s)/s^2 do not depend on s        *)
(* (P2AU_PBM_SCALE_E): near each s a regular window exists (P2AL_NO_CONJ,    *)
(* P2AL_WIN_AT), where P = jy^T G jy (P2AU_WOK_PBM) has logarithmic          *)
(* derivative 2/s (P2AU_WIN_PB_DERIV), so P/s^2 has derivative 0.            *)
(* ------------------------------------------------------------------------- *)

let p2au_wq = new_definition
 `p2au_wq (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
          (Z:real^N) (a:real^N) (c:real^N) (s:real) =
    (p2al_jy V tt s1 r W b' U phi Phi Z s ** a) dot
    (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
     (p2al_jy V tt s1 r W b' U phi Phi Z s ** c))`;;

let P2AU_LOGDER_SQ = prove
 (`!(P:real->real) p s.
     &0 < s /\ P s = p /\ (P has_real_derivative (&2 / s) * p) (atreal s)
     ==> ((\s'. P s' / s' pow 2) has_real_derivative &0) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real->real`; `(&2 / s) * p`; `\s':real. s' pow 2`; `&2 * s`; `s:real`]
                HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      BETA_TAC THEN REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal s) ==>
                                         (f has_real_derivative b) (atreal s)`) THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let P2AU_PBM_DERIV0 = prove
 (`!(V:p2alv) tt (x:A) b Z s (a:real^N) (c:real^N).
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x b /\ &0 < s /\ s pow 2 < b /\
     p2au_soliton_shape V tt x Z s
     ==> ((\s'. (a dot (p2au_pbm V tt x (s' pow 2) Z ** c)) / s' pow 2) has_real_derivative &0)
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`]
                P2AL_NO_CONJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`] P2AL_WIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1")) o
             last o CONJUNCTS) THEN
  SUBGOAL_THEN `&0 <= s1` ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\s'. p2au_wq (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z (a:real^N) (c:real^N) s' /
          s' pow 2`; `min e1 s`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "E1" (MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s':real`] P2AU_WOK_PBM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[p2au_wq; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    MATCH_MP_TAC P2AU_LOGDER_SQ THEN
    EXISTS_TAC `p2au_wq (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z (a:real^N) (c:real^N) s` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`; `a:real^N`;
                   `c:real^N`] P2AU_WIN_PB_DERIV) THEN
    ASM_REWRITE_TAC[p2au_wq]]);;

let P2AU_PBM_SCALE_E = prove
 (`!(V:p2alv) tt (x:A) b Z (a:real^N) (c:real^N).
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x b /\
     (!s. &0 < s /\ s pow 2 < b ==> p2au_soliton_shape V tt x Z s)
     ==> !s s0. &0 < s /\ s pow 2 < b /\ &0 < s0 /\ s0 pow 2 < b
                ==> (a dot (p2au_pbm V tt x (s pow 2) Z ** c)) / s pow 2 =
                    (a dot (p2au_pbm V tt x (s0 pow 2) Z ** c)) / s0 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s'. ((a:real^N) dot (p2au_pbm (V:p2alv) tt (x:A) (s' pow 2) Z ** (c:real^N))) /
                       s' pow 2`; `{s:real | &0 < s /\ s pow 2 < b}`]
                HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC P2AU_PBM_DERIV0 THEN EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `s0:real`) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Step R2d: P(.,s)/s^2 = P(.,s0)/s0^2 at every point of Ldom where both are *)
(* defined: the two sides are continuous (P2AU_PBM_CONT_AT) and agree on the *)
(* conull set E (P2AU_PBM_SCALE_E, P2AU_CONULL_AGREE).                       *)
(* ------------------------------------------------------------------------- *)

let P2AU_PBM_SCALE_ALL = prove
 (`!(V:p2alv) tt (x:A) b E (a:real^N) (c:real^N) s s0 Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     E SUBSET p2a_Smin V tt x b /\ negligible((:real^N) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < b ==> p2au_soliton_shape V tt x Z s) /\
     &0 < s /\ s pow 2 < b /\ &0 < s0 /\ s0 pow 2 < b /\
     Z IN p2a_Ldom V tt x (s pow 2) /\ Z IN p2a_Ldom V tt x (s0 pow 2)
     ==> (a dot (p2au_pbm V tt x (s pow 2) Z ** c)) / s pow 2 =
         (a dot (p2au_pbm V tt x (s0 pow 2) Z ** c)) / s0 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`\Z. lift((a dot (p2au_pbm (V:p2alv) tt (x:A) (s pow 2) Z ** c)) /
                                 s pow 2)`;
                       `\Z. lift((a dot (p2au_pbm (V:p2alv) tt (x:A) (s0 pow 2) Z ** c)) /
                                 s0 pow 2)`;
                       `E:real^N->bool`; `Z:real^N`] P2AU_CONULL_AGREE)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC P2AU_PBM_CONT_AT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC P2AU_PBM_CONT_AT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `Y:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Y:real^N`; `a:real^N`; `c:real^N`]
                  P2AU_PBM_SCALE_E) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Step R2e, part 1: for the flow view, Lexp_tau is a local parametrization  *)
(* of M near every Z of Ldom(tau) with J(Z,tau) > 0 (P2AU_LEXP_PARAM:        *)
(* P2A_LEXP_LOCAL, GEOF_SMOOTH_MAP_CHART_REP, GEOF_CONTINUOUS_CHART_REP,     *)
(* MFD_LOCAL_PARAM), and the curvature of the pullback metric p2au_pbm is    *)
(* the sectional curvature of g(b - tau) at Lexp_tau(Z) (P2AU_PBM_SECTIONAL: *)
(* APX_PULLBACK_SECTIONAL_GEN).                                              *)
(* ------------------------------------------------------------------------- *)

let P2AU_LINEAR_DET_INJ = prove
 (`!(f:real^N->real^N) h. linear f /\ ~(det(matrix f) = &0) /\ f h = vec 0 ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(matrix(f:real^N->real^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `h:real^N = matrix_inv(matrix(f:real^N->real^N)) ** (matrix f ** h)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; MATRIX_VECTOR_MUL_RZERO]);;

let P2AU_LEXP_PARAM = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau Z.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 < tau /\ tau < b - a /\
     Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z
     ==> ?S. open S /\ Z IN S /\
             S SUBSET p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
             mfd_param top atlas S
               (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b - tau`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `!t. p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t = atlas`
  ASSUME_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `Z:real^3`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Wr:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^3` (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum`
     STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^3) IN atlas` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN N ==> p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b p tau w IN FST(U:A->bool,phi:A->real^3) /\
                   SND(U,phi) (p2a_Lexp V b p tau w) =
                   (fstcart o (Phi:real^3->real^(3,3)finite_sum)) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[FST; SND; o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Phi:real^3->real^(3,3)finite_sum`)) (concl th))) THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b p tau`;
                 `N:real^3->bool`; `Z:real^3`] MFD_LOCAL_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GEOF_CONTINUOUS_CHART_REP) THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `(U:A->bool,phi:A->real^3)`;
                            `fstcart o (Phi:real^3->real^(3,3)finite_sum)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
      MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GEOF_SMOOTH_MAP_CHART_REP) THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(U:A->bool,phi:A->real^3)`;
                            `fstcart o (Phi:real^3->real^(3,3)finite_sum)`] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
      REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN X_GEN_TAC `h:real^3` THEN
      DISCH_TAC THEN MATCH_MP_TAC P2AU_LINEAR_DET_INJ THEN
      EXISTS_TAC `frechet_derivative
                   (\y. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                          (p2a_Lexp (V:(real->A topology)#(real->((A->bool)#
                          (A->real^3))->bool)#(real->A->real^3^3)) b p tau Z))
                         (p2a_Lexp V b p tau y)) (at Z)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `Z:real^3`]
                      P2A_LEXP_DIFFERENTIABLE) THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `&0 < p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b p tau Z` THEN
        ASM_REWRITE_TAC[p2a_J; REAL_ABS_0; REAL_MUL_LZERO; real_div; REAL_LT_REFL]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real^3->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P2AU_PBM_EQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) tau.
     p2au_pbm V tt x tau =
     rfs_pullback (p2a_vatlas V (tt - tau)) (p2a_Lexp V tt x tau) (p2a_vmetric V (tt - tau))`,
  REWRITE_TAC[FUN_EQ_THM; p2au_pbm]);;

let P2AU_PBM_SECTIONAL = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau S y u v.
     p2a_cbflow (top,atlas) a b g /\ &0 < tau /\ tau < b - a /\
     mfd_param top atlas S
       (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) /\
     y IN S
     ==> lsectional (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) y u v =
         mfd_sectional atlas (g(b - tau))
           (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau y)
           (frechet_derivative
              (SND(chart_at atlas
                     (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau y)) o
               p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) (at y) u)
           (frechet_derivative
              (SND(chart_at atlas
                     (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau y)) o
               p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) (at y) v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  REWRITE_TAC[P2AU_PBM_EQ; P2AU_FLOW_VIEW_PARTS] THEN
  MATCH_MP_TAC APX_PULLBACK_SECTIONAL_GEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `S:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Step R2e, part 2: the curvature scaling.  P(.,s) = (s/s0)^2 P(.,s0) near  *)
(* Z (P2AU_PBM_MAT_SCALE), so the curvature of P(.,s0) at Z is (s/s0)^2      *)
(* times that of P(.,s) (MFDR_LSECTIONAL_LOCAL, APX_LSECTIONAL_SCALE), which *)
(* is a sectional curvature of g(b - s^2) and so bounded by K; letting s ->  *)
(* 0 gives 0 (P2AU_SMALL_SQ, P2AU_SEC_ZERO_AT).                              *)
(* ------------------------------------------------------------------------- *)

let P2AU_SMALL_SQ = prove
 (`!X K s0. &0 < s0 /\ (!s. &0 < s /\ s < s0 ==> abs X <= (s / s0) pow 2 * K) ==> X = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!e. &0 < e ==> abs X <= e` MP_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `q = min (&1 / &2) (e / (abs K + &1))` THEN
    SUBGOAL_THEN `&0 < q /\ q <= &1 / &2 /\ q * (abs K + &1) <= e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < abs K + &1`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0 * q`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `s0 * q <= s0 * (&1 / &2) /\ &0 < s0 ==> s0 * q < s0`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s0 * q) / s0 = q` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `q pow 2 * K <= e` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q * (abs K + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2 * abs K` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `q * k <= &1 * k /\ &0 <= k ==> q * k <= k + &1`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `abs X / &2`) THEN REAL_ARITH_TAC);;

let P2AU_PBM_MAT_SCALE = prove
 (`!(V:p2alv) tt (x:A) b E s s0 (Z:real^N).
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     E SUBSET p2a_Smin V tt x b /\ negligible((:real^N) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < b ==> p2au_soliton_shape V tt x Z s) /\
     &0 < s /\ s pow 2 < b /\ &0 < s0 /\ s0 pow 2 < b /\
     Z IN p2a_Ldom V tt x (s pow 2) /\ Z IN p2a_Ldom V tt x (s0 pow 2)
     ==> p2au_pbm V tt x (s pow 2) Z = (s pow 2 / s0 pow 2) %% p2au_pbm V tt x (s0 pow 2) Z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ; MATRIX_CMUL_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `E:real^N->bool`;
                 `basis i:real^N`; `basis j:real^N`; `s:real`; `s0:real`; `Z:real^N`]
                P2AU_PBM_SCALE_ALL) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ &0 < s0 pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* Linear maps with nonzero determinant: injective, onto, keep planes.       *)

let P2AU_LIN_DET_FACTS = prove
 (`!f:real^N->real^N.
     linear f /\ ~(det(matrix f) = &0)
     ==> (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) /\
         (!u v. ~collinear {vec 0,u,v} ==> ~collinear {vec 0,f u,f v})`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. (f:real^N->real^N) x = f y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC P2AU_LINEAR_DET_INJ THEN EXISTS_TAC `f:real^N->real^N` THEN
    ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `{vec 0:real^N,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(f:real^N->real^N)`)] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let P2AU_LEXP_DER = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau Z.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 < tau /\ tau < b - a /\
     Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z
     ==> linear(frechet_derivative
                 (SND(chart_at atlas
                        (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z)) o
                  p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) (at Z)) /\
         ~(det(matrix(frechet_derivative
                 (SND(chart_at atlas
                        (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z)) o
                  p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) (at Z))) =
           &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `!t. p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t = atlas`
  ASSUME_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                  `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `Z:real^3`]
                  P2A_LEXP_DIFFERENTIABLE) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `&0 < p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b p tau Z` THEN
    ASM_REWRITE_TAC[p2a_J; REAL_ABS_0; REAL_MUL_LZERO; real_div; REAL_LT_REFL]]);;

let P2AU_SEC_ZERO_AT = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau0 E Z s0 u v.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 < tau0 /\ tau0 < b - a /\
     E SUBSET p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
     negligible((:real^3) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < tau0
            ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z s) /\
     &0 < s0 /\ s0 pow 2 < tau0 /\
     Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2) /\
     (!s. &0 < s /\ s <= s0
          ==> &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s pow 2) Z) /\
     ~collinear {vec 0,u,v}
     ==> lsectional (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2))
                    Z u v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `s0 pow 2 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s0 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`] P2A_LGEOD_FLOW_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC P2AU_SMALL_SQ THEN MAP_EVERY EXISTS_TAC [`K:real`; `s0:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 <= s0 pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^3) IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^3^3)) b p (s pow 2)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`Z:real^3`; `s0 pow 2`; `s pow 2`] o check (fun th ->
      length(fst(strip_forall(concl th))) = 3 && p2au_mentions "p2a_Ldom" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^3^3)) b p (s0 pow 2) Z /\
                &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s pow 2) Z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s0 pow 2`; `Z:real^3`] P2AU_LEXP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s pow 2`; `Z:real^3`] P2AU_LEXP_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S1:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the scaling identity near Z *)
  SUBGOAL_THEN
   `!Y. Y IN S0 INTER S1
        ==> p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                     b p (s pow 2) Y =
            (s pow 2 / s0 pow 2) %% p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                             b p (s0 pow 2) Y`
  ASSUME_TAC THENL
   [X_GEN_TAC `Y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(Y:real^3) IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^3^3)) b p (s pow 2) /\
      Y IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`)
      THENL [EXISTS_TAC `S1:real^3->bool`; EXISTS_TAC `S0:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2AU_PBM_MAT_SCALE THEN
    MAP_EVERY EXISTS_TAC [`tau0:real`; `E:real^3->bool`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 / s0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field S0 (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^3^3)) b p (s0 pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2AU_PBM_EQ; P2AU_FLOW_VIEW_PARTS] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b])
                  (g:real->A->real^3^3)) b p (s0 pow 2)) Z u v =
    (s pow 2 / s0 pow 2) *
    lsectional (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s pow 2))
               Z u v`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `lsectional (p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^3^3)) b p (s pow 2)) Z u v =
      lsectional (\z. (s pow 2 / s0 pow 2) %%
                      p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                               b p (s0 pow 2) z) Z u v`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `S0 INTER S1:real^3->bool` THEN
      ASM_SIMP_TAC[OPEN_INTER; IN_INTER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S0:real^3->bool`;
                   `p2au_pbm (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^3^3)) b p (s0 pow 2)`;
                   `s pow 2 / s0 pow 2`; `Z:real^3`; `u:real^3`; `v:real^3`]
                  APX_LSECTIONAL_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_FIELD `!x c. &0 < c ==> x = c * (x / c)`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the bound by K at time b - s^2 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s pow 2`; `S1:real^3->bool`; `Z:real^3`;
                 `u:real^3`; `v:real^3`] P2AU_PBM_SECTIONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s pow 2`; `Z:real^3`] P2AU_LEXP_DER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2AU_LIN_DET_FACTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
      (s pow 2) Z IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `s pow 2`; `Z:real^3`] P2A_T81_LEXP_TOPSPACE) THEN
    ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THENL [SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s / s0) pow 2 *
              mfd_rm_norm atlas ((g:real->A->real^3^3)(b - s pow 2))
                (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s pow 2) Z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_POW_DIV] THEN
    SUBGOAL_THEN `abs(s pow 2 / s0 pow 2) = s pow 2 / s0 pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* All sectional curvatures of g(b - s0^2) vanish at Lexp_{s0^2}(Z).          *)

let P2AU_FLAT_LEXP = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau0 E Z s0 u v.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 < tau0 /\ tau0 < b - a /\
     E SUBSET p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
     negligible((:real^3) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < tau0
            ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z s) /\
     &0 < s0 /\ s0 pow 2 < tau0 /\
     Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2) /\
     (!s. &0 < s /\ s <= s0
          ==> &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s pow 2) Z) /\
     ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas (g(b - s0 pow 2))
           (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2) Z) u v =
         &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s0 pow 2 /\ s0 pow 2 < b - a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^3^3)) b p (s0 pow 2) Z` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s0 pow 2`; `Z:real^3`] P2AU_LEXP_DER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(MATCH_MP P2AU_LIN_DET_FACTS th)) THEN
  ABBREV_TAC `D = frechet_derivative
                   (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                          (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b])
                                       (g:real->A->real^3^3)) b p (s0 pow 2) Z)) o
                    p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (s0 pow 2))
                   (at Z)` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `u:real^3` th) THEN MP_TAC(SPEC `v:real^3` th)) o
    check (fun th -> is_forall(concl th) && is_exists(snd(strip_forall(concl th))))) THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^3`) THEN DISCH_THEN(X_CHOOSE_TAC `u0:real^3`) THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3,u0,v0}` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`D:real^3->real^3`; `{vec 0:real^3,u0,v0}`] COLLINEAR_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(D:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s0 pow 2`; `Z:real^3`] P2AU_LEXP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s0 pow 2`; `S0:real^3->bool`; `Z:real^3`;
                 `u0:real^3`; `v0:real^3`] P2AU_PBM_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P2AU_SEC_ZERO_AT THEN MAP_EVERY EXISTS_TAC [`tau0:real`; `E:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Step R2f, part 1: chart tools.  Vanishing of all sectional curvatures at  *)
(* a point does not depend on the chart (P2AU_SEC_ZERO_CHART,                *)
(* LSECTIONAL_CHART_TRANS); along a Ricci flow the chart sectional curvature *)
(* is jointly continuous in (t,y) for a < t < b (P2AU_LSEC_JOINT_CONT:       *)
(* LRG_RICCI_FLOW_ON_CHART, LRG_LSMOOTH_LRIEMANN).                           *)
(* ------------------------------------------------------------------------- *)

let P2AU_SEC_ZERO_CHART = prove
 (`!top atlas (g:A->real^N^N) U (phi:A->real^N) V psi x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V /\
     (!u v. ~collinear {vec 0,u,v}
            ==> lsectional (metric_local atlas (V,psi) g) (psi x) u v = &0)
     ==> !u v. ~collinear {vec 0,u,v}
               ==> lsectional (metric_local atlas (U,phi) g) (phi x) u v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `g:A->real^N^N`; `x:A`;
                 `u:real^N`; `v:real^N`] LSECTIONAL_CHART_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = chart_jac (U:A->bool,phi:A->real^N) (V,psi) x` THEN
  ABBREV_TAC `J' = chart_jac (V:A->bool,psi:A->real^N) (U,phi) x` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y z. (J:real^N->real^N) y = J z ==> y = z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `J':real^N->real^N` o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_abs(rand(concl th)))) THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^N->real^N`; `{vec 0:real^N,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(J:real^N->real^N)`)] THEN
  ASM_MESON_TAC[]);;

let P2AU_LSEC_JOINT_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) c (u:real^N) (v:real^N).
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ ~collinear {vec 0,u,v}
     ==> (\z. lift(lsectional (metric_local atlas c (g(drop(fstcart z)))) (sndcart z) u v))
         continuous_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`] LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Gt = \t. metric_local (atlas:((A->bool)#(A->real^N))->bool) c ((g:real->A->real^N^N) t)` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (O:real^N->bool)` THEN
  SUBGOAL_THEN `!t. metric_local (atlas:((A->bool)#(A->real^N))->bool) c ((g:real->A->real^N^N) t) =
                    (Gt:real->real^N->real^N^N) t` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Gt" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lrg_lsmooth (O:real^N->bool) a b (Gt:real->real^N->real^N^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `lricci_flow (O:real^N->bool) a b (Gt:real->real^N->real^N^N)` THEN
    SIMP_TAC[lricci_flow; lrg_lsmooth];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  SUBGOAL_THEN `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
                continuous_on (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^(1,N)finite_sum->real^N.
      w continuous_on (S:real^(1,N)finite_sum->bool)
      ==> (\z. (Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** w z)
          continuous_on S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                   `w:real^(1,N)finite_sum->real^N`;
                   `\(m:real^(N,N)finite_prod) (x:real^N). (matrify m:real^N^N) ** x`;
                   `S:real^(1,N)finite_sum->bool`] BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. (\z. lift(x dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** y)))
                 continuous_on (S:real^(1,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                 lriemann (Gt (drop(fstcart z))) (sndcart z) u v v)))
    continuous_on (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC LRG_LSMOOTH_LRIEMANN THEN ASM_REWRITE_TAC[lrg_lsmooth];
    ALL_TAC] THEN
  ABBREV_TAC `den = \z. ((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** u)) *
                        ((v:real^N) dot (Gt (drop(fstcart z)) (sndcart z) ** v)) -
                        (u dot (Gt (drop(fstcart z)) (sndcart z) ** v)) pow 2` THEN
  SUBGOAL_THEN `(lift o (den:real^(1,N)finite_sum->real)) continuous_on S` ASSUME_TAC THENL
   [EXPAND_TAC "den" THEN REWRITE_TAC[o_DEF; LIFT_SUB; REAL_POW_2; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (S:real^(1,N)finite_sum->bool) ==> &0 < den z` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                                   FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "den" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC APX_SECT_DEN_POS THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z. inv((den:real^(1,N)finite_sum->real) z) %
                  lift((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                       lriemann (Gt (drop(fstcart z))) (sndcart z) u v v))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    EXPAND_TAC "den" THEN REWRITE_TAC[lsectional; real_div; GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(lift o (\z. inv((den:real^(1,N)finite_sum->real) z))) =
                (lift o inv o den)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

(* A chart curve along which the sectional curvature vanishes for s < s1   *)
(* has vanishing sectional curvature at s1 (one-sided limit, interior time). *)

let P2AU_SEC_CURVE_LIMIT = prove
 (`!top atlas a b (g:real->A->real^N^N) c (sig:real^1->real^N) s1 d (u:real^N) (v:real^N).
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ ~collinear {vec 0,u,v} /\ &0 < d /\
     sig continuous (at (lift s1) within {w | s1 - d < drop w /\ drop w <= s1}) /\
     (!s. s1 - d < s /\ s <= s1
          ==> sig(lift s) IN IMAGE (SND c) (FST c) /\ a < b - s pow 2 /\ b - s pow 2 < b) /\
     (!s. s1 - d < s /\ s < s1
          ==> lsectional (metric_local atlas c (g(b - s pow 2))) (sig(lift s)) u v = &0)
     ==> lsectional (metric_local atlas c (g(b - s1 pow 2))) (sig(lift s1)) u v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`; `u:real^N`; `v:real^N`]
                P2AU_LSEC_JOINT_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Tw = {w:real^1 | s1 - d < drop w /\ drop w <= s1}` THEN
  ABBREV_TAC `h = \w:real^1. pastecart (lift(b - drop w pow 2)) ((sig:real^1->real^N) w)` THEN
  SUBGOAL_THEN `IMAGE (h:real^1->real^(1,N)finite_sum) Tw SUBSET
                interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN EXPAND_TAC "Tw" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN
    X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop w` o check (fun th -> is_forall(concl th) &&
      p2au_mentions "IMAGE" th)) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^1->real^(1,N)finite_sum) continuous (at (lift s1) within Tw)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    REWRITE_TAC[CONTINUOUS_CONST] THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift(s1) IN (Tw:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tw" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Fs = (\z. lift(lsectional (metric_local (atlas:((A->bool)#(A->real^N))->bool) c
                       ((g:real->A->real^N^N)(drop(fstcart z)))) (sndcart z) u v)) o
                   (h:real^1->real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `(Fs:real^1->real^1) continuous (at (lift s1) within Tw)` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(\z. lift(lsectional (metric_local (atlas:((A->bool)#(A->real^N))->bool) c
                     ((g:real->A->real^N^N)(drop(fstcart z)))) (sndcart z) u v))
                 continuous_on interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)` THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (Fs:real^1->real^1) (lift s) =
                    lift(lsectional (metric_local (atlas:((A->bool)#(A->real^N))->bool) c
                       ((g:real->A->real^N^N)(b - s pow 2))) ((sig:real^1->real^N)(lift s)) u v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Fs" THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
    p2au_mentions "lsectional" th && free_in `Fs:real^1->real^1` (concl th))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Fs:real^1->real^1`; `lift s1`; `Tw:real^1->bool`; `vec 0:real^1`]
                CONTINUOUS_WITHIN_AVOID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift(s1 - min e d / &2)`) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Tw" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Step R2f, part 2: flatness at every point.  For x in M and tau1 in        *)
(* (0,tau0], a minimizer gamma of Smin(tau1) ends at (x,b - tau1)            *)
(* (P2AU_SMIN_COVER, FL2); for s^2 < tau1 the point gamma(s^2) is Lexp of an *)
(* initial vector without conjugate points, so the curvature vanishes there  *)
(* (P2AU_FLAT_LEXP); the chart curve of gamma and the joint continuity of    *)
(* the curvature give the limit s -> sqrt tau1 (P2AU_SEC_CURVE_LIMIT)        *)
(* (P2AU_FLAT_INTERIOR).                                                     *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLAT_INTERIOR = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau0 E tau1 x u v.
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau0 /\ tau0 < b - a /\
     E SUBSET p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
     negligible((:real^3) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < tau0
            ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z s) /\
     &0 < tau1 /\ tau1 <= tau0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas (g(b - tau1)) x u v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`] P2A_LGEOD_FLOW_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  (* the minimizer to x *)
  MP_TAC(ISPECL [`(:A)`; `(:3)`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `tau1:real`] P2AU_SMIN_COVER) THEN
  ASM_REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Zx:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(Zx:real^3) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau1` ASSUME_TAC THENL
   [UNDISCH_TAC `(Zx:real^3) IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau1` THEN
    SIMP_TAC[p2a_Smin; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `gam = p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b p Zx tau1` THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b p Zx tau1 gam /\ gam tau1 = x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_LGEO_PROP THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b p tau1 Zx = x` THEN
      REWRITE_TAC[p2a_Lexp]];
    ALL_TAC] THEN
  (* the chart near s0 = sqrt tau1 *)
  ABBREV_TAC `s0 = sqrt tau1` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 pow 2 = tau1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b p Zx tau1 gam` THEN
  REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `c:(A->bool)#(A->real^3)` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `Ad:real^1->real^3` STRIP_ASSUME_TAC)))))) THEN
  UNDISCH_TAC `c IN restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#
                 (A->real^3))->bool)#(real->A->real^3^3)) b') W` THEN
  EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
                IN_RESTRICT_ATLAS) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `phi = SND(c:(A->bool)#(A->real^3))` THEN
  ABBREV_TAC `d1 = min d s0` THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 <= d /\ d1 <= s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* vanishing in the chart (U0,phi) for s < s0 *)
  SUBGOAL_THEN
   `!s. s0 - d1 < s /\ s < s0
        ==> !u v. ~collinear {vec 0,u,v}
                  ==> lsectional (metric_local atlas (U0,phi:A->real^3)
                                    ((g:real->A->real^3^3)(b - s pow 2)))
                                 (phi(gam(s pow 2))) u v = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s /\ s pow 2 < tau1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `s0 pow 2`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`Zx:real^3`; `tau1:real`; `s pow 2`] o check (fun th ->
      length(fst(strip_forall(concl th))) = 3 && p2au_mentions "p2a_Ldom" th)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s pow 2`)) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM p2a_Lexp] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `!u' v'. ~collinear {vec 0,u',v'}
              ==> mfd_sectional atlas ((g:real->A->real^3^3)(b - s pow 2))
                    (p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) b p (s pow 2) Zx) u' v' = &0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "V" THEN
      MATCH_MP_TAC P2AU_FLAT_LEXP THEN MAP_EVERY EXISTS_TAC [`tau0:real`; `E:real^3->bool`] THEN
      EXPAND_TAC "V" THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AL_NO_CONJ THEN
        EXISTS_TAC `tau1:real` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `y = p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b p (s pow 2) Zx` THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`; `b:real`; `p:A`; `s pow 2`; `Zx:real^3`]
                    P2A_T81_LEXP_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN
      COND_CASES_TAC THENL [SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A)(s pow 2) = y` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`Zx:real^3`; `tau1:real`; `s pow 2`] o check (fun th ->
        length(fst(strip_forall(concl th))) = 3 && p2au_mentions "p2a_Ldom" th)) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b p (s pow 2) Zx = y` THEN
      REWRITE_TAC[p2a_Lexp] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN U0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        p2au_mentions "FST" th && free_in `gam:real->A` (concl th) &&
        not (p2au_mentions "has_vector_derivative" th))) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC P2AU_SEC_ZERO_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))`;
                          `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM mfd_sectional] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the limit s -> s0 in the chart (U0,phi), then back to chart_at x *)
  SUBGOAL_THEN `(U0:A->bool,phi:A->real^3) IN atlas` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN U0` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `x:A` && is_comb(lhs(concl th)))) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `s0 pow 2`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      p2au_mentions "FST" th && free_in `gam:real->A` (concl th) &&
      not (p2au_mentions "has_vector_derivative" th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; REAL_SUB_REFL; REAL_ABS_0];
                    ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(b - tau1)`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                 `U0:A->bool`; `phi:A->real^3`; `x:A`] P2AU_SEC_ZERO_CHART) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `u':real^3` THEN X_GEN_TAC `v':real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(phi:A->real^3) x = (\w. phi((gam:real->A)(drop w pow 2))) (lift s0) /\
                  b - tau1 = b - s0 pow 2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC P2AU_SEC_CURVE_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `d1:real`] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [(* continuity of the chart curve *)
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th -> is_forall(concl th) &&
        p2au_mentions "has_vector_derivative" th && free_in `gam:real->A` (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; REAL_SUB_REFL; REAL_ABS_0];
                      ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
      EXISTS_TAC `{v | &0 <= drop v /\ drop v pow 2 <= tau1}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
        REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\h:real^1. drop h % (Ad:real^1->real^3)(lift s0)` THEN
        ASM_REWRITE_TAC[GSYM has_vector_derivative];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `s0 pow 2`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      (* the chart curve stays in the chart, interior times *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < s /\ s pow 2 <= tau1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `s0 pow 2`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
          p2au_mentions "FST" th && free_in `gam:real->A` (concl th) &&
          not (p2au_mentions "has_vector_derivative" th))) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      (* vanishing for s < s0 *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        p2au_mentions "lsectional" th)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Step R2f, part 3: the top time t = b.  On (b - tau0,b) all sectional      *)
(* curvatures vanish (P2AU_FLAT_INTERIOR), so the chart Ricci curvature is 0 *)
(* (APX_CONST_CURV_RIEMANN, P2AU_ZERO_SEC_RIC), the chart metric is constant *)
(* in t there (Ricci flow equation), and by continuity at b (p2a_flow_upto)  *)
(* g(b) equals g(t1) in every chart; hence g(b) is flat (P2AU_FLAT_TOP).     *)
(* ------------------------------------------------------------------------- *)

let P2AU_ZERO_SEC_RIC = prove
 (`!top atlas (h:A->real^N^N) c y w1 w2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c) /\
     (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas h (chart_inv c y) u v = &0)
     ==> lricci (metric_local atlas c h) y w1 w2 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `q = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(q:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c q = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `q:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real^N^N`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (q:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (q:A))`; `q:A`]
                P2AU_SEC_ZERO_CHART) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
  ANTS_TAC THENL [REWRITE_TAC[GSYM mfd_sectional] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) c (h:A->real^N^N)`;
                 `y:real^N`; `&0`] APX_CONST_CURV_RIEMANN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[lricci; VEC_COMPONENT; SUM_0]);;

let P2AU_LEFT_LIMIT_CONST = prove
 (`!(f:real^1->real^M) b0 d K.
     f continuous (at (lift b0)) /\ &0 < d /\ (!t. b0 - d < t /\ t < b0 ==> f(lift t) = K)
     ==> f(lift b0) = K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^M`; `lift b0`; `K:real^M`] CONTINUOUS_AT_AVOID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift(b0 - min e d / &2)`) THEN
  ANTS_TAC THENL [REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2AU_FLAT_TOP = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau0 E x u v.
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau0 /\ tau0 < b - a /\
     E SUBSET p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
     negligible((:real^3) DIFF E) /\
     (!Z s. Z IN E /\ &0 < s /\ s pow 2 < tau0
            ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z s) /\
     x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas (g b) x u v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN
   `!t y u v. b - tau0 < t /\ t < b /\ y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas ((g:real->A->real^3^3) t) y u v = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t = b - (b - t)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2AU_FLAT_INTERIOR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `p:A`; `tau0:real`; `E:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t1 = b - tau0 / &2` THEN
  SUBGOAL_THEN `b - tau0 < t1 /\ t1 < b /\ a < t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`] LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  (* the chart metric does not move on (b - tau0,b) *)
  SUBGOAL_THEN
   `!y t. y IN IMAGE (SND c) (FST c) /\ b - tau0 < t /\ t < b
          ==> metric_local atlas c ((g:real->A->real^3^3) t) y =
              metric_local atlas (c:(A->bool)#(A->real^3)) (g t1) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\s. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) s)
                          (y:real^3)$i$j`; `{s:real | b - tau0 < s /\ s < b}`]
                  HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t':real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `lricci (metric_local atlas (c:(A->bool)#(A->real^3))
                     ((g:real->A->real^3^3) t')) y (basis i) (basis j) = &0`
      ASSUME_TAC THENL
       [MATCH_MP_TAC P2AU_ZERO_SEC_RIC THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t (q:A). q IN s /\ s SUBSET t ==> q IN t`) THEN
        EXISTS_TAC `FST(c:(A->bool)#(A->real^3))` THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[OPEN_IN_SUBSET]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 = --(&2) * lricci (metric_local atlas (c:(A->bool)#(A->real^3))
                     ((g:real->A->real^3^3) t')) y (basis i) (basis j)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        p2au_mentions "has_real_derivative" th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* continuity at b *)
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND c) (FST c)
        ==> metric_local atlas c ((g:real->A->real^3^3) b) y =
            metric_local atlas (c:(A->bool)#(A->real^3)) (g t1) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `p2a_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[p2a_flow_upto] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `(Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift b) (y:real^3)) =
      vectorize(metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) b) y)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` (concl th))) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      free_in `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` (concl th) &&
      not(is_forall(concl th)))) THEN
    MP_TAC(ISPECL [`\w:real^1. (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                 (pastecart w (y:real^3))`;
                   `b:real`; `tau0:real`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod)
                      (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t1) y)`]
                  P2AU_LEFT_LIMIT_CONST) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^1. (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                  (pastecart w (y:real^3))) =
                    Fx o (\w. pastecart w y)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
        ALL_TAC] THEN
      BETA_TAC THEN
      SUBGOAL_THEN `open(interval(lift a,lift(b + e)) PCROSS
                         IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
        p2au_mentions "smooth_map_on" th &&
        free_in `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` (concl th))) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^3`] o check (fun th ->
        is_forall(concl th) && free_in `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `lsectional (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t1))
               (SND c x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[GSYM mfd_sectional] THEN
    UNDISCH_TAC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A) = c` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM mfd_sectional] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Step R2g: the statement R2 (P2AU_RIGID_R2; the rvi hypothesis and W3 are  *)
(* not needed) and FL5R from W3 alone (P2AU_FLOW_RV_RIGID_W3, with           *)
(* P2AU_FLOW_RV_RIGID_R2 of pc_p2a_rigcore).                                 *)
(* ------------------------------------------------------------------------- *)

let P2AU_RIGID_R2 = prove
 (`!u:A->bool. P2AU_RIGID_R2_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2AU_RIGID_R2_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau0:real`;
                       `E:real^3->bool`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v1:real^3`; `v2:real^3`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN MATCH_MP_TAC P2AU_FLAT_TOP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `p:A`; `tau0:real`; `E:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t = b - (b - t)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2AU_FLAT_INTERIOR THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `p:A`; `tau0:real`; `E:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AU_FLOW_RV_RIGID_W3 = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_RV_RIGID_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_RV_RIGID_R2 THEN
  REWRITE_TAC[P2AU_RIGID_R2]);;

