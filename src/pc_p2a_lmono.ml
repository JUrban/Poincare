(* ========================================================================= *)
(* Unit pc_p2a_lmono: monotonicity of the reduced-volume integrand along an  *)
(* L-geodesic without conjugate points, the global step                      *)
(* (P2AL_RVI_DECREASING).                                                    *)
(*                                                                           *)
(* First: limits at s = 0 for Jacobi data with Y(0) = 0, Y'(0) = B(0) = c I  *)
(* (c <> 0): Y(t)/t -> c I, det Y(t) <> 0 for small t > 0, and t tr(B Y^-1)  *)
(* -> n.  The proofs follow CMPJ_QUOT_LIM, CMPJ_TS_LIM, CMPJ_TS_TRACE_LIM    *)
(* and CMPJ_DET_POS_NEAR0 of pc_cmp_jcomp (cmp_jsys there has B(0) = I and a *)
(* Jacobi equation; only the data at 0 is used).                             *)
(* ========================================================================= *)

needs "src/pc_p2a_ljac.ml";;

prioritize_real();;
type_invention_error := true;;

let p2al_j0 = new_definition
 `p2al_j0 (Y:real->real^N^N) (B:real->real^N^N) (c:real) <=>
    Y(&0) = mat 0 /\ B(&0) = c %% mat 1 /\ ~(c = &0) /\
    ((\s. vectorize(Y(drop s))) has_vector_derivative vectorize(B(&0))) (at (lift(&0))) /\
    (\s. vectorize(B(drop s))) continuous (at (lift(&0)))`;;

let P2AL_J0_QUOT = prove
 (`!(Y:real->real^N^N) B c x.
     p2al_j0 Y B c
     ==> ((\t. inv t % (Y t ** x)) --> c % x) (atreal (&0) within {t | &0 < t})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_j0] THEN STRIP_TAC THEN
  MATCH_MP_TAC LIM_ATREAL_WITHINREAL THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o MATCH_MP CMPF_HAS_VD_MATVEC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
        (concl th))) THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_AT_1D; LIM_ATREAL_AT; o_DEF] THEN
  ASM_REWRITE_TAC[LIFT_NUM; DROP_VEC; VECTOR_SUB_RZERO; MATRIX_VECTOR_MUL_LZERO;
                  MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID]);;

let P2AL_J0_MQUOT = prove
 (`!(Y:real->real^N^N) B c x.
     p2al_j0 Y B c
     ==> ((\t. (inv t %% Y t) ** x) --> (c %% mat 1) ** x)
         (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  MATCH_MP_TAC P2AL_J0_QUOT THEN EXISTS_TAC `B:real->real^N^N` THEN ASM_REWRITE_TAC[]);;

let P2AL_J0_BLIM = prove
 (`!(Y:real->real^N^N) B c x.
     p2al_j0 Y B c
     ==> ((\t. B t ** x) --> (c %% mat 1) ** x) (atreal (&0) within {t | &0 < t})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_j0] THEN STRIP_TAC THEN
  MATCH_MP_TAC LIM_ATREAL_WITHINREAL THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTINUOUS_MATRIX_VECTORIZE] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  REWRITE_TAC[CONTINUOUS_AT; LIM_ATREAL_AT; o_DEF; LIFT_DROP] THEN
  ASM_REWRITE_TAC[]);;

let P2AL_J0_DETNZ = prove
 (`!(Y:real->real^N^N) B c.
     p2al_j0 Y B c
     ==> ?d. &0 < d /\ !t. &0 < t /\ t < d ==> ~(det(Y t) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\t. det(inv t %% (Y:real->real^N^N) t)) --->
                 det(c %% mat 1:real^N^N)) (atreal (&0) within {t | &0 < t})`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN `x:real^N` o MATCH_MP P2AL_J0_MQUOT) THEN
    REWRITE_TAC[LIM_MATRIX_COMPONENTWISE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_LIFT_DET) THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(det(c %% mat 1:real^N^N) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[DET_CMUL; DET_I; REAL_MUL_RID; REAL_POW_EQ_0] THEN
    ASM_MESON_TAC[p2al_j0];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(det(c %% mat 1:real^N^N))`) THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DET_CMUL] THEN
  ASM_CASES_TAC `det((Y:real->real^N^N) t) = &0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_ABS_NEG; REAL_LT_REFL]);;

let P2AL_J0_TS = prove
 (`!(Y:real->real^N^N) B c e1 e2.
     p2al_j0 Y B c
     ==> ((\t. t * (e1 dot ((B t ** matrix_inv(Y t)) ** e2))) ---> e1 dot e2)
         (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_MESON_TAC[p2al_j0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. t * ((e1:real^N) dot (((B:real->real^N^N) t **
                                matrix_inv((Y:real->real^N^N) t)) ** e2))) =
    (\t. (transp(B t) ** e1) dot (matrix_inv(inv t %% Y t) ** e2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_INV_CMUL; REAL_INV_INV; MATRIX_VECTOR_LMUL;
                DOT_RMUL; DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC;
                MATRIX_MUL_RMUL];
    ALL_TAC] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  SUBGOAL_THEN
   `lift((e1:real^N) dot e2) =
    lift((transp(c %% mat 1:real^N^N) ** e1) dot (matrix_inv(c %% mat 1:real^N^N) ** e2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_INV_CMUL; MATRIX_INV_I;
                MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_LMUL; DOT_RMUL] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPECL [`atreal (&0) within {t | &0 < t}`; `\x y:real^N. lift(x dot y)`]
     LIM_BILINEAR)) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN CONJ_TAC THENL
   [SPEC_TAC(`e1:real^N`,`e1:real^N`) THEN REWRITE_TAC[LIM_MATRIX_TRANSP] THEN
    X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC P2AL_J0_BLIM THEN
    MAP_EVERY EXISTS_TAC [`Y:real->real^N^N`] THEN ASM_REWRITE_TAC[];
    SPEC_TAC(`e2:real^N`,`e2:real^N`) THEN MATCH_MP_TAC LIM_MATRIX_INV THEN
    REWRITE_TAC[DET_CMUL; DET_I; REAL_MUL_RID; REAL_POW_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC P2AL_J0_MQUOT THEN
    EXISTS_TAC `B:real->real^N^N` THEN ASM_REWRITE_TAC[]]);;

let P2AL_J0_TRACE = prove
 (`!(Y:real->real^N^N) B c.
     p2al_j0 Y B c
     ==> ((\t. t * trace(B t ** matrix_inv(Y t))) ---> &(dimindex(:N)))
         (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. t * trace((B:real->real^N^N) t ** matrix_inv((Y:real->real^N^N) t))) =
    (\t. sum(1..dimindex(:N))
            (\i. t * (basis i dot ((B t ** matrix_inv(Y t)) ** basis i))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; trace; GSYM SUM_LMUL] THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(dimindex(:N)) = sum(1..dimindex(:N)) (\i. basis i dot (basis i:real^N))`
  SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS_BASIS; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ADD_SUB; REAL_MUL_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AL_J0_TS THEN
  MAP_EVERY EXISTS_TAC [`c:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The start window at s -> 0+.  Its Jacobi data satisfy p2al_j0 with c = 2  *)
(* (P2AL_SWIN_SETUP), and its comparison function tends to 0 from above at   *)
(* most: for every e > 0, gw(s) <= e and det Y(s) <> 0 for small s > 0       *)
(* (P2AL_SWIN_GW0).                                                          *)
(* ========================================================================= *)

let P2AL_SWIN_SETUP = prove
 (`!(V:p2alv) tt (x:A) Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ?W0 a0 U0 (phi0:A->real^N) e0.
           p2a_region V W0 a0 tt /\ x IN W0 /\ chart_at (p2a_vatlas V tt) x = (U0,phi0) /\
           a0 < tt /\ &0 < e0 /\ e0 <= sqrt(tt - a0) /\
           p2al_wok V tt x (&0) (sqrt(tt - a0)) W0 a0 tt U0 phi0 (:real^N)
             (\Z. pastecart (phi0 x) (&2 % Z)) /\
           (!s. abs s < e0
                ==> p2al_lin V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                      (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s) /\
           p2al_j0 (p2al_jy V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                      (\Z. pastecart (phi0 x) (&2 % Z)) Z0)
                   (p2al_jb V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                      (\Z. pastecart (phi0 x) (&2 % Z)) Z0) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` STRIP_ASSUME_TAC) o
    GEN_REWRITE_RULE I [p2a_bsmooth] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_bsmooth")) (concl th))) THEN
  MP_TAC(ISPEC `chart_at (p2a_vatlas (V:p2alv) tt) (x:A)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` (X_CHOOSE_TAC `phi0:A->real^N`)) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W0:A->bool`; `a0:real`; `U0:A->bool`;
                 `phi0:A->real^N`] P2AL_SWIN_WOK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W0:A->bool`; `a0:real`; `U0:A->bool`;
                 `phi0:A->real^N`; `Z0:real^N`] P2AL_SWIN_JYB0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2al_lwa (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 a0 tt U0 (phi0:A->real^N) (:real^N)
      (\Z. pastecart (phi0 x) (&2 % Z))`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `&0`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`;
                 `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                 `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z0:real^N`; `&0`]
                P2AL_LWIN_JACOBI) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W0:A->bool`; `a0:real`; `U0:A->bool`; `phi0:A->real^N`;
                        `min e1 (sqrt(tt - a0))`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2al_j0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC P2AL_HVD_CONT THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN ACCEPT_TAC th));;

(* Continuity of the chart Lagrangian and of tr Gamma(A,.) along the window *)
(* flow (at any time where the flow is defined).                             *)

let P2AL_WIN_FLCONT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> (\v. p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)) continuous (at (lift s)) /\
         abs(s - s1) < r /\
         fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) IN IMAGE phi (U INTER W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AL_HVD_CONT THEN ASM_MESON_TAC[]);;

let P2AL_WIN_LLAG_CONT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> (\v. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop v)
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))))
         continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WIN_FLCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop v)
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))
                (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))))) =
    (\z. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop(fstcart z))
                (fstcart(sndcart z)) (sndcart(sndcart z)))) o
    (\v. pastecart v (p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_PASTECART THEN ASM_REWRITE_TAC[CONTINUOUS_AT_ID]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag")) (concl th))) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; P2AL_IN_PCROSS_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AL_WIN_TG_CONT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> (\v. lift(p2al_tg (p2a_rlocal V W b' (U INTER W,phi) (tt - drop v pow 2))
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))))
         continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WIN_FLCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER W))` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_lsmooth]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\v. vsum(1..dimindex(:N))
                    (\i. (sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0
                                     (drop v)))$i %
                         lift(p2al_tg (p2a_rlocal V W b' (U INTER W,phi) (tt - drop v pow 2))
                                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))
                                (basis i)))` THEN
  EXISTS_TAC `min e (r - abs(s - s1))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; DROP_SUB; LIFT_DROP; REAL_LT_MIN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `drop v`] P2AL_WIN_FLCONT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM(REWRITE_RULE[o_DEF] LIFT_SUM)] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AL_TG_EXPAND THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
                   (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))` THEN
    REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "metric_field")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
    REWRITE_TAC[GSYM o_DEF] THEN
    SUBGOAL_THEN
     `(\v. sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))) =
      sndcart o (\v. p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_SNDCART] THEN
    REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `basis i:real^N` o MATCH_MP P2AL_TG_SMOOTH) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  SUBGOAL_THEN `open(interval(lift(s1 - r),lift(s1 + r)) PCROSS
                     IMAGE (phi:A->real^N) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift s)
                              (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s))`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(\v. lift(p2al_tg (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - drop v pow 2))
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) (basis i))) =
    (\z. lift(p2al_tg ((\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                        (drop(fstcart z))) (sndcart z) (basis i))) o
    (\v. pastecart v (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
  SUBGOAL_THEN
   `(\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))) =
    fstcart o (\v. p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART] THEN
  REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[]);;

(* F(s) = Ltil(Z0,s^2) -> 0 as s -> 0+.                                       *)

let P2AL_LTIL_LIM0 = prove
 (`!(V:p2alv) tt (x:A) b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> ((\s. p2a_Ltil V tt x (s pow 2) Z0) ---> &0) (atreal (&0) within {s | &0 < s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`] P2AL_LSINT_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z0 b) b`; `&0`; `sqrt b`]
                REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL) THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_RZERO; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (sqrt b)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `s:real`] P2AL_LTIL_INT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2AL_METRIC_NONNEG = prove
 (`!U (G:real^N->real^N^N) y v. metric_field U G /\ y IN U ==> &0 <= v dot (G y ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LRG_METRIC_POS THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2AL_GW_UPPER_ALG = prove
 (`!s Tr TG Q R FF n e.
     &0 < s /\ &0 <= Q /\
     abs(s * (s * Tr) + s pow 2 * TG - n * s + s / &2 * (inv(&2) * Q + &2 * s pow 2 * R) +
         FF / &2) < e
     ==> s pow 2 * (Tr + TG) - (n * s - s pow 3 * R + s * Q / &4 - FF / &2) <= e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `s pow 2 * (Tr + TG) - (n * s - s pow 3 * R + s * Q / &4 - FF / &2) =
    (s * (s * Tr) + s pow 2 * TG - n * s + s / &2 * (inv(&2) * Q + &2 * s pow 2 * R) +
     FF / &2) - (s * Q) / &2`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ASM_REAL_ARITH_TAC]);;

let P2AL_SWIN_GW0 = prove
 (`!(V:p2alv) tt (x:A) b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> ?W0 a0 U0 (phi0:A->real^N).
           p2a_region V W0 a0 tt /\ x IN W0 /\ chart_at (p2a_vatlas V tt) x = (U0,phi0) /\
           p2al_wok V tt x (&0) (sqrt(tt - a0)) W0 a0 tt U0 phi0 (:real^N)
             (\Z. pastecart (phi0 x) (&2 % Z)) /\
           !e. &0 < e
               ==> ?d. &0 < d /\
                       !s. &0 < s /\ s < d
                           ==> s < sqrt(tt - a0) /\ s pow 2 < b /\
                               p2al_lin V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                                 (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s /\
                               ~(det(p2al_jy V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s) = &0) /\
                               p2al_gw V tt x (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                                 (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z0:real^N`] P2AL_SWIN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` (X_CHOOSE_THEN `U0:A->bool`
    (X_CHOOSE_THEN `phi0:A->real^N` (X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`W0:A->bool`; `a0:real`; `U0:A->bool`; `phi0:A->real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 a0 tt U0 (phi0:A->real^N) (:real^N)
                  (\Z. pastecart (phi0 x) (&2 % Z))` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lin (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
      (\Z. pastecart (phi0 x) (&2 % Z)) Z0 (&0)`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_J0_DETNZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  (* the upper function and its limit *)
  SUBGOAL_THEN
   `((\s. s * (s * trace(p2al_jb (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
                            (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s **
                          matrix_inv(p2al_jy V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s))) +
          s pow 2 *
          p2al_tg (p2a_rlocal V W0 tt (U0 INTER W0,phi0) (tt - s pow 2))
            (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s))
            (sndcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s)) -
          &(dimindex(:N)) * s +
          s / &2 *
          p2a_llag (p2a_rlocal V W0 tt (U0 INTER W0,phi0)) tt s
            (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s))
            (sndcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                       (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s)) +
          p2a_Ltil V tt x (s pow 2) Z0 / &2) ---> &0)
     (atreal (&0) within {s | &0 < s})`
  MP_TAC THENL
   [SUBGOAL_THEN
     `&0 = &0 * &(dimindex(:N)) +
           &0 pow 2 *
           p2al_tg (p2a_rlocal (V:p2alv) W0 tt (U0 INTER W0,phi0:A->real^N) (tt - &0 pow 2))
             (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                        (\Z. pastecart (phi0 x) (&2 % Z)) Z0 (&0)))
             (sndcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                        (\Z. pastecart (phi0 x) (&2 % Z)) Z0 (&0))) -
           &(dimindex(:N)) * &0 +
           &0 / &2 *
           p2a_llag (p2a_rlocal V W0 tt (U0 INTER W0,phi0)) tt (&0)
             (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                        (\Z. pastecart (phi0 x) (&2 % Z)) Z0 (&0)))
             (sndcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                        (\Z. pastecart (phi0 x) (&2 % Z)) Z0 (&0))) +
           &0 / &2`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_WITHINREAL_ID] THEN
      MATCH_MP_TAC P2AL_J0_TRACE THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REALLIM_POW THEN REWRITE_TAC[REALLIM_WITHINREAL_ID];
          MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
          MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`;
                         `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                         `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z0:real^N`;
                         `&0`] P2AL_WIN_TG_CONT) THEN
          ASM_REWRITE_TAC[IN_UNIV] THEN
          REWRITE_TAC[CONTINUOUS_AT; TENDSTO_REAL; LIM_ATREAL_AT; o_DEF; LIFT_DROP]];
        MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[REALLIM_WITHINREAL_ID]];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_WITHINREAL_ID];
        MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
        MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`;
                       `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                       `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z0:real^N`; `&0`]
                      P2AL_WIN_LLAG_CONT) THEN
        ASM_REWRITE_TAC[IN_UNIV] THEN
        REWRITE_TAC[CONTINUOUS_AT; TENDSTO_REAL; LIM_ATREAL_AT; o_DEF; LIFT_DROP]];
      MATCH_MP_TAC REALLIM_RMUL THEN MATCH_MP_TAC P2AL_LTIL_LIM0 THEN
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt b` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `min d1 (min d2 (min e0 (sqrt b)))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lin (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
      (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d1:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi0:A->real^N) (U0 INTER W0)`;
                 `p2a_rlocal (V:p2alv) W0 tt (U0 INTER W0,phi0:A->real^N) (tt - s pow 2)`;
                 `fstcart(p2al_lfl (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
                            (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s)`;
                 `sndcart(p2al_lfl (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
                            (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s)`] P2AL_METRIC_NONNEG) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`;
                   `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                   `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z0:real^N`; `s:real`]
                  P2AL_WIN_FLCONT) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN
    REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "metric_field")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2al_gw; p2a_llag] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC P2AL_GW_UPPER_ALG THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_RZERO]) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The global monotonicity.  The chart-free function                         *)
(*   gf(s) = s^2 R'(s) / R(s),  R(s) = rvi(Z,s^2),                            *)
(* equals the window comparison function gw wherever a window with Y        *)
(* invertible is valid (P2AL_GF_EQ), so gf is non-increasing on (0,sm]       *)
(* while J > 0 there, it is <= 0 by the start window (gf(0+) <= 0), hence   *)
(* R is non-increasing on (0,sm] (P2AL_RVI_DECREASING).                       *)
(* ========================================================================= *)

let p2al_gf = new_definition
 `p2al_gf (V:p2alv) tt (x:A) (Z:real^N) (s:real) =
    s pow 2 * real_derivative (\s'. p2a_rvi V tt x (s' pow 2) Z) s /
    p2a_rvi V tt x (s pow 2) Z`;;

let P2AL_WOK_RVI_POS = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> &0 < p2a_J V tt x (s pow 2) Z0 /\ &0 < p2a_rvi V tt x (s pow 2) Z0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < det(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                          (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`] P2AL_ZDENS_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < p2a_J (V:p2alv) tt (x:A) (s pow 2) Z0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_J) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; SQRT_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [MP_TAC(ASSUME `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi`) THEN
    REWRITE_TAC[p2al_wok] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_rvi] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT; REAL_POW_LT]);;

let P2AL_GF_EQ = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> p2al_gf V tt x Z0 s = p2al_gw V tt x s1 r W b' U phi Phi Z0 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_RVI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_RVI_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [MP_TAC(ASSUME `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi`) THEN
    REWRITE_TAC[p2al_wok] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2al_gf] THEN
  UNDISCH_TAC `&0 < p2a_rvi (V:p2alv) tt (x:A) (s pow 2) Z0` THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let P2AL_WIN_DETNZ_NBHD = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> ?e. &0 < e /\
             !s'. abs(s' - s) < e ==> ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s') = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LWIN_JACOBI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0`;
                 `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s`; `s:real`]
                P2AL_ABSDET_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\s'. abs(det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s'))`;
                 `s:real`] P2AL_REAL_CONT_POS) THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_ABS_NZ]);;

(* A regular window at s0 where J > 0: Y is invertible there.               *)

let P2AL_WIN_AT = prove
 (`!(V:p2alv) tt (x:A) b Z s0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s0 /\ s0 pow 2 < b /\ &0 < p2a_J V tt x (s0 pow 2) Z
     ==> ?s1 r W a' b' U (phi:A->real^N) N Phi.
           p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 < s0 /\ s0 < s1 + r /\
           p2al_lin V tt s1 r W b' U phi Phi Z s0 /\
           ~(det(p2al_jy V tt s1 r W b' U phi Phi Z s0) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `s0:real`]
                P2AL_LWIN_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `&0 < p2a_J (V:p2alv) tt (x:A) (s0 pow 2) Z` THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`] P2AL_WOK_J) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO; real_div; REAL_LT_REFL]);;

let P2AL_GF_DERIV_LOCAL = prove
 (`!(V:p2alv) tt (x:A) b Z s0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s0 /\ s0 pow 2 < b /\ &0 < p2a_J V tt x (s0 pow 2) Z
     ==> ?g'. (p2al_gf V tt x Z has_real_derivative g') (atreal s0) /\ g' <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s0:real`] P2AL_WIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`] P2AL_WOK_GW_DERIV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g':real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s'. p2al_gw (V:p2alv) tt (x:A) s1 r W b' U (phi:A->real^N) Phi Z s'` THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`] P2AL_WIN_DETNZ_NBHD) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s0 < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min e1 (min e2 (sqrt b - s0))` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e1:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  CONV_TAC SYM_CONV THEN BETA_TAC THEN MATCH_MP_TAC P2AL_GF_EQ THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `a':real`; `N:real^N->bool`] THEN
  SUBGOAL_THEN `&0 <= s1` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= b` (fun th -> SIMP_TAC[th; SQRT_POW_2; REAL_LE_REFL]) THEN
      MP_TAC(SPEC `s0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* A function with a non-positive derivative at every point of (0,sm] is   *)
(* non-increasing there.                                                     *)

let P2AL_DECREASING_HALFOPEN = prove
 (`!f sm. (!s. &0 < s /\ s <= sm
              ==> ?d. (f has_real_derivative d) (atreal s) /\ d <= &0)
          ==> !s1 s2. &0 < s1 /\ s1 <= s2 /\ s2 <= sm ==> f s2 <= f s1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. --((f:real->real) s)`; `\s. --(real_derivative (f:real->real) s)`;
                 `{s | &0 < s /\ s <= sm}`; `s1:real`; `s2:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_NEG2] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2AL_GF_NONPOS = prove
 (`!(V:p2alv) tt (x:A) b Z sm.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < sm /\ sm pow 2 < b /\
     (!s. &0 < s /\ s <= sm ==> &0 < p2a_J V tt x (s pow 2) Z)
     ==> !s. &0 < s /\ s <= sm ==> p2al_gf V tt x Z s <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 < s /\ s <= sm ==> s pow 2 < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sm pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s1 s2. &0 < s1 /\ s1 <= s2 /\ s2 <= sm
                        ==> p2al_gf (V:p2alv) tt (x:A) Z s2 <= p2al_gf V tt x Z s1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL_DECREASING_HALFOPEN THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2AL_GF_DERIV_LOCAL THEN EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_SWIN_GW0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` (X_CHOOSE_THEN `U0:A->bool`
    (X_CHOOSE_THEN `phi0:A->real^N` STRIP_ASSUME_TAC)))) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(prove(`!g. (!e. &0 < e ==> g <= e) ==> g <= &0`,
    GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `g / &2`) THEN REAL_ARITH_TAC)) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min s (d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2al_gf (V:p2alv) tt (x:A) Z (min s (d / &2))` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`;
                 `a0:real`; `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                 `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z:real^N`;
                 `min s (d / &2)`] P2AL_GF_EQ) THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_ADD_LID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P2AL_RVI_DECREASING = prove
 (`!(V:p2alv) tt (x:A) b Z sm.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < sm /\ sm pow 2 < b /\
     (!s. &0 < s /\ s <= sm ==> &0 < p2a_J V tt x (s pow 2) Z)
     ==> !s1 s2. &0 < s1 /\ s1 <= s2 /\ s2 <= sm
                 ==> p2a_rvi V tt x (s2 pow 2) Z <= p2a_rvi V tt x (s1 pow 2) Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. p2a_rvi (V:p2alv) tt (x:A) (s pow 2) Z`; `sm:real`]
                P2AL_DECREASING_HALFOPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sm pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`] P2AL_WIN_AT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  EXISTS_TAC `p2a_rvi (V:p2alv) tt (x:A) (s pow 2) Z *
              p2al_gw V tt x s1 r W b' U (phi:A->real^N) Phi Z s / s pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_WOK_RVI_DERIV THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_GF_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sm:real`]
                P2AL_GF_NONPOS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_RVI_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= (a * --g) * c ==> (a * g) * c <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]]);;

