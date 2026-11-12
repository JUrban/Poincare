(* ========================================================================= *)
(* Unit pc_p2a_lsv: no conjugate points before the end of a minimizing       *)
(* L-geodesic (MT Props 6.30/6.31) and L5 P2A_RVI_MONO.  At the first zero   *)
(* sz of J a window column c has Y(sz) c = 0 and u = B(sz) c <> 0.  The      *)
(* curve gamma_{Z + eps c} up to sa^2, two chart pieces with linear fields   *)
(* on [sa,sz] and [sz,sb] and gamma_Z after sb^2 is admissible with the end  *)
(* point of gamma_Z and, for t = kappa eps and small eps, shorter            *)
(* (second-order estimates via the first variation formula and a chart       *)
(* Taylor lemma), contradicting minimality (P2AL_NO_CONJ).  With             *)
(* pc_p2a_lmono this gives L5.                                               *)
(*                                                                           *)
(* Contents: the kernel lemma; J and its first zero; conjugate data;         *)
(* analysis tools and the chart Taylor lemma P2AL_CTL; a uniform tube;       *)
(* helpers and the final arithmetic; the window Taylor lemma; the chart      *)
(* competitor P2AL_CORE_NEG; the competitor on the manifold P2AL_NOCONJ_WIN; *)
(* P2AL_NO_CONJ and L5.                                                      *)
(*                                                                           *)
(* First: a Jacobi column (Y c, B c) of a window that vanishes at one time   *)
(* vanishes at every time of the window (the window flow is a                *)
(* diffeomorphism, ODE_FLOW_DIFFEO); the kernel lemma P2AL_JAC_KERNEL.       *)
(* ========================================================================= *)

needs "src/pc_p2a_lmono.ml";;
needs "src/pc_p2a_seg.ml";;
needs "src/pc_p2a_reg.ml";;
needs "src/pc_p2a_inj.ml";;
needs "src/pc_p2a_smth.ml";;

prioritize_real();;
type_invention_error := true;;

(* The window flow at time s as a function of the initial state.            *)

let P2AL_PSI_FACTS = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi
     ==> diffeomorphism_on
           {w | pastecart (lift s) (pastecart (lift s1) w) IN
                ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                  (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                   (IMAGE phi (U INTER W) PCROSS (:real^N)))}
           {w | pastecart (lift s1) (pastecart (lift s) w) IN
                ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                  (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                   (IMAGE phi (U INTER W) PCROSS (:real^N)))}
           (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                  (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                   (IMAGE phi (U INTER W) PCROSS (:real^N)))
                  (lift s) (pastecart (lift s1) w))
           (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                  (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                   (IMAGE phi (U INTER W) PCROSS (:real^N)))
                  (lift s1) (pastecart (lift s) w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  MATCH_MP_TAC ODE_FLOW_DIFFEO THEN ASM_REWRITE_TAC[]);;

let P2AL_LFL_PSI_DERIV = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> !c. pastecart (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c)
                       (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c) =
             frechet_derivative
               (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                      (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                       (IMAGE phi (U INTER W) PCROSS (:real^N)))
                      (lift s) (pastecart (lift s1) w))
               (at (Phi Z0)) (frechet_derivative Phi (at Z0) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:real^N` THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AL_PSI_FACTS) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (N:real^N->bool) /\ smooth_map_on N (Phi:real^N->real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LFL_HASDER_YB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`Phi:real^N->real^(N,N)finite_sum`;
    `\w. ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
           (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
           (lift s) (pastecart (lift s1) w)`;
    `frechet_derivative (Phi:real^N->real^(N,N)finite_sum) (at Z0)`;
    `frechet_derivative
       (\w. ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
              (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
              (lift s) (pastecart (lift s1) w))
       (at ((Phi:real^N->real^(N,N)finite_sum) Z0))`;
    `Z0:real^N`] DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
       `{w | pastecart (lift s) (pastecart (lift s1) w) IN
             ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
               (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                (IMAGE phi (U INTER W) PCROSS (:real^N)))}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` THEN
      REWRITE_TAC[p2al_lin]];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; GSYM p2al_lfl] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o CONJ (ASSUME
   `((\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s) has_derivative
     (\c. pastecart (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c)
                    (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c))) (at Z0)`)) THEN
  DISCH_THEN(MP_TAC o C AP_THM `c:real^N`) THEN REWRITE_TAC[]);;

let P2AL_FD_ZERO = prove
 (`!(f:real^M->real^P) net. f differentiable net ==> frechet_derivative f net (vec 0) = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  REWRITE_TAC[linear] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `vec 0:real^M`] o CONJUNCT2) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO]);;

let P2AL_JAC_KERNEL = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s c.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c = vec 0 /\
     p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c = vec 0
     ==> !s'. p2al_lin V tt s1 r W b' U phi Phi Z0 s'
              ==> p2al_jy V tt s1 r W b' U phi Phi Z0 s' ** c = vec 0 /\
                  p2al_jb V tt s1 r W b' U phi Phi Z0 s' ** c = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_EQ_VEC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s':real`]
                P2AL_LFL_PSI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `frechet_derivative (Phi:real^N->real^(N,N)finite_sum) (at Z0) c = vec 0`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_LFL_PSI_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN
    ASM_REWRITE_TAC[PASTECART_VEC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AL_PSI_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(Phi:real^N->real^(N,N)finite_sum) Z0`;
                                `frechet_derivative (Phi:real^N->real^(N,N)finite_sum) (at Z0) c`] o
                MATCH_MP (REWRITE_RULE[IMP_CONJ] ODE_DIFFEO_DERIVATIVE_INVERSE)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` THEN
      REWRITE_TAC[p2al_lin];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `vec 0:real^(N,N)finite_sum`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC P2AL_FD_ZERO THEN
    UNDISCH_TAC
     `diffeomorphism_on
       {w | pastecart (lift s) (pastecart (lift s1) w) IN
            ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
              (interval(lift(s1 - r),lift(s1 + r)) PCROSS
               (IMAGE phi (U INTER W) PCROSS (:real^N)))}
       {w | pastecart (lift s1) (pastecart (lift s) w) IN
            ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
              (interval(lift(s1 - r),lift(s1 + r)) PCROSS
               (IMAGE phi (U INTER W) PCROSS (:real^N)))}
       (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
              (interval(lift(s1 - r),lift(s1 + r)) PCROSS
               (IMAGE phi (U INTER W) PCROSS (:real^N)))
              (lift s) (pastecart (lift s1) w))
       (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
              (interval(lift(s1 - r),lift(s1 + r)) PCROSS
               (IMAGE phi (U INTER W) PCROSS (:real^N)))
              (lift s1) (pastecart (lift s) w))` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `{w | pastecart (lift s1) (pastecart (lift s) w) IN
           ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
             (interval(lift(s1 - r),lift(s1 + r)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)))}` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(Phi:real^N->real^(N,N)finite_sum) Z0 IN
      {w | pastecart (lift s) (pastecart (lift s1) w) IN
           ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
             (interval(lift(s1 - r),lift(s1 + r)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)))}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` THEN
      REWRITE_TAC[p2al_lin];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AL_FD_ZERO THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s':real`] P2AL_PSI_FACTS) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC
   `{w | pastecart (lift s') (pastecart (lift s1) w) IN
         ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
           (interval(lift(s1 - r),lift(s1 + r)) PCROSS
            (IMAGE phi (U INTER W) PCROSS (:real^N)))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s'` THEN
  REWRITE_TAC[p2al_lin]);;

(* ========================================================================= *)
(* J(Z,s^2) along the geodesic: non-negative and continuous in s (window     *)
(* formula P2AL_WOK_J), and the first zero of J.                             *)
(* ========================================================================= *)

let P2AL_J_NONNEG = prove
 (`!(V:p2alv) tt (x:A) b Z s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s /\ s pow 2 <= b
     ==> &0 <= p2a_J V tt x (s pow 2) Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `s:real`]
                P2AL_LWIN_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_J) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`] P2AL_ZDENS_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < det(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                          (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]);;

let P2AL_J_CONT = prove
 (`!(V:p2alv) tt (x:A) b Z s0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s0 /\ s0 pow 2 < b
     ==> (\s. p2a_J V tt x (s pow 2) Z) real_continuous (atreal s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `s0:real`]
                P2AL_LWIN_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. abs(det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)) *
                  sqrt(det(p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                             (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))) /
                  p2a_zdens V tt x` THEN
  EXISTS_TAC `min e s0` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [X_GEN_TAC `s':real` THEN BETA_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AL_WOK_J THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ABS THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_DET_VECTORIZE THEN
    MATCH_MP_TAC P2AL_HVD_CONT THEN
    EXISTS_TAC `vectorize(p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s0)` THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`]
                  P2AL_LWIN_JACOBI) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_DET_VECTORIZE THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s0:real`]
                  P2AL_WIN_GCONT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* J > 0 near tau = 0 (start window, det Y <> 0 there).                     *)

let P2AL_J_POS0 = prove
 (`!(V:p2alv) tt (x:A) b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b
     ==> ?d. &0 < d /\
             !s. &0 < s /\ s < d ==> s pow 2 < b /\ &0 < p2a_J V tt x (s pow 2) Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_SWIN_GW0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` (X_CHOOSE_THEN `U0:A->bool`
    (X_CHOOSE_THEN `phi0:A->real^N` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`;
                 `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                 `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z:real^N`; `s:real`]
                P2AL_WOK_RVI_POS) THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_ADD_LID] THEN SIMP_TAC[]);;

(* The first zero of s |-> J(Z,s^2) on (0,s0].                               *)

let P2AL_FIRST_ZERO = prove
 (`!(V:p2alv) tt (x:A) b Z s0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s0 /\ s0 pow 2 < b /\ p2a_J V tt x (s0 pow 2) Z = &0
     ==> ?sz. &0 < sz /\ sz <= s0 /\ p2a_J V tt x (sz pow 2) Z = &0 /\
              !s. &0 < s /\ s < sz ==> &0 < p2a_J V tt x (s pow 2) Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_J_POS0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. &0 < s /\ s <= s0 ==> s pow 2 < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s0 pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= s0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
      can (find_term ((=) `d:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K = {s | d / &2 <= s /\ s <= s0 /\
                       p2a_J (V:p2alv) tt (x:A) (s pow 2) (Z:real^N) = &0}` THEN
  SUBGOAL_THEN `~(K:real->bool = {}) /\ (?bb. !s. s IN K ==> bb <= s)` MP_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `d / &2` THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INF) THEN
  ABBREV_TAC `sz = inf(K:real->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inf1") (LABEL_TAC "inf2")) THEN
  SUBGOAL_THEN `d / &2 <= sz /\ sz <= s0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REMOVE_THEN "inf2" MATCH_MP_TAC THEN EXPAND_TAC "K" THEN SIMP_TAC[IN_ELIM_THM];
      USE_THEN "inf1" MATCH_MP_TAC THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `sz:real` THEN
  SUBGOAL_THEN `&0 < sz` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= j /\ ~(&0 < j) ==> j = &0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AL_J_NONNEG THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. p2a_J (V:p2alv) tt (x:A) (s pow 2) (Z:real^N)`; `sz:real`]
                  P2AL_REAL_CONT_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AL_J_CONT THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `sz + e / &2 <= sz` MP_TAC THENL
     [REMOVE_THEN "inf2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `sz <= s` ASSUME_TAC THENL
       [USE_THEN "inf1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `(s:real) IN K` THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        can (find_term ((=) `e:real`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LT_REFL]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < d` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (find_term ((=) `d:real`)) (concl th) && is_forall(concl th) &&
      not (can (find_term ((=) `s0:real`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= j /\ ~(j = &0) ==> &0 < j`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_J_NONNEG THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN SUBGOAL_THEN `sz <= s` MP_TAC THENL
     [USE_THEN "inf1" MATCH_MP_TAC THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* In a window, J(Z,s^2) = 0 exactly when det Y(s) = 0; at the first zero sz *)
(* of J a window column c has Y(sz) c = 0 and B(sz) c <> 0 (P2AL_JAC_KERNEL  *)
(* and det Y <> 0 just before sz).                                           *)
(* ========================================================================= *)

let P2AL_WOK_DETG_POS = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> &0 < det(p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                    (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2AL_WOK_J_ZERO = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ &0 < s /\
     s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> (p2a_J V tt x (s pow 2) Z0 = &0 <=>
          det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_J) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_DETG_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`] P2AL_ZDENS_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO] THEN
  MATCH_MP_TAC(TAUT `~q ==> (p \/ q <=> p)`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT]);;

let P2AL_CONJ_DATA = prove
 (`!(V:p2alv) tt (x:A) b Z sz.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < sz /\ sz pow 2 < b /\
     p2a_J V tt x (sz pow 2) Z = &0 /\
     (!s. &0 < s /\ s < sz ==> &0 < p2a_J V tt x (s pow 2) Z)
     ==> ?s1 r W a' b' U (phi:A->real^N) N Phi c.
           p2al_wok V tt x s1 r W a' b' U phi N Phi /\ &0 < s1 /\ s1 < sz /\
           sz < s1 + r /\ Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z sz /\
           p2al_jy V tt s1 r W b' U phi Phi Z sz ** c = vec 0 /\
           ~(p2al_jb V tt s1 r W b' U phi Phi Z sz ** c = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `sz:real`]
                P2AL_LWIN_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi /\ &0 < s1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok; p2al_lwin]; ALL_TAC] THEN
  SUBGOAL_THEN `det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z sz) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_J_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z sz`
               HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                        `phi:A->real^N`; `N:real^N->bool`;
                        `Phi:real^N->real^(N,N)finite_sum`; `c:real^N`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`; `c:real^N`]
                P2AL_JAC_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ker") THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  ABBREV_TAC `sq = max ((s1 + sz) / &2) (sz - e / &2)` THEN
  SUBGOAL_THEN `s1 < sq /\ sq < sz /\ abs(sq - sz) < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sq:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ker" (MP_TAC o SPEC `sq:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sq:real`] P2AL_WOK_J_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p /\ q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < j ==> ~(j = &0)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    EXISTS_TAC `c:real^N` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Real-analysis tools for the competitor estimates. Derivatives along a     *)
(* line; the cubic smallness of F(Z+tc) - F(Z) - m(Z).(y(Z+tc) - y(Z)) when  *)
(* D y(Z) c = 0 and D F = (D y) . m (P2AL_CHI_SMALL); the partial derivative *)
(* of the L-Lagrangian in the state; the chart Taylor lemma P2AL_CTL: for an *)
(* L-geodesic chart curve y0 and a C^1 field eta, cL(y0 + eta) - cL(y0) is   *)
(* the boundary term [eta . G A] up to B M2 (s2 - s1), where B is a          *)
(* second-order Taylor constant of the Lagrangian on a compact set           *)
(* containing the segments.                                                  *)
(* ========================================================================= *)

let P2AL_LINE_RDERIV = prove
 (`!(g:real^N->real^1) g' (Z0:real^N) c t.
     (g has_derivative g') (at (Z0 + t % c))
     ==> ((\s. drop(g(Z0 + s % c))) has_real_derivative drop(g' c)) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN `(lift o (\s. drop((g:real^N->real^1)(Z0 + s % c))) o drop) =
                g o (\v:real^1. Z0 + drop v % c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(g':real^N->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. drop((g':real^N->real^1) c) % x) = g' o (\h:real^1. drop h % c)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`\v:real^1. Z0:real^N`; `\h:real^1. vec 0:real^N`;
                 `\v:real^1. drop v % (c:real^N)`; `\h:real^1. drop h % (c:real^N)`;
                 `at(lift t)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let P2AL_CHI_SMALL = prove
 (`!S (Fl:real^N->real^1) (fy:real^N->real^N) (mm:real^N->real^N) Z0 c.
     open S /\ Z0 IN S /\ smooth_map_on S fy /\ smooth_map_on S mm /\
     (!Z. Z IN S
          ==> (Fl has_derivative (\h. lift(frechet_derivative fy (at Z) h dot mm Z))) (at Z)) /\
     frechet_derivative fy (at Z0) c = vec 0
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. &0 < t /\ t < d
                         ==> abs(drop(Fl(Z0 + t % c)) - drop(Fl Z0) -
                                 mm Z0 dot (fy(Z0 + t % c) - fy Z0)) <= e * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mm:real^N->real^N`; `S:real^N->bool`; `Z0:real^N`] P2A_SMOOTH_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Lt:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip")))))) THEN
  SUBGOAL_THEN `(\Z. frechet_derivative (fy:real^N->real^N) (at Z) c) continuous (at Z0)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `fy:real^N->real^N`; `c:real^N`]
                  SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN ASM_REWRITE_TAC[DIST_0] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (Lt * norm(c:real^N) + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  SUBGOAL_THEN `&0 < norm(c:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min r1 d2 / (norm(c:real^N) + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= t
                    ==> s * norm(c:real^N) < r1 /\ s * norm c < d2 /\
                        Z0 + s % c IN cball(Z0,r1) /\ Z0 + s % c IN S /\
                        dist(Z0 + s % c,Z0) = s * norm c`
  (LABEL_TAC "pts") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s * norm(c:real^N) < min r1 d2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s * (norm(c:real^N) + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * (norm(c:real^N) + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(Z0 + s % c,Z0:real^N) = s * norm c` ASSUME_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
      ALL_TAC] THEN
    SUBGOAL_THEN `Z0 + s % c IN cball(Z0:real^N,r1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `s * norm(c:real^N) < min r1 d2` THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= t
        ==> ((\s. drop((Fl:real^N->real^1)(Z0 + s % c)) -
                  (mm:real^N->real^N) Z0 dot (fy:real^N->real^N)(Z0 + s % c))
             has_real_derivative
             (frechet_derivative fy (at (Z0 + s % c)) c dot (mm(Z0 + s % c) - mm Z0)))
            (atreal s)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "pts" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `((fy:real^N->real^N) has_derivative frechet_derivative fy (at (Z0 + s % c)))
                  (at (Z0 + s % c))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\Z:real^N. lift((mm:real^N->real^N) Z0 dot (fy:real^N->real^N) Z)`;
                   `\h:real^N. lift((mm:real^N->real^N) Z0 dot
                                    frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) h)`;
                   `Z0:real^N`; `c:real^N`; `s:real`] P2AL_LINE_RDERIV) THEN
    ANTS_TAC THENL
     [MP_TAC(INST [`(mm:real^N->real^N) Z0`,`v:real^N`]
        (MATCH_MP HAS_DERIVATIVE_LIFT_DOT (ASSUME
          `((fy:real^N->real^N) has_derivative frechet_derivative fy (at (Z0 + s % c)))
           (at (Z0 + s % c))`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Fl:real^N->real^1`;
                   `\h:real^N. lift(frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) h dot
                                    (mm:real^N->real^N)(Z0 + s % c))`;
                   `Z0:real^N`; `c:real^N`; `s:real`] P2AL_LINE_RDERIV) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_REAL_DERIVATIVE_SUB) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_RSUB] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. drop((Fl:real^N->real^1)(Z0 + s % c)) -
                      (mm:real^N->real^N) Z0 dot (fy:real^N->real^N)(Z0 + s % c)`;
                 `\s. frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c dot
                      ((mm:real^N->real^N)(Z0 + s % c) - mm Z0)`;
                 `real_interval[&0,t]`; `e * t`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      USE_THEN "der" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "pts" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `norm(frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c)
                  <= e / (Lt * norm(c:real^N) + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "cont" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((mm:real^N->real^N)(Z0 + s % c) - mm Z0) <= Lt * (t * norm(c:real^N))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lt * norm((Z0 + s % c) - Z0:real^N)` THEN
      CONJ_TAC THENL
       [USE_THEN "lip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM dist] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / (Lt * norm(c:real^N) + &1) * (Lt * (t * norm(c:real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(frechet_derivative (fy:real^N->real^N) (at (Z0 + s % c)) c) *
                  norm((mm:real^N->real^N)(Z0 + s % c) - mm Z0)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `e / (Lt * norm(c:real^N) + &1) * (Lt * (t * norm c)) =
                  (e * t) * ((Lt * norm c) / (Lt * norm c + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(c:real^N) + &1` THEN
      SUBGOAL_THEN `&0 < Lt * norm(c:real^N) + &1` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Lt * norm(c:real^N) + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `&0`]) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO; DOT_RSUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ b = c ==> abs x <= b ==> abs y <= c`) THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
                  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC]]);;

(* The derivative in the direction (0,dw) is the partial derivative in w.   *)

let P2AL_PARTIAL_W = prove
 (`!(g:real^(1,M)finite_sum->real^P) s0 w0 dw.
     g differentiable (at (pastecart s0 w0))
     ==> frechet_derivative g (at (pastecart s0 w0)) (pastecart (vec 0) dw) =
         frechet_derivative (\w. g(pastecart s0 w)) (at w0) dw`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  SUBGOAL_THEN
   `((\w. (g:real^(1,M)finite_sum->real^P) (pastecart s0 w)) has_derivative
     (\h. frechet_derivative g (at (pastecart s0 w0)) (pastecart (vec 0) h))) (at w0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^M. pastecart (s0:real^1) w`; `g:real^(1,M)finite_sum->real^P`;
                   `\h:real^M. pastecart (vec 0:real^1) h`;
                   `frechet_derivative (g:real^(1,M)finite_sum->real^P) (at (pastecart s0 w0))`;
                   `w0:real^M`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

(* The state derivative of the L-Lagrangian (the first-variation integrand  *)
(* of P2AL_WEAK_EL_BDRY).                                                    *)

let P2AL_LLAG_DW = prove
 (`!U (Gt:real->real^N->real^N^N) tt s y A dy dA.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U /\
     (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z)) (sndcart(sndcart z))))
       differentiable (at (pastecart (lift s) (pastecart y A)))
     ==> frechet_derivative
           (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z)) (sndcart(sndcart z))))
           (at (pastecart (lift s) (pastecart y A))) (pastecart (vec 0) (pastecart dy dA)) =
         lift(inv(&2) * (A dot (mderiv (Gt(tt - s pow 2)) y dy ** A)) +
              &2 * s pow 2 *
              drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at y) dy) +
              dA dot (Gt(tt - s pow 2) y ** A))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P2AL_PARTIAL_W th]) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`;
                 `y:real^N`; `A:real^N`; `&2 * s pow 2`] P2AL_QF_HASDER) THEN
  ASM_REWRITE_TAC[p2a_llag; GSYM REAL_MUL_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

(* Continuity of the Lagrangian along a continuous state curve.             *)

let P2AL_LG_CURVE_CONT = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (p:real^1->real^N) (q:real^1->real^N) s.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s /\ s < sb /\ p(lift s) IN U /\
     p continuous (at (lift s)) /\ q continuous (at (lift s))
     ==> (\s. p2a_llag Gt tt s (p(lift s)) (q(lift s))) real_continuous atreal s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  SUBGOAL_THEN
   `(lift o (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((p:real^1->real^N)(lift s))
                          ((q:real^1->real^N)(lift s))) o drop) =
    (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z)) (sndcart(sndcart z)))) o
    (\v. pastecart v (pastecart (p v) (q v)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_PASTECART THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
  SUBGOAL_THEN `open(interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_UNIV] THEN ASM_MESON_TAC[p2a_lsmooth];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  ASM_REWRITE_TAC[]);;

let P2AL_INT_BOUND3 = prove
 (`!f2 f1 g i2 i1 j a b C.
     a <= b /\ &0 <= C /\
     (f2 has_real_integral i2) (real_interval[a,b]) /\
     (f1 has_real_integral i1) (real_interval[a,b]) /\
     (g has_real_integral j) (real_interval[a,b]) /\
     (!s. a <= s /\ s <= b ==> abs(f2 s - f1 s - g s) <= C)
     ==> abs(i2 - i1 - j) <= C * (b - a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_BOUND THEN
  EXISTS_TAC `\s:real. f2 s - f1 s - g s` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN ASM_REWRITE_TAC[]);;

(* The chart Taylor lemma.                                                   *)

let P2AL_CTL = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt ta tb K B (y0:real^1->real^N) (eta:real^1->real^N)
    s1 s2 M2.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ lricci_flow U ta tb Gt /\
     sa < s1 /\ s1 <= s2 /\ s2 < sb /\ &0 <= B /\
     (!s. s1 <= s /\ s <= s2 ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb) /\
     K SUBSET interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)) /\
     (!x y. segment[x,y] SUBSET K
            ==> norm(lift(p2a_llag Gt tt (drop(fstcart y)) (fstcart(sndcart y))
                                   (sndcart(sndcart y))) -
                     lift(p2a_llag Gt tt (drop(fstcart x)) (fstcart(sndcart x))
                                   (sndcart(sndcart x))) -
                     frechet_derivative
                       (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z))
                                   (sndcart(sndcart z)))) (at x) (y - x))
                <= B * norm(y - x) pow 2) /\
     (!s. s1 <= s /\ s <= s2
          ==> y0 differentiable (at (lift s)) /\
              (\v. vector_derivative y0 (at v)) continuous (at (lift s)) /\
              ((\v. vector_derivative y0 (at v)) has_vector_derivative
               p2a_lacc Gt tt s (y0(lift s)) (vector_derivative y0 (at (lift s)))) (at (lift s)) /\
              eta differentiable (at (lift s)) /\
              (\v. vector_derivative eta (at v)) continuous (at (lift s)) /\
              segment[pastecart (lift s) (pastecart (y0(lift s)) (vector_derivative y0 (at (lift s)))),
                      pastecart (lift s) (pastecart (y0(lift s) + eta(lift s))
                        (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))))]
              SUBSET K /\
              norm(pastecart (eta(lift s)) (vector_derivative eta (at (lift s)))) pow 2 <= M2)
     ==> abs(p2a_cL Gt tt (\v. y0 v + eta v) s1 s2 - p2a_cL Gt tt y0 s1 s2 -
             (eta(lift s2) dot (Gt(tt - s2 pow 2) (y0(lift s2)) **
                                vector_derivative y0 (at (lift s2))) -
              eta(lift s1) dot (Gt(tt - s1 pow 2) (y0(lift s1)) **
                                vector_derivative y0 (at (lift s1)))))
         <= B * M2 * (s2 - s1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "T") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TAY") (LABEL_TAC "H")))))))))) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_lsmooth]; ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (y0:real^1->real^N)(lift s) IN U /\
            y0(lift s) + (eta:real^1->real^N)(lift s) IN U /\
            vector_derivative (\v. y0 v + eta v) (at (lift s)) =
            vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s)) /\
            abs(p2a_llag Gt tt s (y0(lift s) + eta(lift s))
                  (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))) -
                p2a_llag Gt tt s (y0(lift s)) (vector_derivative y0 (at (lift s))) -
                (inv(&2) * (vector_derivative y0 (at (lift s)) dot
                            (mderiv (Gt(tt - s pow 2)) (y0(lift s)) (eta(lift s)) **
                             vector_derivative y0 (at (lift s)))) +
                 &2 * s pow 2 *
                 drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                         (at (y0(lift s))) (eta(lift s))) +
                 vector_derivative eta (at (lift s)) dot
                 (Gt(tt - s pow 2) (y0(lift s)) ** vector_derivative y0 (at (lift s)))))
            <= B * M2`
  (LABEL_TAC "PW") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "H" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "T" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `pastecart (lift s) (pastecart ((y0:real^1->real^N)(lift s))
                           (vector_derivative y0 (at (lift s)))) IN K /\
      pastecart (lift s) (pastecart (y0(lift s) + (eta:real^1->real^N)(lift s))
        (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s)))) IN K`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(y0:real^1->real^N)(lift s) IN U /\
                  y0(lift s) + (eta:real^1->real^N)(lift s) IN U`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `K SUBSET interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
        MP_TAC(SPEC `pastecart (lift s) (pastecart ((y0:real^1->real^N)(lift s))
                       (vector_derivative y0 (at (lift s))))` th) THEN
        MP_TAC(SPEC `pastecart (lift s) (pastecart (y0(lift s) + (eta:real^1->real^N)(lift s))
          (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))))` th)) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    USE_THEN "TAY" (MP_TAC o SPECL
      [`pastecart (lift s) (pastecart ((y0:real^1->real^N)(lift s))
                             (vector_derivative y0 (at (lift s))))`;
       `pastecart (lift s) (pastecart (y0(lift s) + (eta:real^1->real^N)(lift s))
          (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_SUB;
                VECTOR_SUB_REFL; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_PASTECART_0] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                   `(y0:real^1->real^N)(lift s)`; `vector_derivative (y0:real^1->real^N) (at (lift s))`;
                   `(eta:real^1->real^N)(lift s)`;
                   `vector_derivative (eta:real^1->real^N) (at (lift s))`] P2AL_LLAG_DW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M2` ASSUME_TAC THENL
   [USE_THEN "H" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(pastecart ((eta:real^1->real^N)(lift s1))
                               (vector_derivative eta (at (lift s1)))) pow 2` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2a_llag Gt tt s ((y0:real^1->real^N)(lift s) + (eta:real^1->real^N)(lift s))
           (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))))
    real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "H" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `\v. (y0:real^1->real^N) v + (eta:real^1->real^N) v`;
                   `\v. vector_derivative (y0:real^1->real^N) (at v) +
                        vector_derivative (eta:real^1->real^N) (at v)`; `s:real`]
                  P2AL_LG_CURVE_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2a_llag Gt tt s ((y0:real^1->real^N)(lift s)) (vector_derivative y0 (at (lift s))))
    real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "H" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `y0:real^1->real^N`;
                   `\v. vector_derivative (y0:real^1->real^N) (at v)`; `s:real`]
                  P2AL_LG_CURVE_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y0:real^1->real^N`; `\v. vector_derivative (y0:real^1->real^N) (at v)`;
                 `eta:real^1->real^N`; `\v. vector_derivative (eta:real^1->real^N) (at v)`;
                 `s1:real`; `s2:real`] P2AL_WEAK_EL_BDRY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "H" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "T" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    USE_THEN "H" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "T" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `y0:real^1->real^N`; `\v. vector_derivative (y0:real^1->real^N) (at v)`;
                   `eta:real^1->real^N`; `vector_derivative (eta:real^1->real^N) (at (lift s))`;
                   `s:real`] P2AL_EL_ETA_DERIV) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `p2a_cL Gt tt (\v. (y0:real^1->real^N) v + (eta:real^1->real^N) v) s1 s2 =
    real_integral (real_interval[s1,s2])
     (\s. p2a_llag Gt tt s (y0(lift s) + eta(lift s))
            (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2a_cL] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_cL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC P2AL_INT_BOUND3 THEN
  EXISTS_TAC `\s. p2a_llag Gt tt s ((y0:real^1->real^N)(lift s) + (eta:real^1->real^N)(lift s))
                    (vector_derivative y0 (at (lift s)) + vector_derivative eta (at (lift s)))` THEN
  EXISTS_TAC `\s. p2a_llag Gt tt s ((y0:real^1->real^N)(lift s))
                    (vector_derivative y0 (at (lift s)))` THEN
  EXISTS_TAC
   `\s. inv(&2) * (vector_derivative (y0:real^1->real^N) (at (lift s)) dot
                   (mderiv (Gt(tt - s pow 2)) (y0(lift s)) ((eta:real^1->real^N)(lift s)) **
                    vector_derivative y0 (at (lift s)))) +
        &2 * s pow 2 *
        drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                (at (y0(lift s))) (eta(lift s))) +
        vector_derivative eta (at (lift s)) dot
        (Gt(tt - s pow 2) (y0(lift s)) ** vector_derivative y0 (at (lift s)))` THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL; REAL_LE_MUL] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "PW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* A uniform tube around the window flow.  Near a base vector Z0 and on a    *)
(* compact time range [sa,sb] of a window, the states (s, y, A) of the flows *)
(* of Z with |Z - Z0| <= rz, moved by at most rho in (y,A), lie in one       *)
(* compact set K of the smooth domain of the Lagrangian, with one            *)
(* second-order Taylor constant B (GRGE_SMOOTH_TAYLOR1).                     *)
(* ========================================================================= *)

let P2AL_MARGIN = prove
 (`!(K0:real^M->bool) O.
     compact K0 /\ open O /\ K0 SUBSET O
     ==> ?rho. &0 < rho /\ !q v. q IN K0 /\ norm v <= rho ==> q + v IN O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K0:real^M->bool`; `(:real^M) DIFF O`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MAP_EVERY X_GEN_TAC [`q:real^M`; `v:real^M`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:real^M`; `q + v:real^M`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist; VECTOR_ARITH `q - (q + v):real^M = --v`; NORM_NEG] THEN
  ASM_REAL_ARITH_TAC);;

let P2AL_WIN_TUBE = prove
 (`!(V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi Z0 sa sb.
     p2al_lwa V tt sw r W a' b' U phi N Phi /\ Z0 IN N /\
     sw - r < sa /\ sa <= sb /\ sb < sw + r /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt sw r W b' U phi Phi Z0 s)
     ==> ?rz rho K B.
           &0 < rz /\ &0 < rho /\ &0 <= B /\
           (!Z s. Z IN cball(Z0,rz) /\ sa <= s /\ s <= sb
                  ==> Z IN N /\ p2al_lin V tt sw r W b' U phi Phi Z s) /\
           K SUBSET interval(lift(sw - r),lift(sw + r)) PCROSS
                    (IMAGE phi (U INTER W) PCROSS (:real^N)) /\
           (!x y. segment[x,y] SUBSET K
                  ==> norm(lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                                  (drop(fstcart y)) (fstcart(sndcart y)) (sndcart(sndcart y))) -
                           lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                                  (drop(fstcart x)) (fstcart(sndcart x)) (sndcart(sndcart x))) -
                           frechet_derivative
                             (\z. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                                         (drop(fstcart z)) (fstcart(sndcart z))
                                         (sndcart(sndcart z)))) (at x) (y - x))
                      <= B * norm(y - x) pow 2) /\
           (!Z s v. Z IN cball(Z0,rz) /\ sa <= s /\ s <= sb /\ norm v <= rho
                    ==> segment[pastecart (lift s) (p2al_lfl V tt sw r W b' U phi Phi Z s),
                                pastecart (lift s) (p2al_lfl V tt sw r W b' U phi Phi Z s) +
                                pastecart (vec 0) v] SUBSET K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_FV_K_SMOOTH) THEN
  MP_TAC(ISPECL [`{w:real^(N,1)finite_sum |
                   fstcart w IN N /\
                   p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (fstcart w)
                     (drop(sndcart w))}`;
                 `Z0:real^N`; `interval[lift sa,lift sb]`] NSPA_TUBE) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rz:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!Z s. Z IN cball(Z0:real^N,rz) /\ sa <= s /\ s <= sb
          ==> Z IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s`
  (LABEL_TAC "TUBE") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `lift s`] o check (fun th ->
      can (find_term ((=) `rz:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  ABBREV_TAC
   `K0 = IMAGE (\w:real^(N,1)finite_sum.
                  pastecart (sndcart w)
                    (p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (fstcart w)
                       (drop(sndcart w))))
               (cball(Z0:real^N,rz) PCROSS interval[lift sa,lift sb])` THEN
  SUBGOAL_THEN `compact(K0:real^(1,(N,N)finite_sum)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    SUBGOAL_THEN
     `(\w:real^(N,1)finite_sum.
         p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (fstcart w) (drop(sndcart w))) =
      (\z:real^(1,N)finite_sum. p2al_lfl V tt sw r W b' U phi Phi (sndcart z) (drop(fstcart z))) o
      (\w. pastecart (sndcart w) (fstcart w))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; LINEAR_FSTCART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^(1,N)finite_sum |
                 sndcart z IN N /\
                 p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (sndcart z)
                   (drop(fstcart z))}` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "TUBE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `K0 SUBSET interval(lift(sw - r),lift(sw + r)) PCROSS
              (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`
  ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "TUBE" (MP_TAC o SPECL [`Z:real^N`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open(interval(lift(sw - r),lift(sw + r)) PCROSS
         (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_UNIV] THEN ASM_MESON_TAC[p2a_lsmooth];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `interval(lift(sw - r),lift(sw + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`] P2AL_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `K = {q + y | q IN K0 /\
                 y IN IMAGE (\v:real^(N,N)finite_sum. pastecart (vec 0:real^1) v)
                            (cball(vec 0,rho))}` THEN
  SUBGOAL_THEN `compact(K:real^(1,(N,N)finite_sum)finite_sum->bool) /\
                K SUBSET interval(lift(sw - r),lift(sw + r)) PCROSS
                         (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_CBALL_0] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_PASTECART_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift(sw - r),lift(sw + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                 `K:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `\z:real^(1,(N,N)finite_sum)finite_sum.
                    lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt
                           (drop(fstcart z)) (fstcart(sndcart z)) (sndcart(sndcart z)))`]
                GRGE_SMOOTH_TAYLOR1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_LLAG_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`rz:real`; `rho:real`; `K:real^(1,(N,N)finite_sum)finite_sum->bool`;
                        `B:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^(1,(N,N)finite_sum)finite_sum`;
      `y:real^(1,(N,N)finite_sum)finite_sum`] o check (fun th ->
        can (find_term ((=) `B:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`; `v:real^(N,N)finite_sum`] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `p:real^(1,(N,N)finite_sum)finite_sum` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_CBALL_0] THEN
  EXISTS_TAC `pastecart (lift s) (p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s)` THEN
  EXISTS_TAC `pastecart (vec 0:real^1) (u % v:real^(N,N)finite_sum)` THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "K0" THEN REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY EXISTS_TAC [`Z:real^N`; `lift s`] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; IN_INTERVAL_1];
    EXISTS_TAC `u % v:real^(N,N)finite_sum` THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm(v:real^(N,N)finite_sum)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_LID]];
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % (a + b):real^M = a + u % b`] THEN
    REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]]);;

(* ========================================================================= *)
(* Small helpers for the competitor: first-order smallness along a line, the *)
(* window flow as a C^1 chart curve solving (6.5), affine fields, and the    *)
(* final arithmetic of the second-order argument.                            *)
(* ========================================================================= *)

let P2AL_LINE_SMALLO = prove
 (`!(f:real^N->real^M) f' Z0 c.
     (f has_derivative f') (at Z0)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. &0 < t /\ t < d
                         ==> norm(f(Z0 + t % c) - f Z0 - t % f' c) <= e * t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(c:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "D" (MP_TAC o SPEC `e / (norm(c:real^N) + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / (norm(c:real^N) + &1)` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Z0 + t % c:real^N`) THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; REAL_ARITH `&0 < t ==> abs t = t`] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * (norm(c:real^N) + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[real_div; REAL_ARITH `(e * i) * t * n = (e * t) * (n * i)`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* The window flow as a chart curve: C^1 with the second-order equation.    *)

let P2AL_FLOW_CURVE = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi Z s.
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < s /\ s < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z s
     ==> (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) differentiable
           (at (lift s)) /\
         vector_derivative (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)))
           (at (lift s)) = sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s) /\
         (\w. vector_derivative (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)))
                (at w)) continuous (at (lift s)) /\
         ((\w. vector_derivative (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)))
                 (at w)) has_vector_derivative
          p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
            (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s))
            (sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s))) (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Y")
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "E")))))))))))) THEN
  SUBGOAL_THEN
   `!w. dist(w,lift s) < e
        ==> vector_derivative (\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N)
                                           Phi Z (drop v))) (at w) =
            sndcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; DIST_LIFT; LIFT_DROP] THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    USE_THEN "E" (MP_TAC o SPEC `s':real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s':real`] P2AL_WOK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE];
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\w. sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop w))` THEN
    EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC P2AL_HVD_CONT THEN
    EXISTS_TAC `p2a_lacc (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt s
                  (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s))
                  (sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\w. sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop w))` THEN
    EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[]]);;

(* Affine fields eta(v) = (alpha (beta - v)) w.                              *)

let P2AL_AFF_FIELD = prove
 (`!alpha beta (w:real^N) x.
     ((\v. (alpha * (beta - drop v)) % w) has_vector_derivative (--alpha % w)) (at x) /\
     (\v. (alpha * (beta - drop v)) % w) differentiable (at x) /\
     vector_derivative (\v. (alpha * (beta - drop v)) % w) (at x) = --alpha % w /\
     (\y. vector_derivative (\v. (alpha * (beta - drop v)) % w) (at y)) continuous (at x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!x. ((\v. (alpha * (beta - drop v)) % (w:real^N)) has_vector_derivative (--alpha % w)) (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\v. (alpha * (beta - drop v)) % (w:real^N)) =
                  (\v. (alpha * beta) % w - drop v % (alpha % w))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(\h. drop h % --alpha % (w:real^N)) = (\h. vec 0 - drop h % (alpha % w))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. vector_derivative (\v. (alpha * (beta - drop v)) % (w:real^N)) (at y)) =
                (\y. --alpha % w)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONTINUOUS_CONST] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE];
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

(* The arithmetic of the competitor: with t = kappa eps, the second-order  *)
(* term -kappa eps^2 q0 dominates the remainders.                           *)

let P2AL_NEG_ARITH = prove
 (`!q0 C1 C2 nu.
     &0 < q0 /\ &0 <= C1 /\ &0 <= C2 /\ &0 <= nu
     ==> ?kappa e1 e2 e3.
           &0 < kappa /\ &0 < e1 /\ &0 < e2 /\ &0 < e3 /\
           !eps chi X R1 R2 nd.
             &0 < eps /\ abs chi <= e1 * eps pow 2 /\ abs(X - eps * q0) <= nu * e2 * eps /\
             abs R1 <= C1 * (kappa * eps) pow 2 /\ &0 <= nd /\ nd <= e3 * eps /\
             abs R2 <= C2 * (nd + kappa * eps * nu) pow 2
             ==> chi - kappa * eps * X + R1 + R2 < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C1 + &2 * C2 * nu pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `kappa = q0 / (&8 * ((C1 + &2 * C2 * nu pow 2) + &1))` THEN
  SUBGOAL_THEN `&0 < kappa /\
                kappa * (&8 * ((C1 + &2 * C2 * nu pow 2) + &1)) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kappa" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `e2 = q0 / (&8 * (nu + &1))` THEN
  SUBGOAL_THEN `&0 < e2 /\ e2 * (&8 * (nu + &1)) = q0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e2" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `g = (kappa * q0) / (&16 * (C2 + &1))` THEN
  SUBGOAL_THEN `&0 < g /\ g * (&16 * (C2 + &1)) = kappa * q0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `(kappa * q0) / &8`; `e2:real`; `min (&1) g`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `kappa * eps * (eps * q0 - nu * e2 * eps) <= kappa * eps * X` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `R2 <= C2 * (&2 * nd pow 2 + &2 * (kappa * eps * nu) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * (nd + kappa * eps * nu) pow 2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `nd - kappa * eps * nu` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C2 * nd pow 2 <= ((kappa * q0) / &16) * eps pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * (min (&1) g * eps) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `&0 <= min (&1) g /\ min (&1) g <= &1 /\ min (&1) g <= g` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * min (&1) g` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * g` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 * (kappa * (nu * e2)) <= eps pow 2 * (kappa * (q0 / &8))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 * (kappa * (kappa * (C1 + &2 * C2 * nu pow 2))) <=
                eps pow 2 * (kappa * (q0 / &8))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps pow 2 * (kappa * q0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The chart Taylor lemma in a window, for the window flow of a vector Z     *)
(* near Z0 perturbed by an affine field (alpha (beta - s)) w.                *)
(* ========================================================================= *)

let P2AL_MDERIV_VEC0 = prove
 (`!U (G:real^N->real^N^N) y. metric_field U G /\ y IN U ==> mderiv G y (vec 0) = mat 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                differentiable (at (y:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ASM_SIMP_TAC[P2AL_FD_ZERO; MATRIFY_0]]);;

let P2AL_SEG_FORM = prove
 (`!s (z:real^(N,N)finite_sum) e e'.
     pastecart (lift s) (pastecart (fstcart z + e) (sndcart z + e')) =
     pastecart (lift s) z + pastecart (vec 0) (pastecart e e') /\
     pastecart (lift s) (pastecart (fstcart z) (sndcart z)) = pastecart (lift s) z`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_ADD; SNDCART_ADD; FSTCART_PASTECART; SNDCART_PASTECART;
              VECTOR_ADD_RID]);;

let P2AL_SEG_END = prove
 (`!a b:real^M k. segment[a,b] SUBSET k ==> a IN k /\ b IN k`,
  MESON_TAC[ENDS_IN_SEGMENT; SUBSET]);;

let P2AL_CTL_WIN = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi Z0 sa sb rz rho K B Z
    alpha beta (w:real^N) s1 s2 Mn.
     p2al_wok V tt x sw r W a' b' U phi N Phi /\
     sw < sa /\ sa <= s1 /\ s1 <= s2 /\ s2 <= sb /\ sb < sw + r /\ &0 <= B /\ &0 <= Mn /\
     (!Z s. Z IN cball(Z0,rz) /\ sa <= s /\ s <= sb
            ==> Z IN N /\ p2al_lin V tt sw r W b' U phi Phi Z s) /\
     K SUBSET interval(lift(sw - r),lift(sw + r)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)) /\
     (!x y. segment[x,y] SUBSET K
            ==> norm(lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                            (drop(fstcart y)) (fstcart(sndcart y)) (sndcart(sndcart y))) -
                     lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                            (drop(fstcart x)) (fstcart(sndcart x)) (sndcart(sndcart x))) -
                     frechet_derivative
                       (\z. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt
                                   (drop(fstcart z)) (fstcart(sndcart z))
                                   (sndcart(sndcart z)))) (at x) (y - x))
                <= B * norm(y - x) pow 2) /\
     (!Z s v. Z IN cball(Z0,rz) /\ sa <= s /\ s <= sb /\ norm v <= rho
              ==> segment[pastecart (lift s) (p2al_lfl V tt sw r W b' U phi Phi Z s),
                          pastecart (lift s) (p2al_lfl V tt sw r W b' U phi Phi Z s) +
                          pastecart (vec 0) v] SUBSET K) /\
     Z IN cball(Z0,rz) /\
     (!s. s1 <= s /\ s <= s2
          ==> norm(pastecart ((alpha * (beta - s)) % w) (--alpha % w)) <= rho /\
              norm(pastecart ((alpha * (beta - s)) % w) (--alpha % w)) <= Mn)
     ==> (!s. s1 <= s /\ s <= s2
              ==> fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s) + (alpha * (beta - s)) % w
                  IN IMAGE phi (U INTER W)) /\
         abs(p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt
               (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)) +
                    (alpha * (beta - drop v)) % w) s1 s2 -
             p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt
               (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) s1 s2 -
             (((alpha * (beta - s2)) % w) dot
              (p2a_rlocal V W b' (U INTER W,phi) (tt - s2 pow 2)
                 (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s2)) **
               sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s2)) -
              ((alpha * (beta - s1)) % w) dot
              (p2a_rlocal V W b' (U INTER W,phi) (tt - s1 pow 2)
                 (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s1)) **
               sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s1))))
         <= B * Mn pow 2 * (s2 - s1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TUBE")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TAY")
    (CONJUNCTS_THEN2 (LABEL_TAC "SEG") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NRM")))))))))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (Z:real^N) IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s /\
            sw < s /\ s < sw + r`
  (LABEL_TAC "PTS") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "TUBE" (MP_TAC o SPECL [`Z:real^N`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> segment[pastecart (lift s) (p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s),
                    pastecart (lift s) (p2al_lfl V tt sw r W b' U phi Phi Z s) +
                    pastecart (vec 0) (pastecart ((alpha * (beta - s)) % w) (--alpha % w))]
            SUBSET K`
  (LABEL_TAC "SEGS") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "SEG" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "NRM" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "SEGS" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP P2AL_SEG_END) THEN
    REWRITE_TAC[GSYM(CONJUNCT1(SPEC_ALL P2AL_SEG_FORM))] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `pastecart (lift s)
        (pastecart (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s) +
                    (alpha * (beta - s)) % w)
                   (sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s) + --alpha % w)) IN
      interval(lift(sw - r),lift(sw + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N))`
    MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "PTS" (MP_TAC o SPEC `s1:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sw - r`; `sw + r`;
                 `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
                 `a':real`; `b':real`; `K:real^(1,(N,N)finite_sum)finite_sum->bool`; `B:real`;
                 `\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v))`;
                 `\v. (alpha * (beta - drop v)) % (w:real^N)`;
                 `s1:real`; `s2:real`; `Mn pow 2`] P2AL_CTL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "PTS" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                     `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                     `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "PTS" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_FLOW_CURVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[P2AL_AFF_FIELD; LIFT_DROP] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2AL_SEG_FORM] THEN USE_THEN "SEGS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    USE_THEN "NRM" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`] P2AL_FLOW_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "PTS" (MP_TAC o SPEC `s2:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s2:real`] P2AL_FLOW_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

(* ========================================================================= *)
(* The negative second variation at a conjugate point.  In a window around   *)
(* the first zero sz of J, with Y(sz) c = 0 and u = B(sz) c <> 0, the        *)
(* competitor data (gamma_{Z + eps c} up to sa, the chart pieces Y_{Z+eps c} *)
(* + eta1 on [sa,sz] and Y_Z + eta2 on [sz,sb], with linear fields eta1,     *)
(* eta2 and t = kappa eps) have total length change < 0 for small eps        *)
(* (P2AL_CORE_NEG).                                                          *)
(* ========================================================================= *)

let P2AL_AFF_NORM = prove
 (`!alpha beta (w:real^N) s1 s2 s.
     &0 <= alpha /\ s1 <= s /\ s <= s2 /\ (beta = s1 \/ beta = s2)
     ==> norm(pastecart ((alpha * (beta - s)) % w) (--alpha % w)) <=
         alpha * (s2 - s1) * norm w + alpha * norm w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `norm((alpha * (beta - s)) % (w:real^N)) + norm(--alpha % w)` THEN
   REWRITE_TAC[NORM_PASTECART_LE] THEN
   REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_ABS_MUL] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
   MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z`) THEN
   REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC));;

(* The estimates near Z along c at the conjugate time sz.                   *)

let P2AL_CORE_EST = prove
 (`!(V:p2alv) tt (x:A) b sw r W a' b' U (phi:A->real^N) N Phi Z c sz.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ Z IN p2a_Ldom V tt x b /\
     sw < sz /\ sz < sw + r /\ sz pow 2 < b /\
     p2al_lin V tt sw r W b' U phi Phi Z sz /\
     p2al_jy V tt sw r W b' U phi Phi Z sz ** c = vec 0
     ==> (!e. &0 < e
              ==> ?d. &0 < d /\
                      !t. &0 < t /\ t < d
                          ==> abs(p2a_Ltil V tt x (sz pow 2) (Z + t % c) -
                                  p2a_Ltil V tt x (sz pow 2) Z -
                                  ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) dot
                                  (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + t % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)))
                              <= e * t pow 2) /\
         (!e. &0 < e
              ==> ?d. &0 < d /\
                      !t. &0 < t /\ t < d
                          ==> norm(((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + t % c) sz)) **
                                    sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + t % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) -
                                   t % (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))) <= e * t) /\
         (!e. &0 < e
              ==> ?d. &0 < d /\
                      !t. &0 < t /\ t < d
                          ==> norm(fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + t % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))
                              <= e * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_LFL_HASDER_YB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
  REWRITE_TAC[FSTCART_PASTECART] THEN DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\Z. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)) (at Z) c = vec 0` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `sw:real`; `r:real`; `W:A->bool`;
                   `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`{Z' | Z' IN N /\ p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z' sz /\
             Z' IN p2a_Ldom V tt (x:A) b}`;
      `\Z:real^N. lift(p2a_Ltil (V:p2alv) tt (x:A) (sz pow 2) Z)`;
      `\Z. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)`;
      `\Z. (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)) ** sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)`;
      `Z:real^N`; `c:real^N`] P2AL_CHI_SMALL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP];
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_M_HASDER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real^N` o MATCH_MP P2AL_LINE_SMALLO) THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2))`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2)`;
                   `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)`] P2AL_MDERIV_VEC0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N` o MATCH_MP P2AL_LINE_SMALLO o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]]);;

let P2AL_DIV_BOUND = prove
 (`!x y A. &0 < x /\ &0 <= A /\ x < y / (A + &1) ==> x * A <= y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * (A + &1) < y` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= A ==> &0 < A + &1`];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC);;

let P2AL_CORE_NEG = prove
 (`!(V:p2alv) tt (x:A) b sw r W a' b' U (phi:A->real^N) N Phi Z c sa sz sb.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ Z IN p2a_Ldom V tt x b /\
     sw < sa /\ sa < sz /\ sz < sb /\ sb < sw + r /\ sz pow 2 < b /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt sw r W b' U phi Phi Z s) /\
     p2al_jy V tt sw r W b' U phi Phi Z sz ** c = vec 0 /\
     ~(p2al_jb V tt sw r W b' U phi Phi Z sz ** c = vec 0)
     ==> ?eps t.
           &0 < eps /\
           (!s. sa <= s /\ s <= sb
                ==> Z + eps % c IN N /\ p2al_lin V tt sw r W b' U phi Phi (Z + eps % c) s) /\
           (!s. sa <= s /\ s <= sz
                ==> fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) s) + ((t / (sz - sa)) * (sa - s)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)
                    IN IMAGE phi (U INTER W)) /\
           (!s. sz <= s /\ s <= sb
                ==> fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s) + (inv(sb - sz) * (sb - s)) % ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - t % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))
                    IN IMAGE phi (U INTER W)) /\
           (p2a_Ltil V tt x (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z) +
           (p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) (drop v)) + ((t / (sz - sa)) * (sa - drop v)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) sa sz -
            p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) (drop v))) sa sz) +
           (p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)) + (inv(sb - sz) * (sb - drop v)) % ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - t % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))) sz sb -
            p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) sz sb) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 < r`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok; p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:real^N`; `sz:real`]
                P2AL_CORE_EST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CHI") (CONJUNCTS_THEN2 (LABEL_TAC "MM")
    (LABEL_TAC "DEL"))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field (IMAGE (phi:A->real^N) (U INTER W)) ((p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) (tt - sz pow 2))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz)` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sa:real`; `sb:real`]
                P2AL_WIN_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rz:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `K:real^(1,(N,N)finite_sum)finite_sum->bool` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TUBE") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TAY") (LABEL_TAC "SEG"))))))))))) THEN
  MP_TAC(ISPECL [`(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`;
                 `B * (norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))) pow 2 * (sz - sa)`;
                 `B * (&1 + inv(sb - sz)) pow 2 * (sb - sz)`;
                 `norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`] P2AL_NEG_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `e2:real`
    (X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG"))))))))) THEN
  REMOVE_THEN "CHI" (MP_TAC o SPEC `e1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CHI1"))) THEN
  REMOVE_THEN "MM" (MP_TAC o SPEC `e2:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MM1"))) THEN
  REMOVE_THEN "DEL" (MP_TAC o SPEC `e3:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DEL1"))) THEN
  SUBGOAL_THEN `&0 < &1 + inv(sz - sa) /\ &0 < &1 + inv(sb - sz)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) /\
                &0 <= (e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[NORM_POS_LE] THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eps = min (min (min d1 d2) (min d3 (rz / (norm(c:real^N) + &1))))
                        (min (rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1))
                             (rho / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz)) + &1))) / &2` THEN
  SUBGOAL_THEN
   `&0 < eps /\ eps < d1 /\ eps < d2 /\ eps < d3 /\ eps < rz / (norm(c:real^N) + &1) /\
    eps < rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1) /\
    eps < rho / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz)) + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rz / (norm(c:real^N) + &1) /\
                  &0 < rho / (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) + &1) /\
                  &0 < rho / ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz)) + &1)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Z + eps % c IN cball(Z:real^N,rz)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL; dist; VECTOR_ARITH `a - (a + b):real^N = --b`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `eps * (norm(c:real^N) + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * (kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))) <= rho /\
                eps * ((e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz))) <= rho`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL_DIV_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `eps:real` THEN EXISTS_TAC `kappa * eps` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "TUBE" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sa <= sz /\ sz <= sb /\ &0 <= kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sa:real`; `sb:real`;
                 `rz:real`; `rho:real`; `K:real^(1,(N,N)finite_sum)finite_sum->bool`; `B:real`;
                 `Z + eps % c:real^N`; `(kappa * eps) / (sz - sa)`; `sa:real`; `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`;
                 `sa:real`; `sz:real`; `kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))`]
                P2AL_CTL_WIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(kappa * eps) / (sz - sa)`; `sa:real`; `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)`; `sa:real`; `sz:real`;
                   `s:real`] P2AL_AFF_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(kappa * eps) / (sz - sa) * (sz - sa) * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) +
                  (kappa * eps) / (sz - sa) * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) =
                  kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(sz - sa = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eps * kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa)) <= rho` THEN
    UNDISCH_TAC `norm(pastecart (((kappa * eps) / (sz - sa) * (sa - s)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c))
                                (--((kappa * eps) / (sz - sa)) % (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c))) <=
                 kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MEM1") (LABEL_TAC "CTL1")) THEN
  SUBGOAL_THEN `norm (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) <= e3 * eps` ASSUME_TAC THENL
   [USE_THEN "DEL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm ((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) <= norm (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) + kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
      `norm(y:real^N) = b ==> norm(x - y) <= norm x + b`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sa:real`; `sb:real`;
                 `rz:real`; `rho:real`; `K:real^(1,(N,N)finite_sum)finite_sum->bool`; `B:real`;
                 `Z:real^N`; `inv(sb - sz)`; `sb:real`; `((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`;
                 `sz:real`; `sb:real`; `norm ((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) * (&1 + inv(sb - sz))`]
                P2AL_CTL_WIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; CENTRE_IN_CBALL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`inv(sb - sz)`; `sb:real`; `((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`; `sz:real`; `sb:real`;
                   `s:real`] P2AL_AFF_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sb - sz) * (sb - sz) * norm ((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) + inv(sb - sz) * norm ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) =
                  norm ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) * (&1 + inv(sb - sz))` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(sb - sz = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm ((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) * (&1 + inv(sb - sz))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(e3 * eps + kappa * eps * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `eps * (e3 + kappa * norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c)) * (&1 + inv(sb - sz)) <= rho` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MEM2") (LABEL_TAC "CTL2")) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `abs(p2a_Ltil (V:p2alv) tt (x:A) (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z -
        ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) dot (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) <= e1 * eps pow 2`
  ASSUME_TAC THENL [USE_THEN "CHI1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) - eps * ((p2al_jb V tt sw r W b' U phi Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))) <= norm (p2al_jb V tt sw r W b' U phi Phi Z sz ** c) * e2 * eps`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_RMUL; GSYM DOT_RSUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * norm (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - eps % (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))) ** (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    USE_THEN "MM1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "CTL1" (MP_TAC o ONCE_REWRITE_RULE[REAL_RING
    `B * (kappa * eps * n * l) pow 2 * d = (B * (n * l) pow 2 * d) * (kappa * eps) pow 2`]) THEN
  DISCH_TAC THEN
  REMOVE_THEN "CTL2" (MP_TAC o ONCE_REWRITE_RULE[REAL_RING
    `B * (n * l) pow 2 * d = (B * l pow 2 * d) * n pow 2`]) THEN
  DISCH_THEN(LABEL_TAC "CTL2B") THEN
  FIRST_ASSUM((fun c1 -> USE_THEN "CTL2B" (fun c2 ->
    let r1 = rand(lhand(concl c1)) and r2 = rand(lhand(concl c2)) in
    USE_THEN "NEG" (MP_TAC o SPECL [`eps:real`;
      `p2a_Ltil (V:p2alv) tt (x:A) (sz pow 2) (Z + eps % c) - p2a_Ltil V tt x (sz pow 2) Z -
       ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) dot (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))`;
      `(p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) dot (((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz)) - ((p2a_rlocal V W b' (U INTER W,phi)) (tt - sz pow 2) (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) ** sndcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)))`; r1; r2; `norm (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz))`]))) o check (fun th ->
      can (find_term ((=) `B * (norm (p2al_jb (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z sz ** c) * (&1 + inv(sz - sa))) pow 2 * (sz - sa)`)) (concl th) &&
      is_comb(concl th) && is_comb(rator(concl th)) &&
      fst(dest_const(rator(rator(concl th)))) = "real_le")) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(B * (&1 + inv(sb - sz)) pow 2 * (sb - sz)) * norm ((fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - (kappa * eps) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y < &0 ==> x < &0`) THEN
  SUBGOAL_THEN `(kappa * eps) / (sz - sa) * (sa - sz) = --(kappa * eps) /\
                (kappa * eps) / (sz - sa) * (sa - sa) = &0 /\
                inv(sb - sz) * (sb - sb) = &0 /\ inv(sb - sz) * (sb - sz) = &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `~(sz - sa = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; DOT_LZERO; DOT_LNEG; DOT_LMUL; DOT_LSUB;
              DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The competitor on the manifold.  The L-geodesic of Z + eps c up to sa^2,  *)
(* the two chart pieces of P2AL_CORE_NEG on [sa^2,sz^2] and [sz^2,sb^2], and *)
(* gamma_Z after sb^2 form an admissible curve with the end point of gamma_Z *)
(* at b that is strictly shorter, so a minimizer has no window conjugate     *)
(* data (P2AL_NOCONJ_WIN).                                                   *)
(* ========================================================================= *)

(* Admissibility of L-geodesics from x and congruence of the L-length: the  *)
(* proofs of P2A_T81_LGEOD_ADM, P2A_T81_LGEO_ADM and P2A_T81_LENGTH_CONG of  *)
(* pc_p2a_t81 (copied; that unit is not loaded here).                        *)

let P2AL_LGEOD_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A).
     p2a_Lgeod V tt gamma b /\ gamma(&0) = x /\
     p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b]
     ==> p2a_adm V tt x b gamma`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2a_adm] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_Lgeod]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `sqrt tau0`; `O:A->bool`] P2A_LGEOD_CONT) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e pow 2` THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau`) THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - tau0))` THEN
    ASM_SIMP_TAC[REAL_ABS_LE_SQRT_POS] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(e pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    EXISTS_TAC `{}:real->bool` THEN MATCH_MP_TAC P2A_LGEOD_PC1 THEN ASM_REWRITE_TAC[]]);;

let P2AL_LGEO_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b
     ==> p2a_adm V tt x b (p2a_Lgeo V tt x Z b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL_LGEOD_ADM THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN REWRITE_TAC[p2a_Lgeod_from] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(Z:real^N) s. p2a_lsint (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt
                     (p2a_Lgeo V tt x Z b) b s`; `&0`; `sqrt b`; `{Z:real^N}`]
                P2A_PARAM_REAL_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; COMPACT_SING; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0,lift(sqrt b)] PCROSS
                p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LSINT_JOINT) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; GEOL_IN_PCROSS; IN_SING] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Z:real^N` o CONJUNCT1) THEN
  REWRITE_TAC[IN_SING; ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`;
                 `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x Z b`; `b:real`] P2A_L_LENGTH_SFORM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[real_integrable_on]);;

let P2AL_LENGTH_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma' b.
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau = gamma' tau)
     ==> p2a_L_length V tt gamma b = p2a_L_length V tt gamma' b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&0,b}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING] THEN
  X_GEN_TAC `tau:real` THEN
  REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The L-geodesics of Z at two levels agree on the common domain.          *)

let P2AL_LGEO_AGREE = prove
 (`!(V:p2alv) tt (x:A) Z b b1.
     p2a_svs V /\ Z IN p2a_Ldom V tt x b /\ &0 < b1 /\ b1 <= b
     ==> Z IN p2a_Ldom V tt x b1 /\
         !tau. &0 <= tau /\ tau <= b1 ==> p2a_Lgeo V tt x Z b1 tau = p2a_Lgeo V tt x Z b tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:p2alv) tt (x:A) (Z:real^N) b1 (p2a_Lgeo V tt x Z b)`
  ASSUME_TAC THENL [ASM_MESON_TAC[P2A_LGEOD_FROM_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b1` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_LGEOD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2A_LGEO_PROP]);;

(* Time range of a window.                                                    *)

let P2AL_WIN_TIME = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi s.
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ sw < s /\ s < sw + r
     ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_wok; p2al_lwa] THEN STRIP_TAC THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `sw:real` th) THEN MP_TAC(SPEC `s:real` th)) o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `b':real`)) (concl th) &&
                     not (can (find_term ((=) `Z:real^N`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
  SUBGOAL_THEN `sw pow 2 < s pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Additivity of L~ along a window.                                          *)

let P2AL_LTIL_ADD = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi Z s1 s2.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\
     sw < s1 /\ s1 <= s2 /\ s2 < sw + r /\
     (!s. s1 <= s /\ s <= s2 ==> p2al_lin V tt sw r W b' U phi Phi Z s)
     ==> p2a_Ltil V tt x (s2 pow 2) Z - p2a_Ltil V tt x (s1 pow 2) Z =
         p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) s1 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sw` ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s2:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  ABBREV_TAC `s3 = s2 + min e (sw + r - s2) / &2` THEN
  SUBGOAL_THEN `s2 < s3 /\ s3 < sw + r /\ abs(s3 - s2) < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s3:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s3:real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> ((\s'. p2a_Ltil (V:p2alv) tt (x:A) (s' pow 2) Z) has_real_derivative
             p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt s (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s)) (sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s))) (atreal s) /\
            p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (fstcart(p2al_lfl V tt sw r W b' U phi Phi Z s)) (sndcart(p2al_lfl V tt sw r W b' U phi Phi Z s)) =
            p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s ((\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) (lift s))
              (vector_derivative (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v))) (at (lift s)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s pow 2 < s3 pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s3 pow 2`; `Z:real^N`; `s:real`]
                    P2AL_LTIL_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC P2AL_WOK_LSINT THEN
      MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                     `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                     `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_FLOW_CURVE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s'. p2a_Ltil (V:p2alv) tt (x:A) (s' pow 2) Z`;
                 `\s. p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt s (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s)) (sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s))`;
                 `s1:real`; `s2:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN BETA_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[p2a_cL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Flow curve plus an affine field: C^1 at every window time.               *)

let P2AL_FLOW_AFF_CURVE = prove
 (`!(V:p2alv) tt (x:A) sw r W a' b' U (phi:A->real^N) N Phi Z alpha beta (w:real^N) s.
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ sw < s /\ s < sw + r /\
     p2al_lin V tt sw r W b' U phi Phi Z s
     ==> (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)) + (alpha * (beta - drop v)) % w) differentiable
           (at (lift s)) /\
         (\u. vector_derivative
                (\v. fstcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop v)) + (alpha * (beta - drop v)) % w) (at u))
           continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  SUBGOAL_THEN
   `!u. dist(u,lift s) < e
        ==> ((\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v)) + (alpha * (beta - drop v)) % (w:real^N))
             has_vector_derivative
             (sndcart(p2al_lfl V tt sw r W b' U phi Phi Z (drop u)) + --alpha % w)) (at u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; DIST_LIFT; LIFT_DROP] THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    USE_THEN "E" (MP_TAC o SPEC `s':real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s':real`] P2AL_FLOW_CURVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[P2AL_AFF_FIELD] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vector_derivative")) (concl th) &&
      is_eq(concl th))) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s) + --alpha % (w:real^N)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[DIST_REFL; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\u. sndcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop u)) + --alpha % (w:real^N)` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WIN_GCONT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* Gluing an admissible curve, two segments and the tail of an admissible   *)
(* curve (P2A_SEG_GLUE twice, then P2A_GLUE).                                *)

let P2AL_GLUE3 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (g0:real->A) sg1 sg2 gz b1 b2 b3.
     p2a_adm V tt x b1 g0 /\ p2a_lseg V tt b1 b2 sg1 /\ p2a_lseg V tt b2 b3 sg2 /\
     p2a_adm V tt x b gz /\ b3 < b /\
     g0 b1 = sg1 b1 /\ sg1 b2 = sg2 b2 /\ sg2 b3 = gz b3
     ==> ?gg. p2a_adm V tt x b gg /\ gg b = gz b /\
              p2a_L_length V tt gg b =
              p2a_L_length V tt g0 b1 +
              real_integral (real_interval[b1,b2]) (p2a_L_integrand V tt sg1 b2) +
              real_integral (real_interval[b2,b3]) (p2a_L_integrand V tt sg2 b3) +
              real_integral (real_interval[b3,b]) (p2a_L_integrand V tt gz b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b1 < b2 /\ b2 < b3` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_lseg]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sg1:real->A`; `g0:real->A`;
                 `\tau. if tau <= b1 then (g0:real->A) tau else sg1 tau`;
                 `b2:real`; `b1:real`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sg2:real->A`;
                 `\tau. if tau <= b1 then (g0:real->A) tau else sg1 tau`;
                 `\tau. if tau <= b2 then (if tau <= b1 then (g0:real->A) tau else sg1 tau)
                        else sg2 tau`;
                 `b3:real`; `b2:real`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b2 <= b1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TRANS];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gz:real->A`;
                 `\tau. if tau <= b2 then (if tau <= b1 then (g0:real->A) tau else sg1 tau)
                        else sg2 tau`;
                 `\tau. if tau <= b3
                        then (if tau <= b2 then (if tau <= b1 then (g0:real->A) tau else sg1 tau)
                              else sg2 tau)
                        else gz tau`;
                 `b:real`; `b3:real`] P2A_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b3 <= b2) /\ ~(b3 <= b1)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TRANS];
    STRIP_TAC] THEN
  EXISTS_TAC `\tau. if tau <= b3
                    then (if tau <= b2 then (if tau <= b1 then (g0:real->A) tau else sg1 tau)
                          else sg2 tau)
                    else gz tau` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(b <= b3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* No window conjugate data along a minimizer.                               *)

let P2AL_NOCONJ_WIN = prove
 (`!(V:p2alv) tt (x:A) b sw r W a' b' U (phi:A->real^N) N Phi Z c sa sz sb.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x sw r W a' b' U phi N Phi /\ Z IN N /\ Z IN p2a_Smin V tt x b /\
     sw < sa /\ sa < sz /\ sz < sb /\ sb < sw + r /\ sb pow 2 < b /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt sw r W b' U phi Phi Z s) /\
     p2al_jy V tt sw r W b' U phi Phi Z sz ** c = vec 0 /\
     ~(p2al_jb V tt sw r W b' U phi Phi Z sz ** c = vec 0)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2a_Smin; IN_ELIM_THM] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Smin")) (concl th))) THEN
  REWRITE_TAC[p2a_min] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt sw r W a' b' U (phi:A->real^N) N Phi /\ &0 <= sw`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ p2a_region (V:p2alv) W a' b' /\ (U,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sa /\ sa pow 2 < sz pow 2 /\ sz pow 2 < sb pow 2 /\ sz pow 2 < b`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sa pow 2 < sz pow 2 /\ sz pow 2 < sb pow 2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:real^N`; `sa:real`;
                 `sz:real`; `sb:real`] P2AL_CORE_NEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `t:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "LINE")
    (CONJUNCTS_THEN2 (LABEL_TAC "M1") (CONJUNCTS_THEN2 (LABEL_TAC "M2") (LABEL_TAC "NEG"))))))) THEN
  SUBGOAL_THEN `!s. sw < s /\ s < sw + r ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'`
  (LABEL_TAC "TIME") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AL_WIN_TIME THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `U:A->bool`;
                          `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < b'` ASSUME_TAC THENL
   [USE_THEN "TIME" (MP_TAC o SPEC `sz:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "LINE" (MP_TAC o SPEC `sa:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z + eps % c:real^N`; `sa:real`]
                P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sb:real`]
                P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `(\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (drop v)) + ((t / (sz - sa)) * (sa - drop v)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))`; `sa:real`; `sz:real`; `sw:real`; `sw + r`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "M1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LINE" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC P2AL_FLOW_AFF_CURVE THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `N:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP]) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `(\v. fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (drop v)) + (inv(sb - sz) * (sb - drop v)) % ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - t % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))`; `sz:real`; `sb:real`; `sw:real`; `sw + r`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "M2" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AL_FLOW_AFF_CURVE THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `N:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP]) THEN
  SUBGOAL_THEN `(t / (sz - sa)) * (sa - sz) = --t /\ inv(sb - sz) * (sb - sz) = &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `~(sz - sa = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sz /\ &0 <= sb` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`;
                 `p2a_Lgeo (V:p2alv) tt (x:A) (Z + eps % c) (sa pow 2)`;
                 `(\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi (Z + eps % c) (sqrt tau)) + ((t / (sz - sa)) * (sa - sqrt tau)) % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c)))`; `(\tau. chart_inv (U INTER W,phi:A->real^N) (fstcart(p2al_lfl (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z (sqrt tau)) + (inv(sb - sz) * (sb - sqrt tau)) % ((fstcart(p2al_lfl V tt sw r W b' U phi Phi (Z + eps % c) sz) - fstcart(p2al_lfl V tt sw r W b' U phi Phi Z sz)) - t % (p2al_jb V tt sw r W b' U phi Phi Z sz ** c))))`; `p2a_Lgeo (V:p2alv) tt (x:A) Z b`;
                 `sa pow 2`; `sz pow 2`; `sb pow 2`] P2AL_GLUE3) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2AL_LGEO_ADM] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO;
                 VECTOR_ADD_RID; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `sa pow 2`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
      MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                     `phi:A->real^N`;
                     `p2a_Lexp (V:p2alv) tt (x:A) (sa pow 2) (Z + eps % c)`]
                    P2A_REGION_CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2a_Lexp];
      AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_ACCEPT_TAC(VECTOR_ARITH
        `!a b t (u:real^N). a + --t % u = b + &1 % ((a - b) - t % u)`);
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `sb pow 2`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lexp")) (concl th))) THEN
      MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                     `phi:A->real^N`; `p2a_Lexp (V:p2alv) tt (x:A) (sb pow 2) Z`]
                    P2A_REGION_CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2a_Lexp] THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `sb pow 2`]
                    P2AL_LGEO_AGREE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_POW_2]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gg:real->A` STRIP_ASSUME_TAC) THEN
  USE_THEN "MIN" (MP_TAC o SPEC `gg:real->A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `p2a_Lgeo (V:p2alv) tt (x:A) Z b`; `b:real`;
                 `sb pow 2`] P2A_LENGTH_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `p2a_L_length (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) (sb pow 2) =
                p2a_Ltil V tt x (sb pow 2) Z` SUBST1_TAC THENL
   [REWRITE_TAC[p2a_Ltil] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AL_LENGTH_CONG THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `sb pow 2`]
                  P2AL_LGEO_AGREE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_L_length (V:p2alv) tt (p2a_Lgeo V tt (x:A) (Z + eps % c) (sa pow 2))
                  (sa pow 2) = p2a_Ltil V tt x (sa pow 2) (Z + eps % c)` SUBST1_TAC THENL
   [REWRITE_TAC[p2a_Ltil]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> SUBST1_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th)) THEN
  FIRST_X_ASSUM(fun th -> SUBST1_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th)) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z + eps % c:real^N`; `sa:real`; `sz:real`]
                P2AL_LTIL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "LINE" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`; `sb:real`]
                P2AL_LTIL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "NEG" MP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* No conjugate points before the end of a minimizing L-geodesic             *)
(* (P2AL_NO_CONJ), and L5 P2A_RVI_MONO (the reduced-volume integrand is      *)
(* non-increasing along minimizers), generic in N and at N = 3.              *)
(* ========================================================================= *)

let P2AL_LDOM_TOPSPACE = prove
 (`!(V:p2alv) tt (x:A) b Z. Z IN p2a_Ldom V tt x b ==> x IN topspace(p2a_vtop V tt)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2AL_NO_CONJ = prove
 (`!(V:p2alv) tt (x:A) b Z s.
     p2a_svs V /\ p2a_bsmooth V x tt /\ Z IN p2a_Smin V tt x b /\ &0 < s /\ s pow 2 < b
     ==> &0 < p2a_J V tt x (s pow 2) Z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:p2alv) tt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2AL_LDOM_TOPSPACE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= j /\ ~(j = &0) ==> &0 < j`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_J_NONNEG THEN EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`]
                P2AL_FIRST_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `sz:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sz pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sz:real`]
                P2AL_CONJ_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sw:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` (X_CHOOSE_THEN `c:real^N`
     STRIP_ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sz:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  SUBGOAL_THEN `sz < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d = min (e / &2) ((sqrt b - sz) / &2)` THEN
  SUBGOAL_THEN `&0 < d /\ d < e /\ sz + d < sqrt b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. sz - d <= s' /\ s' <= sz + d
         ==> sw < s' /\ s' < sw + r /\
             p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s'`
  (LABEL_TAC "IN") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "E" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sz + d) pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_POW_2 THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sw < sz - d /\ sz + d < sw + r /\ sz - d < sz /\ sz < sz + d /\
    (!s'. sz - d <= s' /\ s' <= sz + d
          ==> p2al_lin (V:p2alv) tt sw r W b' U (phi:A->real^N) Phi Z s')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [USE_THEN "IN" (MP_TAC o SPEC `sz - d`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "IN" (MP_TAC o SPEC `sz + d`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      GEN_TAC THEN DISCH_TAC THEN USE_THEN "IN" (MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `sw:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:real^N`;
                 `sz - d`; `sz:real`; `sz + d`] P2AL_NOCONJ_WIN) THEN
  ASM_REWRITE_TAC[]);;

let P2AL_NO_CONJ_TAU = prove
 (`!(V:p2alv) tt (x:A) b Z tau.
     p2a_svs V /\ p2a_bsmooth V x tt /\ Z IN p2a_Smin V tt x b /\ &0 < tau /\ tau < b
     ==> &0 < p2a_J V tt x tau Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sqrt tau`]
                P2AL_NO_CONJ) THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT]);;

(* L5, generic in N.                                                          *)

let P2AL_RVI_MONO_N = prove
 (`!(V:p2alv) tt (x:A) b Z b1 b2.
     p2a_svs V /\ p2a_bsmooth V x tt /\ Z IN p2a_Smin V tt x b /\
     &0 < b1 /\ b1 <= b2 /\ b2 <= b
     ==> p2a_rvi V tt x b2 Z <= p2a_rvi V tt x b1 Z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Smin; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:p2alv) tt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2AL_LDOM_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s pow 2 < b ==> &0 < p2a_J (V:p2alv) tt (x:A) (s pow 2) Z`
  (LABEL_TAC "NC") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL_NO_CONJ THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b1 /\ sqrt b1 <= sqrt b2 /\ sqrt b1 pow 2 = b1 /\
                sqrt b2 pow 2 = b2 /\ &0 < sqrt b2 /\ &0 < b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SQRT_LT_0] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `b2 < b` THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sqrt b2`]
                  P2AL_RVI_DECREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "NC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b2:real` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `sqrt b2 pow 2 = b2`)] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`sqrt b1`; `sqrt b2`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `b2:real = b` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p2a_J (V:p2alv) tt (x:A) b Z = &0` THENL
   [ASM_REWRITE_TAC[p2a_rvi; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `sqrt b1 pow 2 = b1`)) THEN
      MATCH_MP_TAC P2AL_J_NONNEG THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_J (V:p2alv) tt (x:A) b Z` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= j /\ ~(j = &0) ==> &0 < j`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sqrt b`]
                  P2AL_J_NONNEG) THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `sqrt b`]
                P2AL_LWIN_NEAR) THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `sw:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `sqrt b`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E")) o
             last o CONJUNCTS) THEN
  ABBREV_TAC `s' = sqrt b + min e (sw + r - sqrt b) / &2` THEN
  SUBGOAL_THEN `sqrt b < s' /\ abs(s' - sqrt b) < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "E" (MP_TAC o SPEC `s':real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `sw:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s':real`] P2AL_WOK_LGEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s' pow 2`; `Z:real^N`; `sqrt b`]
                P2AL_RVI_DECREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `sqrt b pow 2 < s' pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
        MP_TAC(SPEC `b:real` SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = sqrt b` THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "NC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`sqrt b1`; `sqrt b`]) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; SQRT_POW_2; REAL_LT_IMP_LE]);;

(* The headline L5 at N = 3 (P2A_RVI_MONO_STATEMENT of pc_p2a_defs).         *)

let P2A_RVI_MONO = prove
 (`!u:A->bool. P2A_RVI_MONO_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_RVI_MONO_STATEMENT] THEN
  MATCH_ACCEPT_TAC(INST_TYPE [`:3`,`:N`] P2AL_RVI_MONO_N));;

