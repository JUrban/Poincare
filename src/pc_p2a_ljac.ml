(* ========================================================================= *)
(* Unit pc_p2a_ljac: view level of the Riccati comparison along an           *)
(* L-geodesic from x.  Windows: around every s in (0, sqrt b] the            *)
(* L-geodesics with initial vectors near Z0 are, in one region chart and for *)
(* s' in a two-sided s-interval, given by the flow of the system (6.5) from  *)
(* a base point s1 < s (P2A_LPROP_NEAR of pc_p2a_lgeo3, P2AL_FLOW_LGEOD);    *)
(* this gives the Jacobi matrix Y = D_Z y, its velocity B, the Jacobian J    *)
(* and the L-length in charts, the first variation formula D_Z Ltil(Z,s^2) c *)
(* = (Y c) . (G A) (P2AL_FV_ALL) and the self-adjointness of the shape       *)
(* operator (P2AL_WOK_SYM).  Dimension-generic in N.                         *)
(*                                                                           *)
(* First: the L-geodesics given by the window flow.                          *)
(* ========================================================================= *)

needs "src/pc_p2a_lric.ml";;
needs "src/pc_p2a_lconv.ml";;
needs "src/pc_pde_torus.ml";;

prioritize_real();;
type_invention_error := true;;

(* Parsing abbreviation for the view type (generic in A and N).            *)

new_type_abbrev("p2alv",
  `:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`);;

(* The proof of P2AL_FLOW_LGEOD is the second half of the proof of           *)
(* P2A_LPROP_FLOW (pc_p2a_lgeo3): the window flow from s1 of the propagation *)
(* data gives the L-geodesics up to every later s2 in the window.            *)

let P2AL_FLOW_LGEOD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x s1 N W a' b' U (phi:A->real^N) r (Phi:real^N->real^(N,N)finite_sum) s2 Z.
     open N /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < r /\ (!s'. abs(s' - s1) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
     smooth_map_on N Phi /\
     (!Z. Z IN N
          ==> ?gamma. p2a_Lgeod_from V tt x Z (s1 pow 2) gamma /\
                      gamma(s1 pow 2) IN U INTER W /\
                      phi(gamma(s1 pow 2)) = fstcart(Phi Z) /\
                      ((\v. phi(gamma(drop v pow 2))) has_vector_derivative sndcart(Phi Z))
                        (at (lift s1) within {v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2})) /\
     &0 < s1 /\ s1 < s2 /\ s2 < s1 + r /\ Z IN N /\
     pastecart (lift s2) (pastecart (lift s1) (Phi Z)) IN
       ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
         (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
     ==> ?gamma. p2a_Lgeod_from V tt x Z (s2 pow 2) gamma /\
                 gamma(s2 pow 2) IN U INTER W /\
                 phi(gamma(s2 pow 2)) =
                 fstcart(ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                           (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                            (IMAGE phi (U INTER W) PCROSS (:real^N)))
                           (lift s2) (pastecart (lift s1) (Phi Z))) /\
                 ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
                  sndcart(ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                           (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                            (IMAGE phi (U INTER W) PCROSS (:real^N)))
                           (lift s2) (pastecart (lift s1) (Phi Z))))
                   (at (lift s2) within {v | &0 <= drop v /\ drop v pow 2 <= s2 pow 2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'
                   (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  (* ODE facts *)
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b') W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b') W`;
      `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `s1 - r`; `s1 + r`] P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a' b'` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N` o check (fun th ->
  is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "Z")) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z = pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z)` THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
               `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s2`;
               `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
               `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
               `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fstcart(z:real^(1,(N,N)finite_sum)finite_sum) = lift s1 /\
              sndcart z = (Phi:real^N->real^(N,N)finite_sum) Z`
  STRIP_ASSUME_TAC THENL
 [EXPAND_TAC "z" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D z` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `gamma:real->A`; `s1 pow 2`; `s2 pow 2`;
               `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
               `s1 - r`; `s1 + r`;
               `\t. fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                     D t z)`;
               `\t. sndcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                     D t z)`;
               `J:real^1->bool`] P2A_LGEOD_FROM_GLUE) THEN
  SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2 /\ s1 pow 2 < s2 pow 2`
  STRIP_ASSUME_TAC THENL
 [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
  ALL_TAC] THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN
  ANTS_TAC THENL
 [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC;
  ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC
 `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
        else chart_inv (U INTER W,phi:A->real^N)
               (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                 D (lift(sqrt tau)) z))` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Windows.  p2al_lwa is the analytic part of a window (a region chart, a    *)
(* time interval around s1 and a smooth initial state Phi), p2al_lwin adds   *)
(* the propagation data at a base point s1 > 0 (as in P2A_LPROP_NEAR),       *)
(* p2al_lfl is the window flow of (6.5) from s1 and p2al_lin its domain.     *)
(* ========================================================================= *)

let p2al_lwa = new_definition
 `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N
           (Phi:real^N->real^(N,N)finite_sum) <=>
    &0 < r /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
    (!s'. abs(s' - s1) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
    open N /\ smooth_map_on N Phi`;;

let p2al_lwin = new_definition
 `p2al_lwin (V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N
            (Phi:real^N->real^(N,N)finite_sum) <=>
    &0 < s1 /\ p2al_lwa V tt s1 r W a' b' U phi N Phi /\
    (!Z. Z IN N
         ==> ?gamma. p2a_Lgeod_from V tt x Z (s1 pow 2) gamma /\
                     gamma(s1 pow 2) IN U INTER W /\
                     phi(gamma(s1 pow 2)) = fstcart(Phi Z) /\
                     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative sndcart(Phi Z))
                       (at (lift s1) within {v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2}))`;;

let p2al_lfl = new_definition
 `p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
           (Z:real^N) (s:real) =
    ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
             (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
             (lift s) (pastecart (lift s1) (Phi Z))`;;

let p2al_lin = new_definition
 `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
           (Z:real^N) (s:real) <=>
    pastecart (lift s) (pastecart (lift s1) (Phi Z)) IN
    ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
               (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))`;;

let P2AL_LWIN_NEAR = prove
 (`!(V:p2alv) tt (x:A) Z0 b0 Tm.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b0 /\ &0 < Tm /\ Tm pow 2 <= b0
     ==> ?s1 r W a' b' U (phi:A->real^N) N Phi.
           p2al_lwin V tt x s1 r W a' b' U phi N Phi /\ s1 < Tm /\ Tm < s1 + r /\
           Z0 IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z0 Tm`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LPROP_NEAR) THEN
  REWRITE_TAC[p2al_lwin; p2al_lwa; p2al_lin] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2AL_LWIN_LGEOD = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z s2.
     p2al_lwin V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 < s2 /\ s2 < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z s2
     ==> ?gamma. p2a_Lgeod_from V tt x Z (s2 pow 2) gamma /\
                 gamma(s2 pow 2) IN U INTER W /\
                 phi(gamma(s2 pow 2)) = fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s2) /\
                 ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
                  sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s2))
                   (at (lift s2) within {v | &0 <= drop v /\ drop v pow 2 <= s2 pow 2})`,
  REWRITE_TAC[p2al_lwin; p2al_lwa; p2al_lin; p2al_lfl] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2AL_FLOW_LGEOD THEN
  MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `a':real`] THEN ASM_REWRITE_TAC[]);;

let P2AL_IN_UNIV_PCROSS = prove
 (`!(z:real^(1,N)finite_sum) S. z IN (:real^1) PCROSS S <=> sndcart z IN S`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV]);;

let P2AL_IN_PCROSS_UNIV = prove
 (`!(w:real^(N,N)finite_sum) S. w IN S PCROSS (:real^N) <=> fstcart w IN S`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV]);;

let P2AL_LWIN_FACTS = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi.
     p2al_lwa V tt s1 r W a' b' U phi N Phi
     ==> p2a_lsmooth (IMAGE phi (U INTER W)) (s1 - r) (s1 + r)
           (\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) /\
         open {z | sndcart z IN N /\
                   p2al_lin V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))} /\
         smooth_map_on {z | sndcart z IN N /\
                            p2al_lin V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))}
           (\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))) /\
         (!Z s. Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s
                ==> abs(s - s1) < r /\
                    fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s) IN IMAGE phi (U INTER W) /\
                    (?e. &0 < e /\
                         !s'. abs(s' - s) < e ==> p2al_lin V tt s1 r W b' U phi Phi Z s') /\
                    ((\v. p2al_lfl V tt s1 r W b' U phi Phi Z (drop v)) has_vector_derivative
                     p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt
                       (pastecart (lift s) (p2al_lfl V tt s1 r W b' U phi Phi Z s))) (at (lift s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_lwa] THEN STRIP_TAC THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
      (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2al_lin; p2al_lfl] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (N:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((:real^1) PCROSS N)
      (\z. pastecart (fstcart z) (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum)
                                                        (sndcart z))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1) PCROSS (N:real^N->bool)`; `\z:real^(1,N)finite_sum. z`]
                    SMOOTH_MAP_ON_FSTCART_OPEN) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (Phi:real^N->real^(N,N)finite_sum)(sndcart z)) =
                  Phi o sndcart` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART];
      MP_TAC(ISPECL [`(:real^1) PCROSS (N:real^N->bool)`; `\z:real^(1,N)finite_sum. z`]
                    SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{z | sndcart z IN N /\
         pastecart (fstcart z) (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum)
                                                      (sndcart z))) IN
         ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D} =
    {z | z IN (:real^1) PCROSS N /\
         (\z. pastecart (fstcart z) (pastecart (lift s1) (Phi (sndcart z)))) z IN
         ode_domain f D}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; P2AL_IN_UNIV_PCROSS];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\z. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (fstcart z)
             (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) (sndcart z)))) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o
      (\z. pastecart (fstcart z) (pastecart (lift s1) (Phi (sndcart z))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^1) PCROSS (N:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `z = pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z)` THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pastecart (lift s) (ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                 D (lift s) z) IN D` THEN
  EXPAND_TAC "D" THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; P2AL_IN_PCROSS_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
      concl th = `open(ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D z)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    REWRITE_TAC[ODE_IN_DOMAIN] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The variational equation in a window.  The state derivative of the field  *)
(* of (6.5) is (dy,dA) |-> (dA, D_y lacc dy + D_A lacc dA)                   *)
(* (P2AL_LFIELD_DSTATE); the Jacobi matrix Y = D_Z y and B = D_Z A of the    *)
(* window flow satisfy Y' = B, B' = Ly Y + LA B (P2AL_LWIN_JACOBI).          *)
(* ========================================================================= *)

let P2AL_PARTIALS2 = prove
 (`!(g:real^(1,(N,N)finite_sum)finite_sum->real^M) s0 y0 A0 dy dA.
     g differentiable (at (pastecart s0 (pastecart y0 A0)))
     ==> frechet_derivative g (at (pastecart s0 (pastecart y0 A0)))
           (pastecart (vec 0) (pastecart dy dA)) =
         frechet_derivative (\y. g(pastecart s0 (pastecart y A0))) (at y0) dy +
         frechet_derivative (\w. g(pastecart s0 (pastecart y0 w))) (at A0) dA`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  SUBGOAL_THEN
   `((\y. (g:real^(1,(N,N)finite_sum)finite_sum->real^M) (pastecart s0 (pastecart y A0)))
     has_derivative (\h. frechet_derivative g (at (pastecart s0 (pastecart y0 A0)))
                           (pastecart (vec 0) (pastecart h (vec 0))))) (at y0) /\
    ((\w. g (pastecart s0 (pastecart y0 w)))
     has_derivative (\h. frechet_derivative g (at (pastecart s0 (pastecart y0 A0)))
                           (pastecart (vec 0) (pastecart (vec 0) h)))) (at A0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y:real^N. pastecart (s0:real^1) (pastecart y (A0:real^N))`;
                     `g:real^(1,(N,N)finite_sum)finite_sum->real^M`;
                     `\h:real^N. pastecart (vec 0:real^1) (pastecart h (vec 0:real^N))`;
                     `frechet_derivative (g:real^(1,(N,N)finite_sum)finite_sum->real^M)
                        (at (pastecart s0 (pastecart y0 A0)))`; `y0:real^N`] DIFF_CHAIN_AT);
      MP_TAC(ISPECL [`\w:real^N. pastecart (s0:real^1) (pastecart (y0:real^N) w)`;
                     `g:real^(1,(N,N)finite_sum)finite_sum->real^M`;
                     `\h:real^N. pastecart (vec 0:real^1) (pastecart (vec 0:real^N) h)`;
                     `frechet_derivative (g:real^(1,(N,N)finite_sum)finite_sum->real^M)
                        (at (pastecart s0 (pastecart y0 A0)))`; `A0:real^N`] DIFF_CHAIN_AT)] THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. (g:real^(1,(N,N)finite_sum)finite_sum->real^M)
                              (pastecart s0 (pastecart y A0))) (at y0) =
    (\h. frechet_derivative g (at (pastecart s0 (pastecart y0 A0)))
           (pastecart (vec 0) (pastecart h (vec 0)))) /\
    frechet_derivative (\w. g (pastecart s0 (pastecart y0 w))) (at A0) =
    (\h. frechet_derivative g (at (pastecart s0 (pastecart y0 A0)))
           (pastecart (vec 0) (pastecart (vec 0) h)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable"))
                         (concl th))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
  REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]);;

let P2AL_SLICE_HASDER = prove
 (`!(c:real^1) (y:real^N) (A:real^N) (net:(real^N)net).
     ((\z:real^N. pastecart c (pastecart z A)) has_derivative
      (\h:real^N. pastecart (vec 0:real^1) (pastecart h (vec 0:real^N)))) net /\
     ((\w:real^N. pastecart c (pastecart y w)) has_derivative
      (\h:real^N. pastecart (vec 0:real^1) (pastecart (vec 0:real^N) h))) net`,
  REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID]);;

let P2AL_LFIELD_DSTATE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt s y A dy dA.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s /\ s < sb /\ y IN U
     ==> (\z. p2a_lacc Gt tt s z A) differentiable (at y) /\
         (\w. p2a_lacc Gt tt s y w) differentiable (at A) /\
         frechet_derivative (p2a_lfield Gt tt) (at (pastecart (lift s) (pastecart y A)))
           (pastecart (vec 0) (pastecart dy dA)) =
         pastecart dA (frechet_derivative (\z. p2a_lacc Gt tt s z A) (at y) dy +
                       frechet_derivative (\w. p2a_lacc Gt tt s y w) (at A) dA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LFIELD_SMOOTH) THEN
  SUBGOAL_THEN `open(interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_UNIV] THEN ASM_MESON_TAC[p2a_lsmooth];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. (p2a_lfield (Gt:real->real^N->real^N^N) tt) differentiable
                             (at (pastecart (lift s) (pastecart y w)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z IN U ==> (p2a_lfield (Gt:real->real^N->real^N^N) tt) differentiable
                                        (at (pastecart (lift s) (pastecart z A)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. p2a_lacc (Gt:real->real^N->real^N^N) tt s z A) differentiable (at y) /\
    (\w. p2a_lacc Gt tt s y w) differentiable (at A)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. p2a_lacc (Gt:real->real^N->real^N^N) tt s z A) =
      sndcart o p2a_lfield Gt tt o (\z. pastecart (lift s) (pastecart z A)) /\
      p2a_lacc Gt tt s y =
      sndcart o p2a_lfield Gt tt o (\w. pastecart (lift s) (pastecart y w))`
    (fun th -> REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART;
                  LIFT_DROP];
      ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
    SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_SNDCART] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_SIMP_TAC[o_THM] THEN
    REWRITE_TAC[differentiable] THENL
     [EXISTS_TAC `\h:real^N. pastecart (vec 0:real^1) (pastecart h (vec 0:real^N))`;
      EXISTS_TAC `\h:real^N. pastecart (vec 0:real^1) (pastecart (vec 0:real^N) h)`] THEN
    REWRITE_TAC[P2AL_SLICE_HASDER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2a_lfield (Gt:real->real^N->real^N^N) tt`; `lift s`; `y:real^N`; `A:real^N`;
                 `dy:real^N`; `dA:real^N`] P2AL_PARTIALS2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(\y'. p2a_lfield (Gt:real->real^N->real^N^N) tt (pastecart (lift s) (pastecart y' A))) =
    (\y'. pastecart A (p2a_lacc Gt tt s y' A)) /\
    (\w. p2a_lfield Gt tt (pastecart (lift s) (pastecart y w))) =
    (\w. pastecart w (p2a_lacc Gt tt s y w))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y'. pastecart (A:real^N) (p2a_lacc (Gt:real->real^N->real^N^N) tt s y' A))
                       (at y) =
    (\h. pastecart (vec 0) (frechet_derivative (\z. p2a_lacc Gt tt s z A) (at y) h)) /\
    frechet_derivative (\w. pastecart w (p2a_lacc Gt tt s y w)) (at A) =
    (\h. pastecart h (frechet_derivative (\w. p2a_lacc Gt tt s y w) (at A) h))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID] THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID]);;

let P2AL_FLW_SMOOTH = prove
 (`!(f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D t0.
     open D /\ smooth_map_on D f
     ==> open {w | pastecart (fstcart w) (pastecart t0 (sndcart w)) IN ode_domain f D} /\
         smooth_map_on {w | pastecart (fstcart w) (pastecart t0 (sndcart w)) IN ode_domain f D}
           (\w. ode_flow f D (fstcart w) (pastecart t0 (sndcart w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,(N,N)finite_sum)finite_sum)
      (\w:real^(1,(N,N)finite_sum)finite_sum. pastecart (fstcart w) (pastecart (t0:real^1) (sndcart w)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^(1,(N,N)finite_sum)finite_sum)`; `\z:real^(1,(N,N)finite_sum)finite_sum. z`]
                    SMOOTH_MAP_ON_FSTCART_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`(:real^(1,(N,N)finite_sum)finite_sum)`; `\z:real^(1,(N,N)finite_sum)finite_sum. z`]
                    SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | pastecart (fstcart w) (pastecart (t0:real^1) (sndcart w)) IN
         ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D} =
    {w | w IN (:real^(1,(N,N)finite_sum)finite_sum) /\
         (\w. pastecart (fstcart w) (pastecart t0 (sndcart w))) w IN ode_domain f D}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (fstcart w)
           (pastecart (t0:real^1) (sndcart w))) =
    (\w. ode_flow f D (fstcart w) (sndcart w)) o
    (\w. pastecart (fstcart w) (pastecart t0 (sndcart w)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^(1,(N,N)finite_sum)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let P2AL_HASDER_CARTS = prove
 (`!(f:real^M->real^(N,P)finite_sum) f' net.
     (f has_derivative f') net
     ==> ((\x. fstcart(f x)) has_derivative (\h. fstcart(f' h))) net /\
         ((\x. sndcart(f x)) has_derivative (\h. sndcart(f' h))) net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM HAS_DERIVATIVE_PASTECART_EQ; PASTECART_FST_SND; ETA_AX] THEN
  ASM_REWRITE_TAC[]);;

let P2AL_HASVD_CARTS = prove
 (`!(f:real^1->real^(N,P)finite_sum) f' net.
     (f has_vector_derivative f') net
     ==> ((\x. fstcart(f x)) has_vector_derivative fstcart f') net /\
         ((\x. sndcart(f x)) has_vector_derivative sndcart f') net`,
  REWRITE_TAC[has_vector_derivative] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2AL_HASDER_CARTS) THEN
  REWRITE_TAC[FSTCART_CMUL; SNDCART_CMUL]);;

(* The Jacobi matrix Y = D_Z y and its velocity B = D_Z A of the window     *)
(* flow at Z0 (chart coordinates of the region chart of the window).        *)

let p2al_jy = new_definition
 `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
          (Z0:real^N) (s:real) =
    matrix(frechet_derivative (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) (at Z0))`;;

let p2al_jb = new_definition
 `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
          (Z0:real^N) (s:real) =
    matrix(frechet_derivative (\Z. sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) (at Z0))`;;

let P2AL_LFL_HASDER_Z = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s) has_derivative
          (\h. frechet_derivative
                 (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                        (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                         (IMAGE phi (U INTER W) PCROSS (:real^N)))
                        (fstcart w) (pastecart (lift s1) (sndcart w)))
                 (at (pastecart (lift s) (Phi Z0)))
                 (pastecart (vec 0) (frechet_derivative Phi (at Z0) h)))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (N:real^N->bool) /\ smooth_map_on N (Phi:real^N->real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` THEN
    REWRITE_TAC[p2al_lwa] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt`;
                 `interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                 `lift s1`] P2AL_FLW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2al_lfl] THEN
  MP_TAC(ISPECL
   [`\Z:real^N. pastecart (lift s) ((Phi:real^N->real^(N,N)finite_sum) Z)`;
    `\w:real^(1,(N,N)finite_sum)finite_sum.
       ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
         (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
         (fstcart w) (pastecart (lift s1) (sndcart w))`;
    `\h:real^N. pastecart (vec 0:real^1)
                  (frechet_derivative (Phi:real^N->real^(N,N)finite_sum) (at Z0) h)`;
    `frechet_derivative
       (\w:real^(1,(N,N)finite_sum)finite_sum.
          ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
            (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
            (fstcart w) (pastecart (lift s1) (sndcart w)))
       (at (pastecart (lift s) ((Phi:real^N->real^(N,N)finite_sum) Z0)))`;
    `Z0:real^N`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `{w | pastecart (fstcart w) (pastecart (lift s1) (sndcart w)) IN
           ode_domain (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
             (interval(lift(s1 - r),lift(s1 + r)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` THEN
    REWRITE_TAC[p2al_lin]]);;

(* Column j of the joint Jacobi matrix (Y,B): the derivative of the window  *)
(* flow from s1 in the direction D_Z Phi(Z0) e_j of the initial state.       *)

let p2al_jcol = new_definition
 `p2al_jcol (V:p2alv) tt s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
            (Z0:real^N) (j:num) (t:real) =
    frechet_derivative
      (\w. ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
             (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
             (fstcart w) (pastecart (lift s1) (sndcart w)))
      (at (pastecart (lift t) (Phi Z0)))
      (pastecart (vec 0) (frechet_derivative Phi (at Z0) (basis j)))`;;

let P2AL_JYB_COLUMNS = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> p2al_jy V tt s1 r W b' U phi Phi Z0 s =
         cmp_fmat (\j t. fstcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j t)) s /\
         p2al_jb V tt s1 r W b' U phi Phi Z0 s =
         cmp_fmat (\j t. sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j t)) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_HASDER_CARTS o MATCH_MP P2AL_LFL_HASDER_Z) THEN
  DISCH_THEN(CONJUNCTS_THEN
    (ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE)) THEN
  ASM_REWRITE_TAC[p2al_jy; p2al_jb; matrix; cmp_fmat; p2al_jcol]);;

let P2AL_JCOL_DERIV = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s j.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\v. p2al_jcol V tt s1 r W b' U phi Phi Z0 j (drop v)) has_vector_derivative
          pastecart (sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s))
            (frechet_derivative
               (\z. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s z
                      (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
               (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
               (fstcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s)) +
             frechet_derivative
               (\w. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
                      (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) w)
               (at (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
               (sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s)))) (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. frechet_derivative (p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt)
          (at (pastecart (lift s) (p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
          (pastecart (vec 0) c) =
        pastecart (sndcart c)
          (frechet_derivative
             (\z. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s z
                    (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
             (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) (fstcart c) +
           frechet_derivative
             (\w. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
                    (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) w)
             (at (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) (sndcart c))`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^(N,N)finite_sum` THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s1 - r`; `s1 + r`;
                   `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`; `s:real`;
                   `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                   `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                   `fstcart(c:real^(N,N)finite_sum)`; `sndcart(c:real^(N,N)finite_sum)`]
                  P2AL_LFIELD_DSTATE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` THEN
  REWRITE_TAC[p2al_lin; ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt`;
                 `interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                 `lift s1`; `(Phi:real^N->real^(N,N)finite_sum) Z0`;
                 `frechet_derivative (Phi:real^N->real^(N,N)finite_sum) (at Z0) (basis j)`]
                ODE_FLOW_VARIATIONAL_FIXED_TIME) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift s` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM p2al_lfl] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p2al_jcol; LIFT_DROP]);;

let P2AL_FMAT_LIN2 = prove
 (`!(Ly:real^N->real^N) (LA:real^N->real^N) (c:num->real->real^(N,N)finite_sum) t.
     linear Ly /\ linear LA
     ==> cmp_fmat (\j t. Ly(fstcart(c j t)) + LA(sndcart(c j t))) t =
         matrix Ly ** cmp_fmat (\j t. fstcart(c j t)) t +
         matrix LA ** cmp_fmat (\j t. sndcart(c j t)) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CMPF_FMAT_LMUL] THEN BETA_TAC THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; MATRIX_ADD_COMPONENT; VECTOR_ADD_COMPONENT]);;

let P2AL_LWIN_JACOBI = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\v. vectorize(p2al_jy V tt s1 r W b' U phi Phi Z0 (drop v))) has_vector_derivative
          vectorize(p2al_jb V tt s1 r W b' U phi Phi Z0 s)) (at (lift s)) /\
         ((\v. vectorize(p2al_jb V tt s1 r W b' U phi Phi Z0 (drop v))) has_vector_derivative
          vectorize(matrix(frechet_derivative
                     (\z. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s z
                            (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
                     (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))) **
                    p2al_jy V tt s1 r W b' U phi Phi Z0 s +
                    matrix(frechet_derivative
                     (\w. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
                            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) w)
                     (at (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))) **
                    p2al_jb V tt s1 r W b' U phi Phi Z0 s)) (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s1 - r`; `s1 + r`;
                 `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`; `s:real`;
                 `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                 `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                 `vec 0:real^N`; `vec 0:real^N`] P2AL_LFIELD_DSTATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE)
    (ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE o CONJUNCT1)) THEN
  SUBGOAL_THEN
   `!v. dist(v,lift s) < e
        ==> p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v) =
            cmp_fmat (\j t. fstcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j t)) (drop v) /\
            p2al_jb V tt s1 r W b' U phi Phi Z0 (drop v) =
            cmp_fmat (\j t. sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j t)) (drop v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; DIST_LIFT; LIFT_DROP] THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AL_JYB_COLUMNS THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `lift s`) THEN
  REWRITE_TAC[DIST_REFL; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `!j. ((\v. p2al_jcol (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 j (drop v))
         has_vector_derivative
         pastecart (sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s))
           (frechet_derivative
              (\z. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s z
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
              (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
              (fstcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s)) +
            frechet_derivative
              (\w. p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) w)
              (at (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
              (sndcart(p2al_jcol V tt s1 r W b' U phi Phi Z0 j s)))) (at (lift s))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AL_JCOL_DERIV THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `\v. vectorize(cmp_fmat (\j t. fstcart(p2al_jcol (V:p2alv) tt s1 r W b' U
                                                  (phi:A->real^N) Phi Z0 j t)) (drop v))`;
    EXISTS_TAC `\v. vectorize(cmp_fmat (\j t. sndcart(p2al_jcol (V:p2alv) tt s1 r W b' U
                                                  (phi:A->real^N) Phi Z0 j t)) (drop v))`] THEN
  EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[] THENL
   [MATCH_MP_TAC CMPF_HAS_VD_FMAT THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASVD_CARTS o SPEC `j:num`) THEN
    REWRITE_TAC[FSTCART_PASTECART];
    ASM_SIMP_TAC[GSYM P2AL_FMAT_LIN2] THEN
    MATCH_MP_TAC CMPF_HAS_VD_FMAT THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP P2AL_HASVD_CARTS o SPEC `j:num`) THEN
    REWRITE_TAC[SNDCART_PASTECART]]);;

(* ========================================================================= *)
(* Windows with representation.  p2al_wok: for every Z in N and every s >=   *)
(* s1 of the window where the flow is defined, the window flow is the chart  *)
(* state of the L-geodesic from x with initial vector Z. Regular windows     *)
(* (P2AL_LWIN_WOK) and the start window at s1 = 0 in the chart at x, with    *)
(* initial state (phi x, 2 Z) (P2AL_SWIN_WOK).                               *)
(* ========================================================================= *)

let p2al_wok = new_definition
 `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N
           (Phi:real^N->real^(N,N)finite_sum) <=>
    &0 <= s1 /\ p2al_lwa V tt s1 r W a' b' U phi N Phi /\
    (!Z s. Z IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\
           p2al_lin V tt s1 r W b' U phi Phi Z s
           ==> ?gamma. p2a_Lgeod_from V tt x Z (s pow 2) gamma /\
                       gamma(s pow 2) IN U INTER W /\
                       phi(gamma(s pow 2)) = fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s) /\
                       ((\v. phi(gamma(drop v pow 2))) has_vector_derivative
                        sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                         (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2}))`;;

let P2AL_LFL_BASE = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ p2al_lin V tt s1 r W b' U phi Phi Z s
     ==> p2al_lin V tt s1 r W b' U phi Phi Z s1 /\
         p2al_lfl V tt s1 r W b' U phi Phi Z s1 = Phi Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  UNDISCH_TAC `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s` THEN
  REWRITE_TAC[p2al_lin; p2al_lfl; ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt`;
                 `interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                 `pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z)`]
                ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN SIMP_TAC[]);;

let P2AL_LWIN_WOK = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi.
     p2al_lwin V tt x s1 r W a' b' U phi N Phi
     ==> p2al_wok V tt x s1 r W a' b' U phi N Phi`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2al_wok] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2al_lwin]) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s1 < s` THENL
   [MATCH_MP_TAC P2AL_LWIN_LGEOD THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = s1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s1:real`] P2AL_LFL_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

(* The start window: base s1 = 0, the chart at x of the slice at tt, the     *)
(* region at x ending at tt, and the initial state (phi x, 2 Z).  The proof  *)
(* of the representation follows the end of P2A_LPROP_START (pc_p2a_lgeo3).  *)

let P2AL_SWIN_WOK = prove
 (`!(V:p2alv) tt (x:A) W a U (phi:A->real^N).
     p2a_region V W a tt /\ x IN W /\ chart_at (p2a_vatlas V tt) x = (U,phi)
     ==> a < tt /\ x IN U /\
         p2al_wok V tt x (&0) (sqrt(tt - a)) W a tt U phi (:real^N)
           (\Z. pastecart (phi x) (&2 % Z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_region; p2a_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:p2alv) tt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:p2alv) tt /\ (x:A) IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:p2alv) tt`; `p2a_vatlas (V:p2alv) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a) /\ sqrt(tt - a) pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lwa (V:p2alv) tt (&0) (sqrt(tt - a)) W a tt U (phi:A->real^N) (:real^N)
      (\Z. pastecart (phi x) (&2 % Z))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2al_lwa; OPEN_UNIV; REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(tt - a) pow 2` MP_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
        REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN
  REWRITE_TAC[REAL_SUB_LZERO; REAL_ADD_LID] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2al_wok; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`] THEN
  REWRITE_TAC[IN_UNIV; p2al_lin; p2al_lfl; REAL_SUB_LZERO; REAL_ADD_LID; LIFT_NUM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt`;
                 `interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`; `lift s`;
                 `pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % (Z:real^N)))`]
                ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt`;
                 `interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                 `pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % (Z:real^N)))`]
                ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `W:A->bool`; `a:real`; `U:A->bool`;
    `phi:A->real^N`;
    `\t. fstcart(ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt)
                   (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                    (IMAGE phi (U INTER W) PCROSS (:real^N))) t
                   (pastecart (vec 0:real^1) (pastecart (phi x) (&2 % (Z:real^N)))))`;
    `\t. sndcart(ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt)
                   (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                    (IMAGE phi (U INTER W) PCROSS (:real^N))) t
                   (pastecart (vec 0:real^1) (pastecart (phi x) (&2 % (Z:real^N)))))`;
    `ode_maxint (p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt)
       (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
        (IMAGE phi (U INTER W) PCROSS (:real^N)))
       (pastecart (vec 0:real^1) (pastecart (phi x) (&2 % (Z:real^N))))`;
    `s:real`] P2A_LGEOD_FROM_SOL) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  EXISTS_TAC
   `\tau. chart_inv (U INTER W,phi:A->real^N)
            (fstcart(ode_flow (p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi)) tt)
                       (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                        (IMAGE phi (U INTER W) PCROSS (:real^N)))
                       (lift(sqrt tau))
                       (pastecart (vec 0:real^1) (pastecart (phi x) (&2 % (Z:real^N))))))` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* Lexp, the Jacobian J and the slices of a window at a fixed s.             *)
(* P2AL_WOK_LGEO: the chosen L-geodesic p2a_Lgeo up to s^2 is the window     *)
(* flow; P2AL_WOK_SLICE: the slice of the window domain at s is open and the *)
(* flow is smooth on it; P2AL_WOK_J: J(Z0,s^2) is |det Y(s)| sqrt(det G)     *)
(* divided by the reference density (P2A_J_REGION).                          *)
(* ========================================================================= *)

let P2AL_WOK_LGEO = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2a_svs V /\ p2al_wok V tt x s1 r W a' b' U phi N Phi /\
     Z IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z s
     ==> Z IN p2a_Ldom V tt x (s pow 2) /\
         p2a_Lexp V tt x (s pow 2) Z IN U INTER W /\
         phi(p2a_Lexp V tt x (s pow 2) Z) =
         fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s) /\
         ((\v. phi(p2a_Lgeo V tt x Z (s pow 2) (drop v pow 2))) has_vector_derivative
          sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
           (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi` THEN
  REWRITE_TAC[p2al_wok] THEN
  DISCH_THEN(MP_TAC o SPECL [`Z:real^N`; `s:real`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) (s pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`; `gamma:real->A`;
                 `p2a_Lgeo (V:p2alv) tt (x:A) Z (s pow 2)`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2a_Lexp (V:p2alv) tt (x:A) (s pow 2) Z = gamma(s pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[p2a_Lexp] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let P2AL_WOK_SLICE = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi
     ==> open {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s} /\
         smooth_map_on {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s}
           (\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\Z:real^N. pastecart (lift s) Z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} =
    {Z | Z IN (:real^N) /\
         (\Z:real^N. pastecart (lift s) Z) Z IN
         {z | sndcart z IN N /\
              p2al_lin V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_UNIV; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s) =
    (\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))) o
    (\Z:real^N. pastecart (lift s) Z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z | sndcart z IN N /\
                   p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart z)
                     (drop(fstcart z))}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let P2AL_WOK_J = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ p2al_wok V tt x s1 r W a' b' U phi N Phi /\
     Z0 IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> p2a_J V tt x (s pow 2) Z0 =
         abs(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s)) *
         sqrt(det(p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                    (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))) /
         p2a_zdens V tt x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o MATCH_MP P2AL_WOK_SLICE) THEN STRIP_TAC THEN
  UNDISCH_TAC `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` THEN
  REWRITE_TAC[p2al_lwa] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s pow 2`;
                 `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`;
                 `Z0:real^N`] P2A_J_REGION) THEN
  REWRITE_TAC[p2a_zdens; p2al_jy; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
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

(* ========================================================================= *)
(* The L-length F(s) = Ltil(Z,s^2) as an integral over [0,s] of the          *)
(* s-integrand of the L-geodesic up to b (P2AL_LTIL_INT), F' = the integrand *)
(* (P2AL_LTIL_DERIV), and the integrand in a window chart: the chart         *)
(* Lagrangian llag of the window flow (P2AL_WOK_LSINT).                      *)
(* ========================================================================= *)

let P2AL_LSINT_CONT = prove
 (`!(V:p2alv) tt (x:A) b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b
     ==> (p2a_lsint V tt (p2a_Lgeo V tt x Z b) b) real_continuous_on
         real_interval[&0,sqrt b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(Z':real^N) (t:real). p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z' b) b t`;
                 `&0`; `sqrt b`; `{Z:real^N}`] P2A_PARAM_REAL_INTEGRAL_CONTINUOUS) THEN
  REWRITE_TAC[COMPACT_SING; IN_SING] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0,lift(sqrt b)] PCROSS p2a_Ldom (V:p2alv) tt (x:A) b` THEN
    ASM_SIMP_TAC[P2A_LSINT_JOINT] THEN
    REWRITE_TAC[SUBSET_PCROSS; LIFT_NUM; SUBSET_REFL] THEN ASM SET_TAC[];
    DISCH_THEN(MP_TAC o SPEC `Z:real^N` o CONJUNCT1) THEN REWRITE_TAC[ETA_AX]]);;

let P2AL_LTIL_INT = prove
 (`!(V:p2alv) tt (x:A) b Z s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s /\ s pow 2 <= b
     ==> p2a_Ltil V tt x (s pow 2) Z =
         real_integral (real_interval[&0,s]) (p2a_lsint V tt (p2a_Lgeo V tt x Z b) b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `s pow 2`]
                P2A_LDOM_RESTRICT) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s pow 2`; `Z:real^N`] P2AL_LSINT_CONT) THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`] P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`] P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `p2a_Lgeo (V:p2alv) tt (x:A) Z (s pow 2)`; `s pow 2`]
                P2A_L_LENGTH_SFORM) THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2a_Ltil] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t /\ t pow 2 <= s pow 2 /\ t pow 2 <= b` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ y <= z ==> x <= y /\ x <= z`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `p2a_Lgeo (V:p2alv) tt (x:A) Z b`; `b:real`; `t:real`]
                P2A_LSINT_RESTRICT) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `p2a_Lgeo (V:p2alv) tt (x:A) Z (s pow 2)`; `s pow 2`;
                 `t:real`] P2A_LSINT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC P2A_LSINT_AGREE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2AL_LTIL_DERIV = prove
 (`!(V:p2alv) tt (x:A) b Z s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < s /\ s pow 2 < b
     ==> ((\s'. p2a_Ltil V tt x (s' pow 2) Z) has_real_derivative
          p2a_lsint V tt (p2a_Lgeo V tt x Z b) b s) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\u. real_integral (real_interval[&0,u])
           (p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b)`;
    `min s (sqrt b - s)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN BETA_TAC THEN
    MATCH_MP_TAC P2AL_LTIL_INT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b`; `&0`; `sqrt b`]
                REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_SIMP_TAC[P2AL_LSINT_CONT] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(INST [`p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b s`,`f':real`]
          (ISPECL [`\u. real_integral (real_interval[&0,u])
                          (p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b)`;
                   `real_interval[&0,sqrt b]`; `real_interval(&0,sqrt b)`; `s:real`]
                  HAS_REAL_DERIVATIVE_WITHIN_SUBSET)) THEN
  ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. real_integral (real_interval[&0,u])
                        (p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b)`;
                 `p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b s`;
                 `s:real`; `real_interval(&0,sqrt b)`] HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let P2AL_WOK_LSINT = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2a_svs V /\ p2al_wok V tt x s1 r W a' b' U phi N Phi /\
     Z IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
     Z IN p2a_Ldom V tt x b /\ s pow 2 <= b
     ==> p2a_lsint V tt (p2a_Lgeo V tt x Z b) b s =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
           (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_LGEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `s pow 2`]
                P2A_LDOM_RESTRICT) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `b:real`] P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`] P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `p2a_Lgeo (V:p2alv) tt (x:A) Z b`; `b:real`; `s:real`]
                P2A_LSINT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) (s pow 2) s =
    p2a_lsint V tt (p2a_Lgeo V tt x Z (s pow 2)) (s pow 2) s`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2A_LSINT_AGREE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p2a_Lexp]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "fstcart")) (rand(concl th)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2al_lwa] o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2al_wok]) THEN
  SUBGOAL_THEN `a' < tt - s pow 2 /\ tt - s pow 2 <= b'` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `b':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LSINT_CHART THEN EXISTS_TAC `a':real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]);;

(* ========================================================================= *)
(* The derivative of the reduced-volume integrand in s in a                  *)
(* window: with F(s) = Ltil(Z0,s^2) and Jc = |det Y| sqrt(det G),           *)
(*   rvi(s^2) = exp(-F(s)/(2s)) (Jc(s)/zdens) / s^n,                        *)
(* d/ds rvi(s^2) = rvi(s^2) gw(s) / s^2 with gw = s^2 sigma - H, sigma =    *)
(* tr(B Y^-1) + tr Gamma(A,.) (P2AL_WOK_RVI_DERIV).                         *)
(* ========================================================================= *)

let P2AL_POW_DERIV_ID = prove
 (`!n s. ~(s = &0) ==> &n * s pow (n - 1) = &n / s * s pow n`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; real_div] THEN
  REWRITE_TAC[SUC_SUB1; real_pow] THEN CONV_TAC REAL_FIELD);;

let P2AL_RVI_FORM_DERIV = prove
 (`!(Lf:real->real) Lf1 (Jc:real->real) Jc1 zd n s.
     &0 < s /\ ~(Jc s = &0) /\ ~(zd = &0) /\
     (Lf has_real_derivative Lf1) (atreal s) /\ (Jc has_real_derivative Jc1) (atreal s)
     ==> ((\x. exp(--(Lf x / (&2 * x))) * Jc x / zd / x pow n) has_real_derivative
          (exp(--(Lf s / (&2 * s))) * Jc s / zd / s pow n) *
          (--(Lf1 / (&2 * s)) + Lf s / (&2 * s pow 2) + Jc1 / Jc s - &n / s)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\x. --(Lf x / (&2 * x))) has_real_derivative
                 --((Lf1 * (&2 * s) - Lf s * &2) / (&2 * s) pow 2)) (atreal s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    MP_TAC(ISPECL [`Lf:real->real`; `Lf1:real`; `\x:real. &2 * x`; `&2`; `s:real`]
                  HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `&2`; `s:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. exp(--(Lf x / (&2 * x)))) has_real_derivative
     --((Lf1 * (&2 * s) - Lf s * &2) / (&2 * s) pow 2) * exp(--(Lf s / (&2 * s)))) (atreal s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2(BETA_RULE(REWRITE_RULE[HAS_REAL_DERIVATIVE_EXP]
      (INST [`exp`,`g':real->real`]
        (ISPECL [`\x. --((Lf:real->real) x / (&2 * x))`; `exp`]
                HAS_REAL_DERIVATIVE_CHAIN_UNIV))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Jc:real->real`; `Jc1:real`; `\x:real. zd:real`; `&0`; `s:real`]
                HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. (Jc:real->real) x / zd`;
                 `((Jc1:real) * zd - (Jc:real->real) s * &0) / zd pow 2`;
                 `\x:real. x pow n`; `&n * s pow (n - 1) * &1`; `s:real`]
                HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. x`; `&1`; `s:real`; `n:num`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`\x. exp(--((Lf:real->real) x / (&2 * x)))`;
                 `--((Lf1 * (&2 * s) - Lf s * &2) / (&2 * s) pow 2) * exp(--(Lf s / (&2 * s)))`;
                 `\x. (Jc:real->real) x / zd / x pow n`;
                 `(((Jc1:real) * zd - (Jc:real->real) s * &0) / zd pow 2 * s pow n -
                   Jc s / zd * (&n * s pow (n - 1) * &1)) / (s pow n) pow 2`;
                 `s:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_RID] THEN ASM_SIMP_TAC[P2AL_POW_DERIV_ID; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `~(s pow n = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `~((Jc:real->real) s = &0)` THEN
  UNDISCH_TAC `~(zd = &0)` THEN
  SPEC_TAC(`exp(--((Lf:real->real) s / (&2 * s)))`,`ee:real`) THEN
  SPEC_TAC(`s pow n`,`p:real`) THEN CONV_TAC REAL_FIELD);;

let P2AL_ZDENS_POS = prove
 (`!(V:p2alv) tt (x:A). p2a_svs V /\ x IN topspace(p2a_vtop V tt) ==> &0 < p2a_zdens V tt x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tt:real` o GEN_REWRITE_RULE I [p2a_svs]) THEN
  SUBGOAL_THEN `~(topspace(p2a_vtop (V:p2alv) tt) = {})` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:p2alv) tt`; `p2a_vatlas (V:p2alv) tt`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_zdens] THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let P2AL_WOK_FACTS = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> lricci_flow (IMAGE phi (U INTER W)) a' b' (p2a_rlocal V W b' (U INTER W,phi)) /\
         p2a_lsmooth (IMAGE phi (U INTER W)) (s1 - r) (s1 + r)
           (\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) /\
         s1 - r < s /\ &0 < s /\ a' < tt - s pow 2 /\ tt - s pow 2 < b' /\
         fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) IN IMAGE phi (U INTER W) /\
         ((\v. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) has_vector_derivative
          sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) (at (lift s)) /\
         ((\v. sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) has_vector_derivative
          p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt s
            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
            (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) (at (lift s)) /\
         (?e. &0 < e /\
              !s'. abs(s' - s) < e
                   ==> s1 < s' /\ s' < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  UNDISCH_TAC `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` THEN
  REWRITE_TAC[p2al_lwa] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`]
                P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < s /\ s1 pow 2 < s pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `a':real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `a':real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASVD_CARTS) THEN
    REWRITE_TAC[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART];
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP P2AL_HASVD_CARTS) THEN
    REWRITE_TAC[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    EXISTS_TAC `min e (min (s - s1) (s1 + r - s))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The comparison function of a window: gw = s^2 sigma - H with sigma =     *)
(* tr(B Y^-1) + tr Gamma(A,.) and H = n s - s^3 R + s |A|^2/4 - F/2.         *)

let p2al_gw = new_definition
 `p2al_gw (V:p2alv) tt (x:A) s1 r W b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum)
          (Z0:real^N) (s:real) =
    s pow 2 * (trace(p2al_jb V tt s1 r W b' U phi Phi Z0 s **
                     matrix_inv(p2al_jy V tt s1 r W b' U phi Phi Z0 s)) +
               p2al_tg (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                       (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) -
    (&(dimindex(:N)) * s -
     s pow 3 * lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) +
     s * (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) dot
          (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
          sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) / &4 -
     p2a_Ltil V tt x (s pow 2) Z0 / &2)`;;

let P2AL_WOK_RVI_DERIV = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> ((\s'. p2a_rvi V tt x (s' pow 2) Z0) has_real_derivative
          p2a_rvi V tt x (s pow 2) Z0 * p2al_gw V tt x s1 r W b' U phi Phi Z0 s / s pow 2)
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LWIN_JACOBI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the derivative of F(s) = Ltil(Z0,s^2) *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `s:real`]
                P2AL_LTIL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_LSINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  (* the derivative of Jc = |det Y| sqrt(det G) *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b':real`;
                 `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`; `s:real`;
                 `\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
                 `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                 `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0`;
                 `p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s`] P2AL_JC_DERIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* positivity *)
  SUBGOAL_THEN `&0 < det(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                          (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC) THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`] P2AL_ZDENS_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s'. p2a_Ltil (V:p2alv) tt (x:A) (s' pow 2) Z0`;
    `p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt s
       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
       (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))`;
    `\s'. abs(det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s')) *
          sqrt(det(p2a_rlocal V W b' (U INTER W,phi) (tt - s' pow 2)
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s'))))`;
    `(abs(det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)) *
      sqrt(det(p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                 (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))) *
     ((trace(p2al_jb V tt s1 r W b' U phi Phi Z0 s **
             matrix_inv(p2al_jy V tt s1 r W b' U phi Phi Z0 s)) +
       p2al_tg (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
               (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
               (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) +
      &2 * s * lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`;
    `p2a_zdens (V:p2alv) tt (x:A)`; `dimindex(:N)`; `s:real`] P2AL_RVI_FORM_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO; DE_MORGAN_THM] THEN
    ASM_SIMP_TAC[SQRT_EQ_0; REAL_LT_IMP_NZ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\x'. exp(--(p2a_Ltil (V:p2alv) tt (x:A) (x' pow 2) Z0 / (&2 * x'))) *
                   (abs(det(p2al_jy V tt s1 r W b' U (phi:A->real^N) Phi Z0 x')) *
                    sqrt(det(p2a_rlocal V W b' (U INTER W,phi) (tt - x' pow 2)
                               (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 x'))))) /
                   p2a_zdens V tt x / x' pow dimindex(:N)` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s'` ASSUME_TAC THENL
     [MP_TAC(ASSUME `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi`) THEN
      REWRITE_TAC[p2al_wok] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    BETA_TAC THEN REWRITE_TAC[p2a_rvi; p2a_ltil] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s':real`] P2AL_WOK_J) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "exp")) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p2a_rvi; p2a_ltil; p2al_gw; p2a_llag] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_J) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `jy = abs(det(p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s))` THEN
  ABBREV_TAC `sg = sqrt(det(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))` THEN
  SUBGOAL_THEN `~(jy = &0) /\ ~(sg = &0)` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["jy"; "sg"] THEN
    ASM_SIMP_TAC[REAL_ABS_ZERO; SQRT_EQ_0; REAL_LT_IMP_NZ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < p2a_zdens (V:p2alv) tt (x:A)` THEN
  SPEC_TAC(`exp(--(p2a_Ltil (V:p2alv) tt (x:A) (s pow 2) Z0 / (&2 * s)))`,`ee:real`) THEN
  SPEC_TAC(`s pow dimindex(:N)`,`p:real`) THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The first variation of the L-length in a window, part 1. The derivative   *)
(* of the chart Lagrangian in (y,A) (P2AL_QF_HASDER), its derivative along   *)
(* the window flow in the initial vector (P2AL_LLAG_FLOW_ZDERIV), and the    *)
(* integrated Euler-Lagrange identity with boundary terms                    *)
(* (P2AL_WEAK_EL_BDRY, the boundary version of P2A_WEAK_EL).                 *)
(* ========================================================================= *)

let P2AL_QF_HASDER = prove
 (`!U (G:real^N->real^N^N) y A c.
     metric_field U G /\ y IN U
     ==> ((\w. lift(inv(&2) * (sndcart w dot (G(fstcart w) ** sndcart w)) +
                    c * lscalar G (fstcart w))) has_derivative
          (\d. lift(inv(&2) * (A dot (mderiv G y (fstcart d) ** A)) +
                    c * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) (fstcart d)) +
                    sndcart d dot (G y ** A)))) (at (pastecart y A))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable at y /\
                (\z. lift(lscalar (G:real^N->real^N^N) z)) differentiable at y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(N,N)finite_sum. (G:real^N->real^N^N)(fstcart z)`;
                 `\d:real^(N,N)finite_sum.
                    frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                       (at y) (fstcart d)`;
                 `sndcart:real^(N,N)finite_sum->real^N`; `sndcart:real^(N,N)finite_sum->real^N`;
                 `sndcart:real^(N,N)finite_sum->real^N`; `sndcart:real^(N,N)finite_sum->real^N`;
                 `pastecart (y:real^N) (A:real^N)`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
                             REWRITE_TAC[LINEAR_SNDCART] THEN NO_TAC) THEN
    MP_TAC(ISPECL [`(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N)) (at y)`;
                   `pastecart (y:real^N) (A:real^N)`] GRGE_HAS_DERIVATIVE_FSTCART_COMPOSE) THEN
    REWRITE_TAC[FSTCART_PASTECART; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. lift(lscalar (G:real^N->real^N^N) z)`;
                 `frechet_derivative (\z:real^N. lift(lscalar (G:real^N->real^N^N) z)) (at y)`;
                 `pastecart (y:real^N) (A:real^N)`] GRGE_HAS_DERIVATIVE_FSTCART_COMPOSE) THEN
  REWRITE_TAC[FSTCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(inv(&2) * (sndcart w dot ((G:real^N->real^N^N)(fstcart w) ** sndcart w)) +
              c * lscalar G (fstcart w))) =
    (\w. inv(&2) % lift(sndcart w dot (G(fstcart w) ** sndcart w)) +
         c % lift(lscalar G (fstcart w)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\d. lift(inv(&2) * (A dot (mderiv (G:real^N->real^N^N) y (fstcart d) ** A)) +
              c * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) (fstcart d)) +
              sndcart d dot (G y ** A))) =
    (\d:real^(N,N)finite_sum.
       inv(&2) % lift(sndcart d dot (G y ** A) +
                      A dot (matrify(frechet_derivative
                               ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                               (at y) (fstcart d)) ** A + G y ** sndcart d)) +
       c % frechet_derivative (\z. lift(lscalar G z)) (at y) (fstcart d))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `d:real^(N,N)finite_sum` THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`;
                   `sndcart(d:real^(N,N)finite_sum)`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[mderiv; DOT_RADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[ETA_AX]);;

let P2AL_HASDER_MATRIX = prove
 (`!(f:real^M->real^N) f' x.
     (f has_derivative f') (at x)
     ==> (f has_derivative (\c. matrix(frechet_derivative f (at x)) ** c)) (at x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_REWRITE_TAC[ETA_AX]);;

let P2AL_LFL_HASDER_YB = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s) has_derivative
          (\c. pastecart (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c)
                         (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c))) (at Z0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_HASDER_CARTS o MATCH_MP P2AL_LFL_HASDER_Z) THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP P2AL_HASDER_MATRIX o BETA_RULE)) THEN
  REWRITE_TAC[GSYM p2al_jy; GSYM p2al_jb] THEN
  REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`
    PASTECART_FST_SND)] THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV) [GSYM PASTECART_FST_SND] THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART]);;

let P2AL_LLAG_FLOW_ZDERIV = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\Z. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s
                      (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                      (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))) has_derivative
          (\c. lift(inv(&2) *
                    (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) dot
                     (mderiv (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                             (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                             (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) **
                      sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) +
                    &2 * s pow 2 *
                    drop(frechet_derivative
                           (\z. lift(lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) z))
                           (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
                           (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c)) +
                    (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c) dot
                    (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                     sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^N) (U INTER W))
      (p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
                   (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))` THEN
    REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "metric_field")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`;
                 `\w:real^(N,N)finite_sum.
                    lift(inv(&2) * (sndcart w dot
                         (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                            (fstcart w) ** sndcart w)) +
                         (&2 * s pow 2) *
                         lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) (fstcart w))`;
                 `\c. pastecart (p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s ** c)
                                (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c)`;
                 `\d:real^(N,N)finite_sum.
                    lift(inv(&2) *
                         (sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s) dot
                          (mderiv (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                                  (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                                  (fstcart d) **
                           sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) +
                         (&2 * s pow 2) *
                         drop(frechet_derivative
                                (\z. lift(lscalar (p2a_rlocal V W b' (U INTER W,phi)
                                                     (tt - s pow 2)) z))
                                (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
                                (fstcart d)) +
                         sndcart d dot
                         (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                          sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`;
                 `Z0:real^N`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; p2a_llag; REAL_MUL_ASSOC] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2AL_LFL_HASDER_YB THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`;
                 `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)`;
                 `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                 `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                 `&2 * s pow 2`] P2AL_QF_HASDER) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; REAL_MUL_ASSOC]);;

(* The derivative of eta . (G A) along a solution of (6.5): the integrand of *)
(* the first variation (inner step of P2A_WEAK_EL of pc_p2a_bvp).            *)

let P2AL_EL_ETA_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A (eta:real^1->real^N) eta1 s.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)) /\
     (eta has_vector_derivative eta1) (at (lift s))
     ==> ((\s. eta(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))
          has_real_derivative
          (inv(&2) * (A(lift s) dot
                      (mderiv (Gt(tt - s pow 2)) (y(lift s)) (eta(lift s)) ** A(lift s))) +
           &2 * s pow 2 *
           drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                   (at (y(lift s))) (eta(lift s))) +
           eta1 dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `s:real`] P2A_EL_VECTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`; `eta:real^1->real^N`;
                 `\v. (Gt:real->real^N->real^N^N)(tt - drop v pow 2) ((y:real^1->real^N) v) **
                      (A:real^1->real^N) v`;
                 `eta1:real^N`;
                 `((lambda k. inv(&2) * ((A:real^1->real^N)(lift s) dot
                                  (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                          ((y:real^1->real^N)(lift s)) (basis k) **
                                   A(lift s))) +
                      &2 * s pow 2 *
                      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                              (at (y(lift s))) (basis k))):real^N)`;
                 `lift s`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT; LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`;
                 `(y:real^1->real^N)(lift s)`; `(A:real^1->real^N)(lift s)`; `s pow 2`]
                P2A_LLAG_DY_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. lift(inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                               w ** A(lift s))) +
                      &2 * s pow 2 *
                      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                              (at (y(lift s))) w))`;
                 `(eta:real^1->real^N)(lift s)`] P2A_DOT_LAMBDA_LINEAR) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P2AL_WEAK_EL_BDRY = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A (eta:real^1->real^N)
    eta' s1 s2.
     lricci_flow U ta tb Gt /\ s1 <= s2 /\
     (!s. s1 < s /\ s < s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              (eta has_vector_derivative eta'(lift s)) (at (lift s))) /\
     (\s. eta(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))
       real_continuous_on real_interval[s1,s2]
     ==> ((\s. inv(&2) * (A(lift s) dot
                          (mderiv (Gt(tt - s pow 2)) (y(lift s)) (eta(lift s)) ** A(lift s))) +
               &2 * s pow 2 *
               drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                       (at (y(lift s))) (eta(lift s))) +
               eta'(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))
          has_real_integral
          (eta(lift s2) dot (Gt(tt - s2 pow 2) (y(lift s2)) ** A(lift s2)) -
           eta(lift s1) dot (Gt(tt - s1 pow 2) (y(lift s1)) ** A(lift s1))))
         (real_interval[s1,s2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s. (eta:real^1->real^N)(lift s) dot
         ((Gt:real->real^N->real^N^N)(tt - s pow 2) ((y:real^1->real^N)(lift s)) **
          (A:real^1->real^N)(lift s))`;
    `\s. inv(&2) * ((A:real^1->real^N)(lift s) dot
                    (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                            ((eta:real^1->real^N)(lift s)) ** A(lift s))) +
         &2 * s pow 2 *
         drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                 (at (y(lift s))) (eta(lift s))) +
         (eta':real^1->real^N)(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s))`;
    `s1:real`; `s2:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AL_EL_ETA_DERIV THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The first variation of the L-length in a window, part 2:                  *)
(* differentiation under the integral sign (NSPA_SMOOTH_HAS_DERIVATIVE_PARAM *)
(* of the vendored NS parameter integrals) and the integrated Euler-        *)
(* Lagrange identity give, on [sa,sb] inside a window,                      *)
(*   D_Z int_sa^sb llag(s, y(s,Z), A(s,Z)) ds = [ (Y c) . (G A) ]_sa^sb     *)
(* (P2AL_FV_INT).                                                            *)
(* ========================================================================= *)

(* The window integrand as a function of (Z,t), parameter first.            *)

let P2AL_FV_K_SMOOTH = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi.
     p2al_lwa V tt s1 r W a' b' U phi N Phi
     ==> open {w:real^(N,1)finite_sum |
               fstcart w IN N /\
               p2al_lin V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))} /\
         smooth_map_on
           {w:real^(N,1)finite_sum |
            fstcart w IN N /\
            p2al_lin V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))}
           (\w. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop(sndcart w))
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
                       (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w)
                                  (drop(sndcart w))))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  SUBGOAL_THEN `linear (\w:real^(N,1)finite_sum. pastecart (sndcart w) (fstcart w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w:real^(N,1)finite_sum |
     fstcart w IN N /\
     p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w) (drop(sndcart w))} =
    {w | (\w. pastecart (sndcart w) (fstcart w)) w IN
         {z | sndcart z IN N /\
              p2al_lin V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))) =
    (\z. lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop(fstcart z))
                (fstcart(sndcart z)) (sndcart(sndcart z)))) o
    (\w. pastecart (sndcart w)
           ((\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z)))
            ((\w. pastecart (sndcart w) (fstcart w)) w)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(s1 - r),lift(s1 + r)) PCROSS
              (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `w:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`fstcart(w:real^(N,1)finite_sum)`;
                                  `drop(sndcart(w:real^(N,1)finite_sum))`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_domain" ||
                                 is_var t && fst(dest_var t) = "Z")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; P2AL_IN_PCROSS_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN
   `(\w:real^(N,1)finite_sum.
       p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w) (drop(sndcart w))) =
    (\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))) o
    (\w. pastecart (sndcart w) (fstcart w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:real^(1,N)finite_sum | sndcart z IN N /\
                p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart z)
                  (drop(fstcart z))}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[]]);;

let P2AL_FV_PARTIAL = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 t h.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 (drop t)
     ==> frechet_derivative
           (\w:real^(N,1)finite_sum.
              lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop(sndcart w))
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))))
           (at (pastecart Z0 t)) (pastecart h (vec 0)) =
         lift(inv(&2) *
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t)) dot
               (mderiv (p2a_rlocal V W b' (U INTER W,phi) (tt - drop t pow 2))
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t)))
                       (p2al_jy V tt s1 r W b' U phi Phi Z0 (drop t) ** h) **
                sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t)))) +
              &2 * drop t pow 2 *
              drop(frechet_derivative
                     (\z. lift(lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - drop t pow 2)) z))
                     (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t))))
                     (p2al_jy V tt s1 r W b' U phi Phi Z0 (drop t) ** h)) +
              (p2al_jb V tt s1 r W b' U phi Phi Z0 (drop t) ** h) dot
              (p2a_rlocal V W b' (U INTER W,phi) (tt - drop t pow 2)
                 (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t))) **
               sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_FV_K_SMOOTH) THEN
  SUBGOAL_THEN `(\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))) differentiable (at (pastecart (Z0:real^N) (t:real^1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{w:real^(N,1)finite_sum |
                 fstcart w IN N /\
                 p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w)
                   (drop(sndcart w))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\Z:real^N. pastecart Z (t:real^1)`; `\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))`;
                 `\h:real^N. pastecart h (vec 0:real^1)`;
                 `frechet_derivative (\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))) (at (pastecart (Z0:real^N) (t:real^1)))`;
                 `Z0:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; o_DEF] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `drop t`]
                P2AL_LLAG_FLOW_ZDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o CONJ (ASSUME
    `((\x:real^N. lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop t)
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi x (drop t)))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi x (drop t))))) has_derivative
      (\x. frechet_derivative (\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))) (at (pastecart Z0 t)) (pastecart x (vec 0)))) (at Z0)`)) THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN REWRITE_TAC[]);;

(* Continuity of the metric along the window flow, and the integrated       *)
(* derivative integrand: the first variation on [sa,sb] (P2AL_FV_DINT).      *)

let P2AL_WIN_GCONT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> (\v. vectorize(p2a_rlocal V W b' (U INTER W,phi) (tt - drop v pow 2)
                          (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v)))))
         continuous (at (lift s)) /\
         (\v. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) continuous (at (lift s)) /\
         (\v. sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_HASVD_CARTS) THEN
  SUBGOAL_THEN
   `(\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v)))
      continuous (at (lift s)) /\
    (\v. sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))) continuous (at (lift s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL_HVD_CONT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
                 (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))` THEN
  REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. vectorize(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - drop v pow 2)
                     (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))))) =
    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (p2a_rlocal V W b' (U INTER W,phi) (tt - drop(fstcart z) pow 2) (sndcart z))) o
    (\v. pastecart v (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop v))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_PASTECART THEN ASM_REWRITE_TAC[CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(interval(lift(s1 - r),lift(s1 + r)) PCROSS
                     IMAGE (phi:A->real^N) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AL_FV_DINT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 sa sb h.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\ sa <= sb /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt s1 r W b' U phi Phi Z0 s) /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b')
     ==> ((\s. inv(&2) *
               (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) dot
                (mderiv (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                        (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                        (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** h) **
                 sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))) +
               &2 * s pow 2 *
               drop(frechet_derivative
                      (\z. lift(lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) z))
                      (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
                      (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** h)) +
               (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** h) dot
               (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                  (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
          has_real_integral
          ((p2al_jy V tt s1 r W b' U phi Phi Z0 sb ** h) dot
           (p2a_rlocal V W b' (U INTER W,phi) (tt - sb pow 2)
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) **
            sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) -
           (p2al_jy V tt s1 r W b' U phi Phi Z0 sa ** h) dot
           (p2a_rlocal V W b' (U INTER W,phi) (tt - sa pow 2)
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)) **
            sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa))))
         (real_interval[sa,sb])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `lricci_flow (IMAGE (phi:A->real^N) (U INTER W)) a' b'
      (p2a_rlocal (V:p2alv) W b' (U INTER W,phi))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` THEN
    REWRITE_TAC[p2al_lwa] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`] P2A_REGION_LRICCI) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (phi:A->real^N) (U INTER W)`; `a':real`; `b':real`;
    `p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
    `\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
    `\v. sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
    `\v. p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v) ** h`;
    `\v. p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v) ** h`;
    `sa:real`; `sb:real`] P2AL_WEAK_EL_BDRY) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z0:real^N`; `s:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_HASVD_CARTS) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]) THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LWIN_JACOBI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^N` o MATCH_MP CMPF_HAS_VD_MATVEC o CONJUNCT1) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. (p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop x) ** h)
                   dot (p2a_rlocal V W b' (U INTER W,phi) (tt - drop x pow 2)
                          (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop x))) **
                        sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 (drop x)))`;
                 `sa:real`; `sb:real`] P2A_REAL_CONT_OF_VEC) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop x)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `drop x`] P2AL_WIN_GCONT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `drop x`]
                  P2AL_LWIN_JACOBI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^N` o MATCH_MP CMPF_HAS_VD_MATVEC o CONJUNCT1) THEN
    REWRITE_TAC[LIFT_DROP] THEN MESON_TAC[P2AL_HVD_CONT];
    MATCH_MP_TAC CONTINUOUS_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[o_DEF]]);;

let P2AL_FV_INT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 sa sb.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\ sa <= sb /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt s1 r W b' U phi Phi Z0 s) /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b')
     ==> ?d. &0 < d /\
             (!Z s. Z IN ball(Z0,d) /\ sa <= s /\ s <= sb
                    ==> Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s) /\
             ((\Z. lift(real_integral (real_interval[sa,sb])
                     (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s
                            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                            (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))))) has_derivative
              (\h. lift((p2al_jy V tt s1 r W b' U phi Phi Z0 sb ** h) dot
                        (p2a_rlocal V W b' (U INTER W,phi) (tt - sb pow 2)
                           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) **
                         sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) -
                        (p2al_jy V tt s1 r W b' U phi Phi Z0 sa ** h) dot
                        (p2a_rlocal V W b' (U INTER W,phi) (tt - sa pow 2)
                           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)) **
                         sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa))))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_FV_K_SMOOTH) THEN
  MP_TAC(ISPECL
   [`{w:real^(N,1)finite_sum |
      fstcart w IN N /\
      p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w) (drop(sndcart w))}`;
    `Z0:real^N`; `interval[lift sa,lift sb]`] NSPA_TUBE) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`Z:real^N`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `lift s`]) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ball(Z0:real^N,d)`;
    `{w:real^(N,1)finite_sum |
      fstcart w IN N /\
      p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w) (drop(sndcart w))}`;
    `lift sa`; `lift sb`;
    `\w:real^(N,1)finite_sum.
       lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt (drop(sndcart w))
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
              (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))`;
    `Z0:real^N`] NSPA_SMOOTH_HAS_DERIVATIVE_PARAM) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:real^N`; `t:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `t:real^1`]) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL; IN_ELIM_THM;
                 FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  (* the derivative map *)
  SUBGOAL_THEN
   `!h. integral (interval[lift sa,lift sb])
          (\t. frechet_derivative
                 (\w:real^(N,1)finite_sum.
                    lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt
                           (drop(sndcart w))
                           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w)
                                      (drop(sndcart w))))
                           (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w)
                                      (drop(sndcart w))))))
                 (at (pastecart Z0 t)) (pastecart h (vec 0))) =
        lift((p2al_jy V tt s1 r W b' U phi Phi Z0 sb ** h) dot
             (p2a_rlocal V W b' (U INTER W,phi) (tt - sb pow 2)
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) **
              sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) -
             (p2al_jy V tt s1 r W b' U phi Phi Z0 sa ** h) dot
             (p2a_rlocal V W b' (U INTER W,phi) (tt - sa pow 2)
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)) **
              sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `h:real^N` THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `sa:real`; `sb:real`;
                   `h:real^N`] P2AL_FV_DINT) THEN
    ASM_REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `t:real^1`; `h:real^N`]
                  P2AL_FV_PARTIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\w:real^N. integral (interval[lift sa,lift sb])
                 (\t. lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt
                             (drop t)
                             (fstcart(p2al_lfl V tt s1 r W b' U phi Phi w (drop t)))
                             (sndcart(p2al_lfl V tt s1 r W b' U phi Phi w (drop t)))))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN ball(Z0,d)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt s
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
           (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))
      real_integrable_on real_interval[sa,sb]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`\x:real^1. p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt
                     (drop x) (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z (drop x)))
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z (drop x)))`;
                   `sa:real`; `sb:real`] P2A_REAL_CONT_OF_VEC) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(\x:real^1. lift(p2a_llag (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt
                     (drop x) (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z (drop x)))
                     (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z (drop x))))) =
      (\w:real^(N,1)finite_sum.
         lift(p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt (drop(sndcart w))
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w))))
                (sndcart(p2al_lfl V tt s1 r W b' U phi Phi (fstcart w) (drop(sndcart w)))))) o
      (\x. pastecart Z x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{w:real^(N,1)finite_sum |
                 fstcart w IN N /\
                 p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (fstcart w)
                   (drop(sndcart w))}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `t:real^1`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL; IN_ELIM_THM; FSTCART_PASTECART;
                 SNDCART_PASTECART];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

(* ========================================================================= *)
(* Chart invariance of (Y c) . (G A) between two windows valid at the same s *)
(* (P2AL_MY_INV): Y and A transform with the derivative of the chart         *)
(* transition, G by its pullback (P2A_RLOCAL_TRANS).                         *)
(* ========================================================================= *)

let P2AL_TRANS_POINT = prove
 (`!(V:p2alv) W1 a1 b1 U1 (phi1:A->real^N) W2 U2 phi2 q.
     p2a_region V W1 a1 b1 /\ (U1,phi1) IN p2a_vatlas V b1 /\
     q IN U1 INTER W1 /\ q IN U2 INTER W2
     ==> chart_trans (U1 INTER W1,phi1) (U2 INTER W2,phi2) (phi1 q) = phi2 q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `a1 < b1` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_region; p2a_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `W1:A->bool`; `a1:real`; `b1:real`; `b1:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:p2alv) b1`; `p2a_vatlas (V:p2alv) b1`; `U1:A->bool`;
                 `phi1:A->real^N`; `W1:A->bool`; `q:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_SIMP_TAC[]);;

let P2AL_MY_ALG = prove
 (`!(G2:real^N^N) (M:real^N^N) (a1:real^N) (v1:real^N).
     v1 dot ((transp M ** G2 ** M) ** a1) = (M ** v1) dot (G2 ** (M ** a1))`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

(* Two windows valid at (Z,s) see the same point: their chart positions    *)
(* are related by the chart transition.                                     *)

let P2AL_WIN_TRANS_REP = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi s2 r2 W2 a2 b2 U2 phi2 N2 Phi2
    Z s.
     p2a_svs V /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 <= s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z s /\
     p2al_wok V tt x s2 r2 W2 a2 b2 U2 phi2 N2 Phi2 /\ Z IN N2 /\ s2 <= s /\ s < s2 + r2 /\
     p2al_lin V tt s2 r2 W2 b2 U2 phi2 Phi2 Z s /\ &0 < s
     ==> fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s) IN
         IMAGE phi ((U INTER W) INTER (U2 INTER W2)) /\
         chart_trans (U INTER W,phi) (U2 INTER W2,phi2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) =
         fstcart(p2al_lfl V tt s2 r2 W2 b2 U2 phi2 Phi2 Z s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (V:p2alv) W a' b' /\ (U:A->bool,phi:A->real^N) IN p2a_vatlas V b'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok; p2al_lwa]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_LGEO) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s2:real`; `r2:real`; `W2:A->bool`; `a2:real`;
                 `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                 `Phi2:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_WOK_LGEO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `p2a_Lexp (V:p2alv) tt (x:A) (s pow 2) Z` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) =
      `fstcart(p2al_lfl (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z s)`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) =
      `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)`)) THEN
    MATCH_MP_TAC P2AL_TRANS_POINT THEN
    MAP_EVERY EXISTS_TAC [`V:p2alv`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[]]);;

let P2AL_MY_INV = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi s2 r2 W2 a2 b2 U2 phi2 N2 Phi2
    Z0 s c.
     p2a_svs V /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     p2al_wok V tt x s2 r2 W2 a2 b2 U2 phi2 N2 Phi2 /\ Z0 IN N2 /\ s2 < s /\ s < s2 + r2 /\
     p2al_lin V tt s2 r2 W2 b2 U2 phi2 Phi2 Z0 s
     ==> (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) dot
         (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
            (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
          sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) =
         (p2al_jy V tt s2 r2 W2 b2 U2 phi2 Phi2 Z0 s ** c) dot
         (p2a_rlocal V W2 b2 (U2 INTER W2,phi2) (tt - s pow 2)
            (fstcart(p2al_lfl V tt s2 r2 W2 b2 U2 phi2 Phi2 Z0 s)) **
          sndcart(p2al_lfl V tt s2 r2 W2 b2 U2 phi2 Phi2 Z0 s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF1") (CONJUNCTS_THEN2 (LABEL_TAC "LS1") MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "Y1") (CONJUNCTS_THEN2 (LABEL_TAC "A1")
     (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1")))))))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s2:real`; `r2:real`; `W2:A->bool`; `a2:real`;
                 `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                 `Phi2:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF2") (CONJUNCTS_THEN2 (LABEL_TAC "LS2") MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "Y2") (CONJUNCTS_THEN2 (LABEL_TAC "A2")
     (X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E2")))))))))) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi /\
                p2al_lwa V tt s2 r2 W2 a2 b2 U2 (phi2:A->real^N) N2 Phi2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:p2alv) W a' b' /\ (U:A->bool,phi:A->real^N) IN p2a_vatlas V b' /\
                p2a_region V W2 a2 b2 /\ (U2:A->bool,phi2:A->real^N) IN p2a_vatlas V b2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  (* the chart transition *)
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) (U2 INTER W2,phi2)` THEN
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `W2:A->bool`; `a2:real`;
                 `b2:real`; `tt - s pow 2`; `U:A->bool`; `phi:A->real^N`; `U2:A->bool`;
                 `phi2:A->real^N`] P2A_REGION_CHART_DIFFEO) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; diffeomorphism_on] THEN STRIP_TAC THEN
  (* the velocity transforms with Dh *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s2:real`; `r2:real`; `W2:A->bool`;
                 `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                 `Phi2:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                P2AL_WIN_TRANS_REP) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((h:real^N->real^N) has_derivative frechet_derivative h
       (at (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s))))
      (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) ((U INTER W) INTER (U2 INTER W2))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (h:real^N->real^N)
                    (at (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)))` THEN
  SUBGOAL_THEN `linear(D:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sndcart(p2al_lfl (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z0 s) =
    (D:real^N->real^N) (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\v. fstcart(p2al_lfl (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z0
                              (drop v))` THEN
    EXISTS_TAC `lift s` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\v. (h:real^N->real^N)
                      (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0
                                 (drop v)))` THEN
    EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
      DISCH_TAC THEN
      REMOVE_THEN "E1" (MP_TAC o SPEC `drop v`) THEN REMOVE_THEN "E2" (MP_TAC o SPEC `drop v`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      EXPAND_TAC "h" THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                     `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                     `Phi:real^N->real^(N,N)finite_sum`; `s2:real`; `r2:real`; `W2:A->bool`;
                     `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                     `Phi2:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `drop v`]
                    P2AL_WIN_TRANS_REP) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MP_TAC(ASSUME `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi`) THEN
        REWRITE_TAC[p2al_wok] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\v. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 (drop v))`;
                   `h:real^N->real^N`;
                   `sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`;
                   `D:real^N->real^N`; `lift s`] ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the Jacobi matrix transforms with Dh *)
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AL_WOK_SLICE) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s2:real`; `r2:real`; `W2:A->bool`; `a2:real`;
                 `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                 `Phi2:real^N->real^(N,N)finite_sum`; `s:real`] P2AL_WOK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !Z. dist(Z,Z0) < d
            ==> Z IN {Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} /\
                Z IN {Z | Z IN N2 /\ p2al_lin V tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z s}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} INTER
                  {Z | Z IN N2 /\ p2al_lin V tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z s}`
                  OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `Z0:real^N`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; SUBSET; IN_BALL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. p2al_jy (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z0 s ** c =
        (D:real^N->real^N) (p2al_jy V tt s1 r W b' U (phi:A->real^N) Phi Z0 s ** c)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s2:real`; `r2:real`; `W2:A->bool`; `a2:real`;
                   `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                   `Phi2:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_LFL_HASDER_YB) THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                  P2AL_LFL_HASDER_YB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
    DISCH_THEN(MP_TAC o C CONJ (ASSUME
      `((h:real^N->real^N) has_derivative D)
         (at (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)))`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN_AT o BETA_RULE) THEN
    REWRITE_TAC[FSTCART_PASTECART; o_DEF] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
    REWRITE_TAC[FSTCART_PASTECART] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\Z. fstcart(p2al_lfl (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z s)) has_derivative
       (\c. (D:real^N->real^N) (p2al_jy V tt s1 r W b' U (phi:A->real^N) Phi Z0 s ** c)))
      (at Z0)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      EXISTS_TAC `\Z. (h:real^N->real^N)
                        (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s))` THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      EXPAND_TAC "h" THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                     `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                     `Phi:real^N->real^(N,N)finite_sum`; `s2:real`; `r2:real`; `W2:A->bool`;
                     `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                     `Phi2:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`]
                    P2AL_WIN_TRANS_REP) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C CONJ (ASSUME
      `((\Z. fstcart(p2al_lfl (V:p2alv) tt s2 r2 W2 b2 U2 (phi2:A->real^N) Phi2 Z s))
        has_derivative (\c. p2al_jy V tt s2 r2 W2 b2 U2 phi2 Phi2 Z0 s ** c)) (at Z0)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    DISCH_THEN(MP_TAC o C AP_THM `c:real^N`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  (* the metric is the pullback *)
  MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a':real`; `b':real`; `W2:A->bool`; `a2:real`;
                 `b2:real`; `U:A->bool`; `phi:A->real^N`; `U2:A->bool`; `phi2:A->real^N`;
                 `tt - s pow 2`;
                 `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s)`]
                P2A_RLOCAL_TRANS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[P2AL_MY_ALG] THEN ASM_SIMP_TAC[MATRIX_WORKS]);;

(* ========================================================================= *)
(* The first variation formula along the whole L-geodesic. Jacobi data of    *)
(* the start window at s = 0 (Y(0) = 0, B(0) = 2 I, P2AL_SWIN_JYB0), one     *)
(* step inside a window (P2AL_FV_STEP), the start (P2AL_FV_START), and by    *)
(* continuity induction (P2A_REAL_CONT_INDUCT) the formula D_Z Ltil(Z,s^2) c *)
(* = (Y c) . (G A) in every window (P2AL_FV_ALL).                            *)
(* ========================================================================= *)

let P2AL_SWIN_JYB0 = prove
 (`!(V:p2alv) tt (x:A) W a U (phi:A->real^N) Z0.
     p2a_region V W a tt /\ x IN W /\ chart_at (p2a_vatlas V tt) x = (U,phi)
     ==> p2al_lin V tt (&0) (sqrt(tt - a)) W tt U phi (\Z. pastecart (phi x) (&2 % Z)) Z0 (&0) /\
         p2al_jy V tt (&0) (sqrt(tt - a)) W tt U phi (\Z. pastecart (phi x) (&2 % Z)) Z0 (&0) =
         mat 0 /\
         p2al_jb V tt (&0) (sqrt(tt - a)) W tt U phi (\Z. pastecart (phi x) (&2 % Z)) Z0 (&0) =
         &2 %% mat 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W:A->bool`; `a:real`; `U:A->bool`;
                 `phi:A->real^N`] P2AL_SWIN_WOK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pastecart (lift(&0)) (pastecart ((phi:A->real^N) x) (&2 % (Z0:real^N))) IN
    interval(lift(&0 - sqrt(tt - a)),lift(&0 + sqrt(tt - a))) PCROSS
    (IMAGE phi (U INTER W) PCROSS (:real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lin (V:p2alv) tt (&0) (sqrt(tt - a)) W tt U (phi:A->real^N)
      (\Z. pastecart (phi x) (&2 % Z)) Z0 (&0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2al_lin; ODE_IN_DOMAIN] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt`;
                   `interval(lift(&0 - sqrt(tt - a)),lift(&0 + sqrt(tt - a))) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `pastecart (lift(&0)) (pastecart ((phi:A->real^N) x) (&2 % (Z0:real^N)))`]
                  ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a)`; `W:A->bool`; `a:real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `(:real^N)`;
                 `\Z:real^N. pastecart ((phi:A->real^N) x) (&2 % Z)`; `Z0:real^N`; `&0`]
                P2AL_JYB_COLUMNS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `frechet_derivative (\Z:real^N. pastecart ((phi:A->real^N) x) (&2 % Z)) (at Z0) =
    (\h. pastecart (vec 0) (&2 % h))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. p2al_jcol (V:p2alv) tt (&0) (sqrt(tt - a)) W tt U (phi:A->real^N)
          (\Z. pastecart (phi x) (&2 % Z)) Z0 j (&0) =
        pastecart (vec 0) (&2 % basis j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[p2al_jcol] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt`;
                   `interval(lift(&0 - sqrt(tt - a)),lift(&0 + sqrt(tt - a))) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `lift(&0)`; `pastecart ((phi:A->real^N) x) (&2 % (Z0:real^N))`;
                   `pastecart (vec 0:real^N) (&2 % basis j:real^N)`]
                  ODE_FLOW_VARIATIONAL_FIXED_TIME) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[smooth_map_on]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_fmat] THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MAT_COMPONENT; MATRIX_CMUL_COMPONENT;
           VEC_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2AL_FV_STEP = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 sa sb.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ Z0 IN p2a_Ldom V tt x b /\
     s1 <= sa /\ &0 < sa /\ sa <= sb /\ sb < s1 + r /\ sb pow 2 < b /\
     (!s. sa <= s /\ s <= sb ==> p2al_lin V tt s1 r W b' U phi Phi Z0 s) /\
     ((\Z. lift(p2a_Ltil V tt x (sa pow 2) Z)) has_derivative
      (\c. lift((p2al_jy V tt s1 r W b' U phi Phi Z0 sa ** c) dot
                (p2a_rlocal V W b' (U INTER W,phi) (tt - sa pow 2)
                   (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)) **
                 sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa))))) (at Z0)
     ==> ((\Z. lift(p2a_Ltil V tt x (sb pow 2) Z)) has_derivative
          (\c. lift((p2al_jy V tt s1 r W b' U phi Phi Z0 sb ** c) dot
                    (p2a_rlocal V W b' (U INTER W,phi) (tt - sb pow 2)
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb)) **
                     sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sb))))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `sa:real`; `sb:real`]
                P2AL_FV_INT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                   `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`] P2A_LDOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Z0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_ADD o CONJ (ASSUME
   `((\Z. lift(p2a_Ltil (V:p2alv) tt (x:A) (sa pow 2) Z)) has_derivative
     (\c. lift((p2al_jy V tt s1 r W b' U (phi:A->real^N) Phi Z0 sa ** c) dot
               (p2a_rlocal V W b' (U INTER W,phi) (tt - sa pow 2)
                  (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa)) **
                sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 sa))))) (at Z0)`)) THEN
  REWRITE_TAC[GSYM LIFT_ADD; REAL_ARITH `a + (b - a:real) = b`] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\Z. lift(p2a_Ltil (V:p2alv) tt (x:A) (sa pow 2) Z +
             real_integral (real_interval[sa,sb])
               (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi:A->real^N)) tt s
                      (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                      (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))))` THEN
  EXISTS_TAC `min d d'` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b /\ Z IN ball(Z0,d)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sb /\ sa pow 2 <= b /\ sb pow 2 <= b` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sb pow 2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sb:real`] P2AL_LTIL_INT) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `sa:real`] P2AL_LTIL_INT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `sb <= sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_LSINT_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b) real_integrable_on real_interval[&0,sb]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,sqrt b]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b`; `&0`; `sb:real`; `sa:real`]
                REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  BETA_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2AL_WOK_LSINT THEN
  MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `s:real`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sb pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

let P2AL_FV_START = prove
 (`!(V:p2alv) tt (x:A) b W a U (phi:A->real^N) Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2a_region V W a tt /\ x IN W /\ chart_at (p2a_vatlas V tt) x = (U,phi) /\
     Z0 IN p2a_Ldom V tt x b /\ &0 < s /\ s < sqrt(tt - a) /\ s pow 2 < b /\
     (!s'. &0 <= s' /\ s' <= s
           ==> p2al_lin V tt (&0) (sqrt(tt - a)) W tt U phi (\Z. pastecart (phi x) (&2 % Z))
                 Z0 s')
     ==> ((\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) has_derivative
          (\c. lift((p2al_jy V tt (&0) (sqrt(tt - a)) W tt U phi
                       (\Z. pastecart (phi x) (&2 % Z)) Z0 s ** c) dot
                    (p2a_rlocal V W tt (U INTER W,phi) (tt - s pow 2)
                       (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a)) W tt U phi
                                  (\Z. pastecart (phi x) (&2 % Z)) Z0 s)) **
                     sndcart(p2al_lfl V tt (&0) (sqrt(tt - a)) W tt U phi
                               (\Z. pastecart (phi x) (&2 % Z)) Z0 s))))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W:A->bool`; `a:real`; `U:A->bool`;
                 `phi:A->real^N`] P2AL_SWIN_WOK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W:A->bool`; `a:real`; `U:A->bool`;
                 `phi:A->real^N`; `Z0:real^N`] P2AL_SWIN_JYB0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `sqrt(tt - a)`; `W:A->bool`; `a:real`;
                 `tt:real`; `U:A->bool`; `phi:A->real^N`; `(:real^N)`;
                 `\Z:real^N. pastecart ((phi:A->real^N) x) (&2 % Z)`; `Z0:real^N`;
                 `&0`; `s:real`] P2AL_FV_INT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2al_lwa (V:p2alv) tt (&0) (sqrt(tt - a)) W a tt U (phi:A->real^N) (:real^N)
                   (\Z. pastecart (phi x) (&2 % Z))` THEN
    REWRITE_TAC[p2al_lwa] THEN
    DISCH_THEN(MP_TAC o SPEC `s':real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`s':real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `p2al_jy (V:p2alv) tt (&0) (sqrt(tt - a)) W tt U (phi:A->real^N)
      (\Z. pastecart (phi x) (&2 % Z)) Z0 (&0) = mat 0`;
    MATRIX_VECTOR_MUL_LZERO; DOT_LZERO; REAL_SUB_RZERO]) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`] P2A_LDOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Z0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\Z. lift(real_integral (real_interval[&0,s])
               (\s'. p2a_llag (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)) tt s'
                       (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a)) W tt U phi
                                  (\Z. pastecart (phi x) (&2 % Z)) Z s'))
                       (sndcart(p2al_lfl V tt (&0) (sqrt(tt - a)) W tt U phi
                                  (\Z. pastecart (phi x) (&2 % Z)) Z s'))))` THEN
  EXISTS_TAC `min d d'` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) b /\ Z IN ball(Z0,d)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`] P2AL_LTIL_INT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2AL_WOK_LSINT THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `(:real^N)`] THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `t:real`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

(* The first variation property at s: the derivative in every window.       *)

let p2al_fvp = new_definition
 `p2al_fvp (V:p2alv) tt (x:A) (Z0:real^N) s <=>
    !s1 r W a' b' U (phi:A->real^N) N Phi.
      p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
      p2al_lin V tt s1 r W b' U phi Phi Z0 s
      ==> ((\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) has_derivative
           (\c. lift((p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) dot
                     (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                        (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                      sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))) (at Z0)`;;

let P2AL_FVP_ONE = prove
 (`!(V:p2alv) tt (x:A) Z0 s s1 r W a' b' U (phi:A->real^N) N Phi.
     p2a_svs V /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     ((\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) has_derivative
      (\c. lift((p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) dot
                (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                   (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
                 sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))) (at Z0)
     ==> p2al_fvp V tt x Z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2al_fvp] THEN
  MAP_EVERY X_GEN_TAC [`s2:real`; `r2:real`; `W2:A->bool`; `a2:real`; `b2:real`;
                       `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                       `Phi2:real^N->real^(N,N)finite_sum`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN X_GEN_TAC `c:real^N` THEN
  MATCH_MP_TAC P2AL_MY_INV THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `N:real^N->bool`; `a2:real`; `N2:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

let P2AL_FV_START_NBHD = prove
 (`!(V:p2alv) tt (x:A) b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> ?e. &0 < e /\ !s. &0 < s /\ s < e /\ s pow 2 < b ==> p2al_fvp V tt x Z0 s`,
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
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2al_wok]) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `&0`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT]; ALL_TAC] THEN
  EXISTS_TAC `min e0 (sqrt(tt - a0))` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AL_FVP_ONE THEN
  MAP_EVERY EXISTS_TAC
   [`&0`; `sqrt(tt - a0)`; `W0:A->bool`; `a0:real`; `tt:real`; `U0:A->bool`;
    `phi0:A->real^N`; `(:real^N)`; `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_ADD_LID] THEN
  SUBGOAL_THEN
   `!s'. &0 <= s' /\ s' <= s
         ==> p2al_lin (V:p2alv) tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
               (\Z. pastecart (phi0 x) (&2 % Z)) Z0 s'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  MATCH_MP_TAC P2AL_FV_START THEN
  EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]);;

let P2AL_FV_GROW = prove
 (`!(V:p2alv) tt (x:A) b Z0 Tm.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b /\ &0 < Tm /\ Tm pow 2 < b
     ==> ?e. &0 < e /\
             !s s'. abs(s - Tm) < e /\ abs(s' - Tm) < e /\ &0 < s' /\ s' <= s /\
                    s pow 2 < b /\ p2al_fvp V tt x Z0 s'
                    ==> p2al_fvp V tt x Z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z0:real^N`; `b:real`; `Tm:real`]
                P2AL_LWIN_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `N:real^N->bool`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `Tm:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s':real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC P2AL_FVP_ONE THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                        `phi:A->real^N`; `N:real^N->bool`; `Phi:real^N->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AL_FV_STEP THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `a':real`; `N:real^N->bool`; `s':real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    UNDISCH_TAC `p2al_fvp (V:p2alv) tt (x:A) Z0 s'` THEN REWRITE_TAC[p2al_fvp] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

let P2AL_FV_ALL = prove
 (`!(V:p2alv) tt (x:A) b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> !s. &0 < s /\ s pow 2 < b ==> p2al_fvp V tt x Z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `Sb:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`] P2AL_FV_START_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= Sb ==> s pow 2 < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `Sb pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. &0 < s ==> p2al_fvp (V:p2alv) tt (x:A) Z0 s`; `Sb:real`]
                P2A_REAL_CONT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `Tm:real`]
                    P2AL_FV_GROW) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `Tm - min e Tm / &2` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM(MP_TAC o SPEC `Tm - min e Tm / &2` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `Tm = &0` THENL
       [EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `Tm:real`]
                    P2AL_FV_GROW) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN DISCH_TAC THEN
      ASM_CASES_TAC `s <= Tm` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Tm:real`)) (concl th) &&
          not (can (find_term ((=) `e:real`)) (concl th)))) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
      EXISTS_TAC `Tm:real` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `Tm:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Tm:real`)) (concl th) &&
          not (can (find_term ((=) `e:real`)) (concl th)))) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]]];
    DISCH_THEN(MP_TAC o SPEC `Sb:real`) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Self-adjointness of the shape operator.  From the first variation formula *)
(* and the symmetry of second derivatives (SCHWARZ_C2 of the vendored NS     *)
(* smooth calculus): Y^T P is symmetric, P = D_Z (G A); hence G S is         *)
(* symmetric for S = B Y^-1 + Gamma(A,.) (P2AL_WOK_SYM).                     *)
(* ========================================================================= *)

let P2AL_SYM_DOT = prove
 (`!M:real^N^N. (!a b. a dot (M ** b) = b dot (M ** a)) ==> symmetric_matrix M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[symmetric_matrix; MATRIX_EQ] THEN
  X_GEN_TAC `u:real^N` THEN ONCE_REWRITE_TAC[GSYM VECTOR_EQ_RDOT] THEN
  X_GEN_TAC `w:real^N` THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_MESON_TAC[DOT_SYM]);;

(* The algebraic step: if Y is invertible and (Y u).P(v) is symmetric with  *)
(* P(v) = DG[Y v] A + G B v, then G (B Y^-1 + Gamma(A,.)) is symmetric.     *)

let P2AL_SYM_FROM_YP = prove
 (`!U (G:real^N->real^N^N) y (A:real^N) (Y:real^N^N) (B:real^N^N).
     metric_field U G /\ y IN U /\ ~(det Y = &0) /\
     (!u v. (Y ** u) dot (mderiv G y (Y ** v) ** A + G y ** (B ** v)) =
            (Y ** v) dot (mderiv G y (Y ** u) ** A + G y ** (B ** u)))
     ==> symmetric_matrix(G y ** (B ** matrix_inv Y + matrix(christoffel G y A)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL_SYM_DOT THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `c:real^N`] THEN
  SUBGOAL_THEN `invertible(Y:real^N^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN `linear(christoffel (G:real^N->real^N^N) y A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] CHRISTOFFEL_BILINEAR) THEN
    ASM_REWRITE_TAC[bilinear] THEN
    DISCH_THEN(MP_TAC o SPEC `A:real^N` o CONJUNCT1) THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `u = matrix_inv(Y:real^N^N) ** a` THEN
  ABBREV_TAC `v = matrix_inv(Y:real^N^N) ** c` THEN
  SUBGOAL_THEN `a = (Y:real^N^N) ** u /\ c = Y ** v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `a = (Y:real^N^N) ** u`; ASSUME `c = (Y:real^N^N) ** v`] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
  SUBGOAL_THEN `matrix_inv(Y:real^N^N) ** Y ** u = u /\ matrix_inv Y ** Y ** v = v`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[DOT_RADD] THEN
  SUBGOAL_THEN `metric_field (U:real^N->bool) G /\ (y:real^N) IN U` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun mf ->
    MP_TAC(SPECL [`A:real^N`; `(Y:real^N^N) ** u`; `(Y:real^N^N) ** v`]
             (MATCH_MP LRG_CHRISTOFFEL_DOT mf)) THEN
    MP_TAC(SPECL [`A:real^N`; `(Y:real^N^N) ** v`; `(Y:real^N^N) ** u`]
             (MATCH_MP LRG_CHRISTOFFEL_DOT mf)) THEN
    MP_TAC(SPECL [`A:real^N`; `(Y:real^N^N) ** u`; `(Y:real^N^N) ** v`]
             (MATCH_MP LRG_MDERIV_SYM mf)) THEN
    MP_TAC(SPECL [`(Y:real^N^N) ** v`; `(Y:real^N^N) ** u`; `A:real^N`]
             (MATCH_MP LRG_MDERIV_SYM mf)) THEN
    MP_TAC(SPECL [`(Y:real^N^N) ** u`; `(Y:real^N^N) ** v`; `A:real^N`]
             (MATCH_MP LRG_MDERIV_SYM mf)) THEN
    MP_TAC(SPECL [`(Y:real^N^N) ** u`; `(B:real^N^N) ** v`]
             (MATCH_MP LRG_METRIC_SYM mf)) THEN
    MP_TAC(SPECL [`(Y:real^N^N) ** v`; `(B:real^N^N) ** u`]
             (MATCH_MP LRG_METRIC_SYM mf))) THEN
  MP_TAC(SPECL [`u:real^N`; `v:real^N`] (ASSUME
   `!u v. ((Y:real^N^N) ** u) dot (mderiv (G:real^N->real^N^N) y (Y ** v) ** A + G y ** (B ** v)) =
          (Y ** v) dot (mderiv G y (Y ** u) ** A + G y ** (B ** u))`)) THEN
  REWRITE_TAC[DOT_RADD] THEN REAL_ARITH_TAC);;


(* The momentum m(Z) = G(y(s,Z)) A(s,Z) in a window and its Z-derivative    *)
(* P c = DG[Y c] A + G B c.                                                  *)

let P2AL_M_HASDER = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z0 IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s
     ==> ((\Z. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                 (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
               sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) has_derivative
          (\c. mderiv (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                      (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                      (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) **
                 sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) +
               p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                 (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
               (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c))) (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPECL [`Z0:real^N`; `s:real`]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^N) (U INTER W))
      (p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
                   (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))` THEN
    REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "metric_field")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o
     p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
    differentiable at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LFL_HASDER_YB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2AL_HASDER_CARTS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSTCART_PASTECART; SNDCART_PASTECART]) THEN
  MP_TAC(ISPECL
   [`\Z. p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))`;
    `\c. frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                             p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
                            (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))
                            (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c)`;
    `\Z. sndcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)`;
    `\c. p2al_jb (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s ** c`;
    `Z0:real^N`] LRG_HAS_DERIVATIVE_MATVEC) THEN
  REWRITE_TAC[mderiv] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\Z. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o
                  p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)`;
                 `\c. p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z0 s ** c`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
                    (at (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))`;
                 `Z0:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN REWRITE_TAC[o_DEF]);;

(* The slice of a window at s inside Ldom(b): open, the chart position and  *)
(* the momentum are smooth there, and Ltil(.,s^2) has the first-variation   *)
(* derivative at each of its points.                                         *)

let P2AL_SLICE_FACTS = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b
     ==> open {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
                   Z IN p2a_Ldom V tt x b} /\
         smooth_map_on {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
                            Z IN p2a_Ldom V tt x b}
           (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) /\
         smooth_map_on {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
                            Z IN p2a_Ldom V tt x b}
           (\Z. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                  (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
                sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) /\
         (!Z. Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\ Z IN p2a_Ldom V tt x b
              ==> ((\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) has_derivative
                   (\c. lift(frechet_derivative
                               (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) (at Z) c dot
                             (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
                              sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))))) (at Z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AL_WOK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`] P2A_LDOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s /\
         Z IN p2a_Ldom V tt x b} =
    {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s} INTER p2a_Ldom V tt x b`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open({Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} INTER
         p2a_Ldom V tt x b)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ({Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} INTER
                   p2a_Ldom V tt x b)
                  (\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ({Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} INTER
                   p2a_Ldom V tt x b)
                  (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) /\
    smooth_map_on ({Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s} INTER
                   p2a_Ldom V tt x b)
                  (\Z. sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}
                      INTER p2a_Ldom V tt x b`;
                     `\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`]
                    SMOOTH_MAP_ON_FSTCART_OPEN);
      MP_TAC(ISPECL [`{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}
                      INTER p2a_Ldom V tt x b`;
                     `\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`]
                    SMOOTH_MAP_ON_SNDCART_OPEN)] THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (phi:A->real^N) (U INTER W))
        (p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN
      REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "metric_field")) (concl th))) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                     `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                     `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`]
                    P2AL_WOK_FACTS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\Z. p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
             (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))) =
      (vectorize o p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) o
      (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_LWIN_FACTS o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lwa")) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPECL [`Z:real^N`; `s:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_FV_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi`) THEN
    REWRITE_TAC[p2al_wok] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2al_fvp] THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                             `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                             `Phi:real^N->real^(N,N)finite_sum`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `c:real^N` THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `s:real`] P2AL_LFL_HASDER_YB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
  REWRITE_TAC[FSTCART_PASTECART] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* Calculus core: if F has derivative c |-> (D y(Z) c) . m(Z) on an open S, *)
(* with y and m smooth, then (D y(Z0) u) . (D m(Z0) v) is symmetric in      *)
(* (u,v) (symmetry of the second derivatives of F and of y).                 *)

let P2AL_FV_SCHWARZ = prove
 (`!S (Fl:real^N->real^1) (fy:real^N->real^N) (mm:real^N->real^N) P Z0.
     open S /\ Z0 IN S /\ smooth_map_on S fy /\ smooth_map_on S mm /\
     (!Z. Z IN S
          ==> (Fl has_derivative (\c. lift(frechet_derivative fy (at Z) c dot mm Z))) (at Z)) /\
     (mm has_derivative P) (at Z0)
     ==> !u v. (frechet_derivative fy (at Z0) u) dot (P v) =
               (frechet_derivative fy (at Z0) v) dot (P u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 2 S (Fl:real^N->real^1)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 = SUC 1`; CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    EXISTS_TAC `\Z c. lift(frechet_derivative (fy:real^N->real^N) (at Z) c dot
                           (mm:real^N->real^N) Z)` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[];
      X_GEN_TAC `h:real^N` THEN
      SUBGOAL_THEN
       `smooth_map_on S (\Z. lift(frechet_derivative (fy:real^N->real^N) (at Z) h dot
                                  (mm:real^N->real^N) Z))`
      MP_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
        REWRITE_TAC[smooth_map_on] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 2 S (fy:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(P:real^N->real^N) /\
                linear(frechet_derivative (fy:real^N->real^N) (at Z0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the second derivative of Fl through the product rule *)
  SUBGOAL_THEN
   `!i. ((\z. frechet_derivative (Fl:real^N->real^1) (at z) (basis i)) has_derivative
         (\d. lift(frechet_derivative (fy:real^N->real^N) (at Z0) (basis i) dot (P:real^N->real^N) d) +
              lift(frechet_derivative (\z. frechet_derivative fy (at z) (basis i)) (at Z0) d dot
                   (mm:real^N->real^N) Z0))) (at Z0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift(frechet_derivative (fy:real^N->real^N) (at z) (basis i) dot
                         (mm:real^N->real^N) z)` THEN
    FIRST_ASSUM(MP_TAC o SPEC `Z0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (S:real^N->bool)`)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN S` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`;
                   `\z. frechet_derivative (fy:real^N->real^N) (at z) (basis i)`;
                   `mm:real^N->real^N`;
                   `frechet_derivative (\z. frechet_derivative (fy:real^N->real^N) (at z) (basis i))
                      (at Z0)`;
                   `P:real^N->real^N`; `Z0:real^N`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* symmetry on basis vectors *)
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> frechet_derivative (fy:real^N->real^N) (at Z0) (basis i) dot
              (P:real^N->real^N) (basis j) =
              frechet_derivative fy (at Z0) (basis j) dot P (basis i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^N->bool`; `Fl:real^N->real^1`; `Z0:real^N`; `i:num`; `j:num`]
                  SCHWARZ_C2) THEN
    MP_TAC(ISPECL [`S:real^N->bool`; `fy:real^N->real^N`; `Z0:real^N`; `i:num`; `j:num`]
                  SCHWARZ_C2) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th) &&
        can (find_term ((=) `P:real^N->real^N`)) (concl th))) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o SPEC `j:num` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th) &&
        can (find_term ((=) `P:real^N->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(a:real^1) + b = c + b <=> a = c`; LIFT_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u v:real^N. lift(frechet_derivative (fy:real^N->real^N) (at Z0) u dot (P:real^N->real^N) v)`;
    `\u v:real^N. lift(frechet_derivative (fy:real^N->real^N) (at Z0) v dot (P:real^N->real^N) u)`]
   BILINEAR_EQ_STDBASIS) THEN
  ASM_SIMP_TAC[FUN_EQ_THM; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[bilinear; linear] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linear]) THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

let P2AL_WOK_SYM = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> symmetric_matrix
           (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
              (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
            (p2al_jb V tt s1 r W b' U phi Phi Z0 s **
             matrix_inv(p2al_jy V tt s1 r W b' U phi Phi Z0 s) +
             matrix(christoffel (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                      (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                      (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^N) (U INTER W))
      (p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci_flow")) (concl th))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AL_SYM_FROM_YP THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_M_HASDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s /\
          Z IN p2a_Ldom V tt (x:A) b}`;
    `\Z. lift(p2a_Ltil (V:p2alv) tt (x:A) (s pow 2) Z)`;
    `\Z. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)`;
    `\Z. p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
         sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)`;
    `\c. mderiv (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
                (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))
                (p2al_jy V tt s1 r W b' U phi Phi Z0 s ** c) **
           sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s) +
         p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
           (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s)) **
         (p2al_jb V tt s1 r W b' U phi Phi Z0 s ** c)`;
    `Z0:real^N`] P2AL_FV_SCHWARZ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_LFL_HASDER_YB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_HASDER_CARTS) THEN
  REWRITE_TAC[FSTCART_PASTECART] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN SIMP_TAC[]);;

(* The comparison function of a window is non-increasing where Y is         *)
(* invertible (P2AL_GFUN_DERIV of pc_p2a_lric with the window data).         *)

let P2AL_WOK_GW_DERIV = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\ s pow 2 < b /\
     ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0)
     ==> ?g'. ((\s'. p2al_gw V tt x s1 r W b' U phi Phi Z0 s') has_real_derivative g')
                (atreal s) /\ g' <= &0`,
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
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
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
    `\s'. p2a_Ltil (V:p2alv) tt (x:A) (s' pow 2) Z0`] P2AL_GFUN_DERIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2al_gw]);;

