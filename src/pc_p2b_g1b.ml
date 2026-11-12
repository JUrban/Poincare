(* ========================================================================= *)
(* Unit pc_p2b_g1b (Part 2B): the chart data of the members of the G1        *)
(* sequence on a chart box of the limit (vocabulary of pc_p2b_w920g): local  *)
(* chart representation of the members (charts of M read through phi_k), the *)
(* weak forms of W3 moved to the limit charts (P2BX_T1_TRANSFER and the      *)
(* gluing lemmas of pc_p2b_g1w), and the regularity of the member metrics    *)
(* and scalar curvatures.                                                    *)
(* ========================================================================= *)

needs "src/pc_p2b_g1a.ml";;
needs "src/pc_p2b_g1w.ml";;
needs "src/pc_p2b_fchart.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The members read in a chart of M.                                         *)
(* ========================================================================= *)

(* Near a point of a chart c of the limit, the member f = phi k is read in  *)
(* the chart c0 of M at f(y0): H = SND c0 o f o chart_inv c is a local      *)
(* diffeomorphism and the pullback metric is mpullback H of the chart       *)
(* metric of c0.                                                             *)

let P2BX_MEMBER_CHART = prove
 (`!(top':B topology) atlas' (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
    W (f:B->A) f' (c:(B->bool)#(B->real^N)) y0.
     smooth_manifold_atlas top' atlas' /\ smooth_manifold_atlas top atlas /\
     mfd_diffeo top' atlas' W top atlas (IMAGE f W) f f' /\ c IN atlas' /\
     y0 IN FST c /\ y0 IN W
     ==> ?U V (H:real^N->real^N) H' c0.
           c0 IN atlas /\ open U /\ SND c y0 IN U /\ diffeomorphism_on U V H H' /\
           (!x. x IN U
                ==> chart_inv c x IN FST c /\ chart_inv c x IN W /\
                    SND c (chart_inv c x) = x /\
                    f(chart_inv c x) IN FST c0 /\ H x = SND c0 (f(chart_inv c x)) /\
                    H x IN IMAGE (SND c0) (FST c0) /\
                    chart_inv c0 (H x) = f(chart_inv c x)) /\
           (!h x. x IN U
                  ==> rfs_pullback atlas (f o chart_inv c) h x =
                      transp(matrix(frechet_derivative H (at x))) **
                      metric_local atlas c0 h (H x) **
                      matrix(frechet_derivative H (at x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(f:B->A) y0 IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(y0:B) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:B->A) y0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:B->A) y0)` THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W:B->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (f:B->A) W`; `f:B->A`; `f':A->B`;
                 `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND(c:(B->bool)#(B->real^N)))
                        {x | x IN FST c INTER W /\ (f:B->A) x IN FST(c0:(A->bool)#(A->real^N))}` THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`;
    `IMAGE (SND(c0:(A->bool)#(A->real^N)))
           {y | y IN FST c0 INTER IMAGE (f:B->A) W /\ (f':A->B) y IN FST(c:(B->bool)#(B->real^N))}`;
    `SND(c0:(A->bool)#(A->real^N)) o (f:B->A) o chart_inv(c:(B->bool)#(B->real^N))`;
    `SND(c:(B->bool)#(B->real^N)) o (f':A->B) o chart_inv(c0:(A->bool)#(A->real^N))`;
    `c0:(A->bool)#(A->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> chart_inv (c:(B->bool)#(B->real^N)) x IN FST c /\ chart_inv c x IN W /\
            SND c (chart_inv c x) = x /\
            (f:B->A)(chart_inv c x) IN FST(c0:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [diffeomorphism_on]);
    EXPAND_TAC "U" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN EXPAND_TAC "c0" THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `x:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `U:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real^N^N`;
                 `IMAGE (SND(c:(B->bool)#(B->real^N))) (FST c INTER W)`;
                 `(f:B->A) o chart_inv(c:(B->bool)#(B->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `x:real^N`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIR; o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_PARAM_EMBED THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                            `IMAGE (f:B->A) W`; `f':A->B`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `x = SND(c:(B->bool)#(B->real^N)) (chart_inv c x)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback; o_ASSOC]);;

(* ========================================================================= *)
(* The space-time data of a member near a point of a box are the data of a   *)
(* chart of M moved by Phi(x,t) = (H x, lam t) (the predicate p2bx_wtr       *)
(* of pc_p2b_g1w).                                                           *)
(* ========================================================================= *)

let P2BX_MEMBER_WTR = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p (top':B topology) atlas' W (f:B->A) f'
    (c:(B->bool)#(B->real^3)) lam a (om:real^(3,1)finite_sum->bool) z0.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top' atlas' W top atlas (IMAGE f W) f f' /\ c IN atlas' /\
     &0 < lam /\ a < &0 /\ open om /\
     (!z. z IN om ==> fstcart z IN IMAGE (SND c) (FST c INTER W) /\ &0 < drop(sndcart z) /\
                      lam * drop(sndcart z) < --a) /\
     (!c0. c0 IN atlas
           ==> (\w. (vectorize:real^3^3->real^(3,3)finite_prod)
                      (p2bw_cmet atlas c0 (&0) g w)) continuous_on p2bw_cdom c0 (&0 - a) /\
               (!w. w IN p2bw_cdom c0 (&0 - a)
                    ==> transp(p2bw_cmet atlas c0 (&0) g w) = p2bw_cmet atlas c0 (&0) g w /\
                        !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cmet atlas c0 (&0) g w ** v)) /\
               (\w. lift(p2bw_cscal atlas c0 (&0) g w)) continuous_on p2bw_cdom c0 (&0 - a) /\
               wan_loclip (p2bw_cdom c0 (&0 - a))
                 (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                       (&0) p))) /\
     z0 IN om
     ==> ?U V H H' c0 N0.
           c0 IN atlas /\ z0 IN N0 /\ N0 SUBSET om /\
           p2bx_wtr U V H H' lam (p2bw_cdom c0 (&0 - a)) (p2bw_cmet atlas c0 (&0) g)
             (p2bw_cscal atlas c0 (&0) g)
             (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p))
             N0
             (\z. inv lam %% rfs_pullback atlas (f o chart_inv c)
                                (g(--(lam * drop(sndcart z)))) (fstcart z))
             (\z. lam * mfd_scalar atlas (g(--(lam * drop(sndcart z))))
                                   (f(chart_inv c (fstcart z))))
             (\z. p2b_klx (top,atlas) g p (lam * drop(sndcart z)) (f(chart_inv c (fstcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:B. y0 IN FST(c:(B->bool)#(B->real^3)) /\ y0 IN W /\
                       fstcart(z0:real^(3,1)finite_sum) = SND c y0`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^(3,1)finite_sum` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `om:real^(3,1)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:B->bool`; `f:B->A`; `f':A->B`; `c:(B->bool)#(B->real^3)`; `y0:B`]
                P2BX_MEMBER_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `V:real^3->bool`
    (X_CHOOSE_THEN `H:real^3->real^3` (X_CHOOSE_THEN `H':real^3->real^3`
    (X_CHOOSE_THEN `c0:(A->bool)#(A->real^3)` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `V:real^3->bool`; `H:real^3->real^3`;
                        `H':real^3->real^3`; `c0:(A->bool)#(A->real^3)`;
                        `{z:real^(3,1)finite_sum | z IN om /\ fstcart z IN U}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c0:(A->bool)#(A->real^3)` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_cmet"))
                                          (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c0:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bx_wtr; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_CDOM_OPEN THEN ASM_REWRITE_TAC[];
    SIMP_TAC[p2bw_cdom; IN_ELIM_THM];
    SUBGOAL_THEN `{z:real^(3,1)finite_sum | z IN om /\ fstcart z IN U} =
                  om INTER (U PCROSS (:real^1))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTER;
                  FSTCART_PASTECART; IN_UNIV];
      MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `om:real^(3,1)finite_sum->bool`)) (concl th) &&
    can (find_term ((=) `a:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `fstcart(z:real^(3,1)finite_sum)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `U:real^3->bool`)) (concl th) &&
    not (can (find_term ((=) `h:A->real^3^3`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `(H:real^3->real^3)(fstcart(z:real^(3,1)finite_sum))`)) THEN
  REWRITE_TAC[p2bw_cmet; p2bw_cscal; p2bw_cfun; p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP; REAL_SUB_LZERO] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < lam * drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BX_KLX_VIEW]);;

(* ========================================================================= *)
(* The source data in a chart c0 of M on the backward-time slab (0, -a):     *)
(* regularity (P2B_FLOW_CHART) and the three weak forms of W3, in the        *)
(* coefficient form of pc_p2b_g1w.                                           *)
(* ========================================================================= *)

let P2BX_CA_FORM = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c b (g:real->A->real^N^N).
     p2bw_cA atlas c b g =
     (\z. sqrt(det(p2bw_cmet atlas c b g z)) %% matrix_inv(p2bw_cmet atlas c b g z)) /\
     p2bw_crho atlas c b g = (\z. sqrt(det(p2bw_cmet atlas c b g z)))`,
  REWRITE_TAC[FUN_EQ_THM; p2bw_cA; p2bw_crho]);;

let P2BX_W3_SOURCE = prove
 (`!(u:A->bool) kappa top atlas (g:real->A->real^3^3) p a.
     P2B_REQ_P2A_WEAK_STATEMENT u /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ a < &0
     ==> !c0. c0 IN atlas
              ==> (\w. (vectorize:real^3^3->real^(3,3)finite_prod)
                         (p2bw_cmet atlas c0 (&0) g w)) continuous_on p2bw_cdom c0 (&0 - a) /\
                  (!w. w IN p2bw_cdom c0 (&0 - a)
                       ==> transp(p2bw_cmet atlas c0 (&0) g w) = p2bw_cmet atlas c0 (&0) g w /\
                           !v. ~(v = vec 0)
                               ==> &0 < v dot (p2bw_cmet atlas c0 (&0) g w ** v)) /\
                  (\w. lift(p2bw_cscal atlas c0 (&0) g w)) continuous_on p2bw_cdom c0 (&0 - a) /\
                  wan_loclip (p2bw_cdom c0 (&0 - a))
                    (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                          (&0) p)) /\
                  p2bw_t1 (p2bw_cdom c0 (&0 - a))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)) %%
                         matrix_inv(p2bw_cmet atlas c0 (&0) g w))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)))
                    (p2bw_cscal atlas c0 (&0) g)
                    (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                          (&0) p)) /\
                  p2bw_t2 (p2bw_cdom c0 (&0 - a))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)) %%
                         matrix_inv(p2bw_cmet atlas c0 (&0) g w))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)))
                    (p2bw_cscal atlas c0 (&0) g)
                    (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                          (&0) p)) /\
                  p2bw_tid (p2bw_cdom c0 (&0 - a))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)) %%
                         matrix_inv(p2bw_cmet atlas c0 (&0) g w))
                    (\w. sqrt(det(p2bw_cmet atlas c0 (&0) g w)))
                    (p2bw_cscal atlas c0 (&0) g)
                    (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g)
                                          (&0) p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W3") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `c0:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) a (&0) (g:real->A->real^3^3)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2AF_CBFLOW_3] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:3)`] P2B_FLOW_CHART) THEN
  REWRITE_TAC[P2B_FLOW_CHART_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `a:real`; `&0`; `g:real->A->real^3^3`;
                             `c0:(A->bool)#(A->real^3)`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN STRIP_TAC THEN
  USE_THEN "W3" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `a:real`; `&0`; `g:real->A->real^3^3`; `p:A`;
                                 `c0:(A->bool)#(A->real^3)`] o
                 REWRITE_RULE[P2B_REQ_P2A_WEAK_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM P2A_FLOW_VIEW_3; P2BX_CA_FORM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
      is_comb(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th))) THEN
    REWRITE_TAC[o_DEF];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Regularity of the moved data and the members near each point of a box.    *)
(* ========================================================================= *)

(* Continuity on an open set is local. *)

let P2BX_CONT_LOCAL = prove
 (`!(f:real^M->real^N) s.
     open s /\ (!z. z IN s ==> ?N. open N /\ z IN N /\ f continuous_on N)
     ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `N:real^M->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[]);;

(* Transposition is continuous. *)

let P2BX_CONT_TRANSP = prove
 (`!(A:real^M->real^N^N) s.
     (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (A z)) continuous_on s
     ==> (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (transp(A z))) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE; TRANSP_COMPONENT] THEN MESON_TAC[]);;

(* The data moved along Phi are continuous, and the moved metric is a       *)
(* metric.                                                                    *)

let P2BX_WTR_REG = prove
 (`!(U:real^N->bool) V H H' lam (om0:real^(N,1)finite_sum->bool) G0 R0 l0 N0 G R l.
     p2bx_wtr U V H H' lam om0 G0 R0 l0 N0 G R l
     ==> (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (G z)) continuous_on N0 /\
         (!z. z IN N0 ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
         (\z. lift(R z)) continuous_on N0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_wtr] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `H:real^N->real^N`; `H':real^N->real^N`;
                 `lam:real`] P2BX_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  UNDISCH_TAC `diffeomorphism_on (U:real^N->bool) V (H:real^N->real^N) H'` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `P = \z:real^(N,1)finite_sum. pastecart ((H:real^N->real^N)(fstcart z))
                                                     (lift(lam * drop(sndcart z)))` THEN
  ABBREV_TAC `J = \z:real^(N,1)finite_sum. matrix(frechet_derivative (H:real^N->real^N)
                                                    (at (fstcart z)))` THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum. z IN N0
                  ==> fstcart z IN U /\
                      (P:real^(N,1)finite_sum->real^(N,1)finite_sum) z IN om0 /\
                      (G:real^(N,1)finite_sum->real^N^N) z =
                      inv lam %% (transp((J:real^(N,1)finite_sum->real^N^N) z) **
                                  (G0:real^(N,1)finite_sum->real^N^N)(P z) ** J z) /\
                      (R:real^(N,1)finite_sum->real) z = lam * R0(P z)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "J"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) continuous_on N0` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^(N,1)finite_sum | fstcart z IN U}` THEN CONJ_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (P:real^(N,1)finite_sum->real^(N,1)finite_sum) N0 SUBSET om0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((J:real^(N,1)finite_sum->real^N^N) z)) continuous_on N0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N`] LRG_SMOOTH_JACOBIAN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(\z. (vectorize:real^N^N->real^(N,N)finite_prod) ((J:real^(N,1)finite_sum->real^N^N) z)) =
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\x. matrix(frechet_derivative (H:real^N->real^N) (at x)))) o fstcart`
    SUBST1_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((G0:real^(N,1)finite_sum->real^N^N)
                      ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))) continuous_on N0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((G0:real^(N,1)finite_sum->real^N^N) ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))) =
      (\w. (vectorize:real^N^N->real^(N,N)finite_prod) (G0 w)) o P`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `om0:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (inv lam %% (transp((J:real^(N,1)finite_sum->real^N^N) z) **
                                 (G0:real^(N,1)finite_sum->real^N^N)
                                  ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) ** J z))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["P"; "J"] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTORIZE_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MP_TAC(ISPECL [`\z. transp((J:real^(N,1)finite_sum->real^N^N) z)`;
                   `\z. (G0:real^(N,1)finite_sum->real^N^N)
                          ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z) **
                        (J:real^(N,1)finite_sum->real^N^N) z`;
                   `N0:real^(N,1)finite_sum->bool`] CONTINUOUS_ON_MATRIX_MUL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_CONT_TRANSP THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\z. (G0:real^(N,1)finite_sum->real^N^N)
                            ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z)`;
                     `J:real^(N,1)finite_sum->real^N^N`;
                     `N0:real^(N,1)finite_sum->bool`] CONTINUOUS_ON_MATRIX_MUL) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `J:real^(N,1)finite_sum->real^N^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(P:real^(N,1)finite_sum->real^(N,1)finite_sum) z` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `G0:real^(N,1)finite_sum->real^N^N`)) (concl th) &&
      can (find_term ((=) `om0:real^(N,1)finite_sum->bool`)) (concl th) &&
      not (can (find_term ((=) `N0:real^(N,1)finite_sum->bool`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "transp")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    SUBGOAL_THEN `invertible((J:real^(N,1)finite_sum->real^N^N) z)` ASSUME_TAC THENL
     [EXPAND_TAC "J" THEN MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `U:real^N->bool`; `H':real^N->real^N`] THEN
      ASM_REWRITE_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; GSYM MATRIX_VECTOR_MUL_ASSOC;
                DOT_MATRIX_TRANSP_RMUL] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(v:real^N = vec 0)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INVERTIBLE_LEFT_INVERSE]) THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real^N^N`) THEN
    SUBGOAL_THEN `(B:real^N^N) ** ((J:real^(N,1)finite_sum->real^N^N) z ** v) = vec 0` MP_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z. lift(lam * (R0:real^(N,1)finite_sum->real)
                                  ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["P"; "J"] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    SUBGOAL_THEN `(\z. lift((R0:real^(N,1)finite_sum->real)
                              ((P:real^(N,1)finite_sum->real^(N,1)finite_sum) z))) =
                  (\w. lift(R0 w)) o P` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `om0:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* Near each point of an open set read through phi_k in a chart c of the    *)
(* limit, the member data (metric G, scalar curvature R, reduced distance  *)
(* l, in backward time scaled by lam) are regular and satisfy the three     *)
(* weak forms of W3.                                                         *)

let P2BX_MEMBER_LOCAL = prove
 (`!(u:A->bool) kappa (top:A topology) atlas (g:real->A->real^3^3) p
    (top':B topology) atlas' W (f:B->A) f' (c:(B->bool)#(B->real^3)) lam a
    (om:real^(3,1)finite_sum->bool) G R l z0.
     P2B_REQ_P2A_WEAK_STATEMENT u /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top' atlas' W top atlas (IMAGE f W) f f' /\ c IN atlas' /\
     &0 < lam /\ a < &0 /\ open om /\
     (!z. z IN om ==> fstcart z IN IMAGE (SND c) (FST c INTER W) /\ &0 < drop(sndcart z) /\
                      lam * drop(sndcart z) < --a) /\
     G = (\z. inv lam %% rfs_pullback atlas (f o chart_inv c)
                           (g(--(lam * drop(sndcart z)))) (fstcart z)) /\
     R = (\z. lam * mfd_scalar atlas (g(--(lam * drop(sndcart z))))
                               (f(chart_inv c (fstcart z)))) /\
     l = (\z. p2b_klx (top,atlas) g p (lam * drop(sndcart z)) (f(chart_inv c (fstcart z)))) /\
     z0 IN om
     ==> ?N0. open N0 /\ z0 IN N0 /\ N0 SUBSET om /\
              (\z. (vectorize:real^3^3->real^(3,3)finite_prod) (G z)) continuous_on N0 /\
              (!z. z IN N0 ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
              (\z. lift(R z)) continuous_on N0 /\
              p2bw_t1 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l /\
              p2bw_t2 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l /\
              p2bw_tid N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`; `a:real`]
                P2BX_W3_SOURCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `W:B->bool`;
                 `f:B->A`; `f':A->B`; `c:(B->bool)#(B->real^3)`; `lam:real`; `a:real`;
                 `om:real^(3,1)finite_sum->bool`; `z0:real^(3,1)finite_sum`] P2BX_MEMBER_WTR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `V:real^3->bool`
    (X_CHOOSE_THEN `H:real^3->real^3` (X_CHOOSE_THEN `H':real^3->real^3`
    (X_CHOOSE_THEN `c0:(A->bool)#(A->real^3)` (X_CHOOSE_THEN `N0:real^(3,1)finite_sum->bool`
      STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c0:(A->bool)#(A->real^3)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_t1")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `p2bx_wtr U V H H' lam (p2bw_cdom (c0:(A->bool)#(A->real^3)) (&0 - a))
      (p2bw_cmet atlas c0 (&0) (g:real->A->real^3^3)) (p2bw_cscal atlas c0 (&0) g)
      (p2bw_cfun c0 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) (p:A)))
      N0 (G:real^(3,1)finite_sum->real^3^3) R l`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `N0:real^(3,1)finite_sum->bool` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_WTR_REG) THEN
  SUBGOAL_THEN `open(N0:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bx_wtr]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC P2BX_T1_TRANSFER; MATCH_MP_TAC P2BX_T2_TRANSFER;
    MATCH_MP_TAC P2BX_TID_TRANSFER] THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^3->bool`; `V:real^3->bool`; `H:real^3->real^3`; `H':real^3->real^3`; `lam:real`;
    `p2bw_cdom (c0:(A->bool)#(A->real^3)) (&0 - a)`; `p2bw_cmet atlas (c0:(A->bool)#(A->real^3)) (&0) g`;
    `p2bw_cscal atlas (c0:(A->bool)#(A->real^3)) (&0) g`;
    `p2bw_cfun (c0:(A->bool)#(A->real^3))
       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) (g:real->A->real^3^3)) (&0) (p:A))`] THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* The member data on a whole open set read through phi_k: regularity and    *)
(* the three weak forms (gluing of the local statements of P2BX_MEMBER_LOCAL *)
(* with P2BX_T1_GLUE, P2BX_T2_GLUE, P2BX_TID_GLUE).                          *)
(* ========================================================================= *)

let P2BX_MEMBER_BOX = prove
 (`!(u:A->bool) kappa (top:A topology) atlas (g:real->A->real^3^3) p
    (top':B topology) atlas' W (f:B->A) f' (c:(B->bool)#(B->real^3)) lam a
    (om:real^(3,1)finite_sum->bool) G R l.
     P2B_REQ_P2A_WEAK_STATEMENT u /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top' atlas' W top atlas (IMAGE f W) f f' /\ c IN atlas' /\
     &0 < lam /\ a < &0 /\ open om /\
     (!z. z IN om ==> fstcart z IN IMAGE (SND c) (FST c INTER W) /\ &0 < drop(sndcart z) /\
                      lam * drop(sndcart z) < --a) /\
     G = (\z. inv lam %% rfs_pullback atlas (f o chart_inv c)
                           (g(--(lam * drop(sndcart z)))) (fstcart z)) /\
     R = (\z. lam * mfd_scalar atlas (g(--(lam * drop(sndcart z))))
                               (f(chart_inv c (fstcart z)))) /\
     l = (\z. p2b_klx (top,atlas) g p (lam * drop(sndcart z)) (f(chart_inv c (fstcart z))))
     ==> (\z. (vectorize:real^3^3->real^(3,3)finite_prod) (G z)) continuous_on om /\
         (!z. z IN om ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
         (\z. lift(R z)) continuous_on om /\
         (wan_loclip om l
          ==> p2bw_t1 om (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l /\
              p2bw_t2 om (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l) /\
         p2bw_tid om (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z0. z0 IN om
         ==> ?N0. open N0 /\ z0 IN N0 /\ N0 SUBSET om /\
              (\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                     ((G:real^(3,1)finite_sum->real^3^3) z)) continuous_on N0 /\
              (!z. z IN N0 ==> transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
              (\z. lift((R:real^(3,1)finite_sum->real) z)) continuous_on N0 /\
              p2bw_t1 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l /\
              p2bw_t2 N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l /\
              p2bw_tid N0 (\z. sqrt(det(G z)) %% matrix_inv(G z)) (\z. sqrt(det(G z))) R l`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `z0:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `W:B->bool`;
                   `f:B->A`; `f':A->B`; `c:(B->bool)#(B->real^3)`; `lam:real`; `a:real`;
                   `om:real^(3,1)finite_sum->bool`; `G:real^(3,1)finite_sum->real^3^3`;
                   `R:real^(3,1)finite_sum->real`; `l:real^(3,1)finite_sum->real`;
                   `z0:real^(3,1)finite_sum`] P2BX_MEMBER_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
                        is_eq(concl th) && lhs(concl th) = v)))
   [`G:real^(3,1)finite_sum->real^3^3`; `R:real^(3,1)finite_sum->real`;
    `l:real^(3,1)finite_sum->real`] THEN
  SUBGOAL_THEN `(\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                       ((G:real^(3,1)finite_sum->real^3^3) z)) continuous_on om`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_CONT_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN om ==> transp((G:real^(3,1)finite_sum->real^3^3) z) = G z /\
                                !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:real^(3,1)finite_sum->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "transp")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((R:real^(3,1)finite_sum->real) z)) continuous_on om` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_CONT_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(3,1)finite_sum->bool`; `G:real^(3,1)finite_sum->real^3^3`]
                P2BW_COEFF_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE]) THEN
  SUBGOAL_THEN `!z. z IN om ==> &0 < drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_T1_GLUE; MATCH_MP_TAC P2BX_T2_GLUE] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    MATCH_MP_TAC P2BX_TID_GLUE THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

