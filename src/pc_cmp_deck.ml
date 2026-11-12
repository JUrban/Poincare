(* ========================================================================= *)
(* Unit pc_cmp_deck (comparison-geometry layer CMP, second unit of           *)
(* CMP_T2_CGT): deck maps of the exp_x pullback.  A deck map on an open W is *)
(* a smooth map sigma of the pullback ball with Psi o sigma = Psi on W (Psi  *)
(* = exp_x o E).  Deck maps are local isometries of the pullback metric,     *)
(* compose, and are determined by one value (rigidity).  For p with Psi p =  *)
(* x the map tau_p = exp^G_p o L_p (L_p = dPsi_p^-1 E) is a deck map with    *)
(* tau_p 0 = p and |tau_p w| <= |p| + |w|; if Psi is not injective on B(0,i) *)
(* there is a deck point x1 <> 0 with |x1| < 2 i (lift of the broken loop).  *)
(* ========================================================================= *)

needs "src/pc_cmp_pmfd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Deck maps; they are local isometries, compose, and are determined by one  *)
(* value.                                                                    *)
(* ========================================================================= *)

let cmp_deck = new_definition
 `cmp_deck (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
           (x:A) (E:real^N^N) (rho:real) (W:real^N->bool) (sigma:real^N->real^N) <=>
    open W /\ W SUBSET ball(vec 0,rho) /\ smooth_map_on W sigma /\
    !w. w IN W ==> sigma w IN ball(vec 0,rho) /\
                   cmp_psi (top,atlas) g x E (sigma w) = cmp_psi (top,atlas) g x E w`;;

let CMPK_DEXP_INVERTIBLE = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w.
        cmp_pullsetup (top,atlas) g x E K rho /\ norm w < rho
        ==> invertible(cmp_dexp (top,atlas) g x E w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
  X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `h:real^N`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `inv(&2)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w ** h = vec 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[cmp_expmetric; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RZERO; GSYM DOT_EQ_0] THEN MP_TAC(ISPEC `h:real^N` DOT_POS_LE) THEN
  REAL_ARITH_TAC);;

let CMPK_PM_DIFF2 = prove
 (`!U V (f:real^N->real^N) v.
        open U /\ v IN U /\ f v IN V
        ==> mfd_differential (open_set_atlas U) (open_set_atlas V) f v =
            frechet_derivative f (at v)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPW_PM_DIFF; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[ETA_AX]);;

(* The derivative of a deck map is a deck for dPsi. *)

let CMPK_DECK_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma a.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\ a IN W
        ==> (sigma has_derivative frechet_derivative sigma (at a)) (at a) /\
            !h. cmp_dexp (top,atlas) g x E (sigma a) ** frechet_derivative sigma (at a) h =
                cmp_dexp (top,atlas) g x E a ** h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_deck] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  SUBGOAL_THEN `(sigma:real^N->real^N) differentiable at a` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  SUBGOAL_THEN `(a:real^N) IN ball(vec 0,rho) /\ (sigma:real^N->real^N) a IN ball(vec 0,rho)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) ((sigma:real^N->real^N) a) =
    cmp_psi (top,atlas) g x E a`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `(sigma:real^N->real^N) a`]
    CMPW_PSI_HAS_DERIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `a:real^N`]
    CMPW_PSI_HAS_DERIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                (cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) a))
             (cmp_psi (top,atlas) g x E y)) has_derivative
     (\h. cmp_dexp (top,atlas) g x E ((sigma:real^N->real^N) a) **
          frechet_derivative sigma (at a) h)) (at a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                       (cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) a))
                    (cmp_psi (top,atlas) g x E y)) o (sigma:real^N->real^N)` THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_SIMP_TAC[o_THM] THEN
    SUBGOAL_THEN
     `(\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) ((sigma:real^N->real^N) a) **
           frechet_derivative sigma (at a) h) =
      (\h. cmp_dexp (top,atlas) g x E (sigma a) ** h) o frechet_derivative sigma (at a)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    UNDISCH_TAC
     `((\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                 (cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                    ((sigma:real^N->real^N) a)))
              (cmp_psi (top,atlas) g x E y)) has_derivative
       (\h. cmp_dexp (top,atlas) g x E (sigma a) ** h)) (at (sigma a))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
              (cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) a))
           (cmp_psi (top,atlas) g x E y)`;
    `\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) ((sigma:real^N->real^N) a) **
         frechet_derivative sigma (at a) h`;
    `\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) a ** h`;
    `a:real^N`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN
  REWRITE_TAC[]);;

(* The metric identity for deck maps. *)

let CMPK_DECK_METRIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma a.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\ a IN W
        ==> cmp_expmetric (top,atlas) g x E a =
            transp(matrix(frechet_derivative sigma (at a))) **
            cmp_expmetric (top,atlas) g x E (sigma a) **
            matrix(frechet_derivative sigma (at a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `a:real^N`] CMPK_DECK_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (sigma:real^N->real^N) (at a))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) ((sigma:real^N->real^N) a) =
    cmp_psi (top,atlas) g x E a`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmp_deck]; ALL_TAC] THEN
  MATCH_MP_TAC CMPP_MATRIX_EQ_DOT THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  REWRITE_TAC[cmp_expmetric; GSYM MATRIX_VECTOR_MUL_ASSOC; CMPP_DOT_TRANSP] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[cmp_psi]) THEN ASM_REWRITE_TAC[]);;

let CMPK_DECK_LISOM = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma
        ==> mfd_local_isometry (subtopology euclidean (ball(vec 0,rho)),
                                open_set_atlas (ball(vec 0,rho)))
              (cmp_expmetric (top,atlas) g x E)
              (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
              (cmp_expmetric (top,atlas) g x E) W sigma`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_deck]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SUBGOAL_THEN `ball(vec 0:real^N,rho) INTER W = W` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN ASM SET_TAC[];
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N) IN ball(vec 0,rho) /\ (sigma:real^N->real^N) a IN ball(vec 0,rho)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CMPK_PM_DIFF2; OPEN_BALL] THEN
    MATCH_MP_TAC CMPK_DECK_METRIC THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`; `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let CMPK_DECK_COMPOSE = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho W1 W2 s1 s2.
        cmp_deck (top,atlas) g x E rho W1 s1 /\ cmp_deck (top,atlas) g x E rho W2 s2 /\
        IMAGE s1 W1 SUBSET W2
        ==> cmp_deck (top,atlas) g x E rho W1 (s2 o s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_deck] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s1:real^N->real^N) w IN W2` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]]]);;

let CMPK_DECK_ID = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho W.
        open W /\ W SUBSET ball(vec 0,rho)
        ==> cmp_deck (top,atlas) g x E rho W (\w. w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_deck; SMOOTH_MAP_ON_ID] THEN ASM SET_TAC[]);;

(* Rigidity: deck maps agreeing at a point of a connected W agree on W. *)

let CMPK_DECK_RIGID = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W s1 s2 a.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W s1 /\ cmp_deck (top,atlas) g x E rho W s2 /\
        connected W /\ a IN W /\ s1 a = s2 a
        ==> !w. w IN W ==> s1 w = s2 w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `W SUBSET ball(vec 0:real^N,rho) /\ (a:real^N) IN ball(vec 0,rho) /\
                (s1:real^N->real^N) a IN ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cmp_deck; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `W:real^N->bool`; `s1:real^N->real^N`; `s2:real^N->real^N`; `a:real^N`]
    MFD_LOCAL_ISOMETRY_RIGID) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPK_DECK_LISOM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPK_DECK_LISOM THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2:real^N->real^N) a IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMPK_PM_DIFF2; OPEN_BALL] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `s1:real^N->real^N`; `a:real^N`] CMPK_DECK_DERIV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `s2:real^N->real^N`; `a:real^N`] CMPK_DECK_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `h:real^N` o CONJUNCT2) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `h:real^N` o CONJUNCT2) THEN
                       REWRITE_TAC[GSYM th]) THEN
  DISCH_THEN(MP_TAC o AP_TERM
    `\z:real^N. matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                             ((s2:real^N->real^N) a)) ** z`) THEN
  SUBGOAL_THEN `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                             ((s2:real^N->real^N) a))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPK_DEXP_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[GSYM IN_BALL_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

(* ========================================================================= *)
(* The deck map tau_p = exp^G_p o L_p at a deck point p (Psi p = x), L_p =   *)
(* dPsi_p^-1 E: a deck map on B(0, R - |p|) with tau_p 0 = p and |tau_p w|   *)
(* <= |p| + |w|.                                                             *)
(* ========================================================================= *)

let cmp_tau = new_definition
 `cmp_tau (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
          (x:A) (E:real^N^N) (rho:real) (p:real^N) (w:real^N) =
    mfd_exp (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
            (cmp_expmetric (top,atlas) g x E) p
            ((matrix_inv(cmp_dexp (top,atlas) g x E p) ** E) ** w)`;;

(* The pullback metric at a point as the pullback of g by dPsi. *)

let CMPK_EXPMETRIC_QUAD = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w a.
        a dot (cmp_expmetric (top,atlas) g x E w ** a) =
        (cmp_dexp (top,atlas) g x E w ** a) dot
        (g(cmp_psi (top,atlas) g x E w) ** (cmp_dexp (top,atlas) g x E w ** a))`,
  REWRITE_TAC[cmp_expmetric; cmp_psi; GSYM MATRIX_VECTOR_MUL_ASSOC; CMPP_DOT_TRANSP]);;

(* L_p is an isometry from (T_0, I) to (T_p, G(p)). *)

let CMPK_LP_ISOMETRY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho p w.
        cmp_pullsetup (top,atlas) g x E K rho /\ norm p < rho /\
        cmp_psi (top,atlas) g x E p = x
        ==> cmp_dexp (top,atlas) g x E p **
            ((matrix_inv(cmp_dexp (top,atlas) g x E p) ** E) ** w) = E ** w /\
            mfd_tnorm (cmp_expmetric (top,atlas) g x E) p
              ((matrix_inv(cmp_dexp (top,atlas) g x E p) ** E) ** w) = norm w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPK_DEXP_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID];
    DISCH_TAC] THEN
  REWRITE_TAC[mfd_tnorm; CMPK_EXPMETRIC_QUAD] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  ASM_SIMP_TAC[GSYM mfd_tnorm; CMPP_TNORM_FRAME]);;

let CMPK_TAU = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R p.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm p < R /\
        cmp_psi (top,atlas) g x E p = x
        ==> cmp_deck (top,atlas) g x E rho (ball(vec 0,R - norm p))
                     (cmp_tau (top,atlas) g x E rho p) /\
            cmp_tau (top,atlas) g x E rho p (vec 0) = p /\
            (!w. norm w < R - norm p
                 ==> norm(cmp_tau (top,atlas) g x E rho p w) <= norm p + norm w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `norm(p:real^N) < rho /\ (p:real^N) IN ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) p) ** E` THEN
  SUBGOAL_THEN `!w. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) p **
                     ((L:real^N^N) ** w) = E ** w /\
                     mfd_tnorm (cmp_expmetric (top,atlas) g x E) p (L ** w) = norm w`
  (LABEL_TAC "L") THENL
   [GEN_TAC THEN EXPAND_TAC "L" THEN MATCH_MP_TAC CMPK_LP_ISOMETRY THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,R) SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. norm w < R - norm(p:real^N)
        ==> (L:real^N^N) ** w IN
            mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                        (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) p /\
            !t. &0 <= t /\ t <= &1
                ==> mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                             open_set_atlas (ball(vec 0,rho)))
                      (cmp_expmetric (top,atlas) g x E) p (t % (L ** w)) IN ball(vec 0,rho) /\
                    norm(mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                                  open_set_atlas (ball(vec 0,rho)))
                           (cmp_expmetric (top,atlas) g x E) p (t % (L ** w))) <=
                    norm p + t * norm w`
  (LABEL_TAC "dom") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
                   `R:real`; `p:real^N`; `(L:real^N^N) ** w`] CMPW_EXP_DOM) THEN
    USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[IN_BALL_0]; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_tau (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho p =
    (\w. mfd_exp (subtopology euclidean (ball(vec 0:real^N,rho)),
                  open_set_atlas (ball(vec 0,rho)))
           (cmp_expmetric (top,atlas) g x E) p ((L:real^N^N) ** w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmp_tau] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`; `p:real^N`]
      MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "dom" (fun th -> MP_TAC(MATCH_MP (SPEC `w:real^N` th)
      (ASSUME `norm(w:real^N) < R - norm(p:real^N)`))) THEN
    DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
    REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL; REAL_MUL_LID] THEN SIMP_TAC[]] THEN
  REWRITE_TAC[cmp_deck; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    MP_TAC(ISPEC `p:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`; `p:real^N`]
      MFD_EXP_SMOOTH) THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`; `p:real^N`]
      MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; INTER_UNIV] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. mfd_exp (subtopology euclidean (ball(vec 0:real^N,rho)),
                    open_set_atlas (ball(vec 0,rho)))
             (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) p
             ((L:real^N^N) ** w)) =
      mfd_exp (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
              (cmp_expmetric (top,atlas) g x E) p o (\w. L ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{v | v IN mfd_exp_dom (subtopology euclidean (ball(vec 0:real^N,rho)),
                                     open_set_atlas (ball(vec 0,rho)))
                       (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) p /\
                     mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                              open_set_atlas (ball(vec 0,rho)))
                       (cmp_expmetric (top,atlas) g x E) p v IN ball(vec 0,rho)}` THEN
    ASM_SIMP_TAC[OPEN_BALL; CMPW_LINEAR_SMOOTH] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `{v | v IN mfd_exp_dom (subtopology euclidean (ball(vec 0:real^N,rho)),
                               open_set_atlas (ball(vec 0,rho)))
                 (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) p /\
               mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                        open_set_atlas (ball(vec 0,rho)))
                 (cmp_expmetric (top,atlas) g x E) p v IN ball(vec 0,rho)} =
        mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                    (cmp_expmetric (top,atlas) g x E) p`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
      EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                     `open_set_atlas (ball(vec 0:real^N,rho))`;
                     `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`; `p:real^N`;
                     `v:real^N`] CMPP_EXP_IN_TOPSPACE) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      USE_THEN "dom" (fun th -> MP_TAC(MATCH_MP (SPEC `w:real^N` th)
      (ASSUME `norm(w:real^N) < R - norm(p:real^N)`))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `&1`)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL; IN_BALL_0] THEN
      SIMP_TAC[]];
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    USE_THEN "dom" (fun th -> MP_TAC(MATCH_MP (SPEC `w:real^N` th)
      (ASSUME `norm(w:real^N) < R - norm(p:real^N)`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seg")) THEN
    USE_THEN "seg" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[IN_BALL_0] o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
      `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
      `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `ball(vec 0:real^N,rho)`; `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
      `p:real^N`; `(L:real^N^N) ** w`] MFD_LOCAL_ISOMETRY_EXP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `ball(vec 0:real^N,rho)`;
                   `p:real^N`] CMPW_PSI_DIFF) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[cmp_psi]]);;

(* ========================================================================= *)
(* A deck point from non-injectivity.  If Psi w1 = Psi w2 with w1 <> w2      *)
(* small, the G-geodesic from w1 with velocity dPsi_w1^-1 dPsi_w2 (-w2)      *)
(* lifts the return path of the broken loop; its endpoint q is a deck point, *)
(* q <> 0 (else uniqueness of geodesics at time 1 gives w1 = w2), and |q| <  *)
(* |w1| + |w2|.                                                              *)
(* ========================================================================= *)

(* Velocities of geodesics agreeing near a time agree. *)

let CMPK_VEL_LOCAL = prove
 (`!top atlas (g:A->real^N^N) gamma1 gamma2 J1 J2 t d.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma1 J1 /\ mfd_geodesic (top,atlas) g gamma2 J2 /\
        &0 < d /\ (!s. abs(s - t) < d ==> s IN J1 /\ s IN J2 /\ gamma1 s = gamma2 s)
        ==> mfd_vel atlas gamma1 t = mfd_vel atlas gamma2 t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real) IN J1 /\ t IN J2 /\ (gamma1:real->A) t = gamma2 t`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma1:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t))`;
                 `(gamma1:real->A) t`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  MATCH_MP_TAC GEOL_CHART_VEL_LOCAL_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`gamma1:real->A`; `gamma2:real->A`;
    `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t))`;
    `t:real`; `d:real`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma1:real->A`; `J1:real->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t)`;
                   `t:real`] MFD_GEODESIC_VEL_CHART) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma2:real->A`; `J2:real->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t)`;
                   `t:real`] MFD_GEODESIC_VEL_CHART) THEN
    ASM_REWRITE_TAC[]]);;

(* The geodesic from w with velocity -w reaches 0 at time 1. *)

let CMPK_RADIAL_BACK = prove
 (`!(G:real^N->real^N^N) rho w.
        metric_field (ball(vec 0,rho)) G /\
        (!z. z IN ball(vec 0,rho) ==> G z ** z = z) /\ norm w < rho
        ==> --w IN mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),
                                open_set_atlas (ball(vec 0,rho))) G w /\
            mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                     open_set_atlas (ball(vec 0,rho))) G w (--w) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(ball(vec 0:real^N,rho)) /\ vec 0 IN ball(vec 0:real^N,rho) /\
                (w:real^N) IN ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_0] THEN
    MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (ball(vec 0:real^N,rho))) G`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[VECTOR_NEG_0] THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `vec 0:real^N`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `J0 = real_interval(--(rho / norm(w:real^N)),rho / norm w)` THEN
  SUBGOAL_THEN `is_realinterval (J0:real->bool) /\ real_open J0 /\
                (!s. s IN J0 ==> s % (w:real^N) IN ball(vec 0,rho)) /\
                &0 IN J0 /\ &1 IN J0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J0" THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
                IN_BALL_0; NORM_MUL] THEN
    SUBGOAL_THEN `&1 < rho / norm(w:real^N)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs s < rho / norm(w:real^N)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `w:real^N`; `J0:real->bool`]
    CMPW_RADIAL_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `\s. s % (w:real^N)`; `J0:real->bool`; `--(&1)`; `&1`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN J0 ==> mfd_vel (open_set_atlas (ball(vec 0,rho))) (\s. s % (w:real^N)) s = w`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s % (w:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[mfd_vel; RFB_OPEN_SET_CHART_AT] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `\t. (\s. s % (w:real^N)) (--(&1) * t + &1)`;
                 `{t | --(&1) * t + &1 IN J0}`; `w:real^N`; `--w:real^N`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; VECTOR_MUL_LID] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `--(&1)`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `&1` o REWRITE_RULE[SUBSET])
                             (MP_TAC o SPEC `&1`)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_exp_dom; mfd_exp; IN_ELIM_THM]);;

(* The lift of the return path cannot close up: if both geodesics end at 0  *)
(* then w1 = w2 (uniqueness of geodesics in M at time 0, then in the        *)
(* pullback at time 1).                                                      *)

let CMPK_LOOP_NONZERO = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w1 w2 v1.
        cmp_pullsetup (top,atlas) g x E K rho /\ norm w1 < rho /\ norm w2 < rho /\
        cmp_psi (top,atlas) g x E w1 = cmp_psi (top,atlas) g x E w2 /\
        v1 IN mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),
                           open_set_atlas (ball(vec 0,rho)))
                          (cmp_expmetric (top,atlas) g x E) w1 /\
        --w2 IN mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),
                             open_set_atlas (ball(vec 0,rho)))
                            (cmp_expmetric (top,atlas) g x E) w2 /\
        cmp_dexp (top,atlas) g x E w1 ** v1 = cmp_dexp (top,atlas) g x E w2 ** --w2 /\
        mfd_exp (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                (cmp_expmetric (top,atlas) g x E) w1 v1 = vec 0 /\
        mfd_exp (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                (cmp_expmetric (top,atlas) g x E) w2 (--w2) = vec 0
        ==> w1 = w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w1:real^N) IN ball(vec 0,rho) /\ (w2:real^N) IN ball(vec 0,rho) /\
                vec 0 IN ball(vec 0:real^N,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)` THEN
  ABBREV_TAC `Psi = cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N)` THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `w1:real^N`; `v1:real^N`] MFD_GEO_MAXIMAL) THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `w2:real^N`; `--w2:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M1 = mfd_geo_maxint (subtopology euclidean (ball(vec 0:real^N,rho)),
                                   open_set_atlas (ball(vec 0:real^N,rho)))
                     (G:real^N->real^N^N) w1 v1` THEN
  ABBREV_TAC `M2 = mfd_geo_maxint (subtopology euclidean (ball(vec 0:real^N,rho)),
                                   open_set_atlas (ball(vec 0:real^N,rho)))
                     (G:real^N->real^N^N) w2 (--w2)` THEN
  ABBREV_TAC `b1 = mfd_geo (subtopology euclidean (ball(vec 0:real^N,rho)),
                            open_set_atlas (ball(vec 0:real^N,rho)))
                     (G:real^N->real^N^N) w1 v1` THEN
  ABBREV_TAC `b2 = mfd_geo (subtopology euclidean (ball(vec 0:real^N,rho)),
                            open_set_atlas (ball(vec 0:real^N,rho)))
                     (G:real^N->real^N^N) w2 (--w2)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN M1 /\ &1 IN M2 /\ (b1:real->real^N) (&1) = vec 0 /\
                (b2:real->real^N) (&1) = vec 0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M1"; "M2"; "b1"; "b2"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_exp_dom; mfd_exp; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!t. t IN M1 ==> (b1:real->real^N) t IN ball(vec 0,rho)) /\
                (!t. t IN M2 ==> (b2:real->real^N) t IN ball(vec 0,rho))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                     `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                     `b1:real->real^N`; `M1:real->bool`; `t:real`]
        GEOL_GEODESIC_IN_TOPSPACE);
      MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                     `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                     `b2:real->real^N`; `M2:real->bool`; `t:real`]
        GEOL_GEODESIC_IN_TOPSPACE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ball(vec 0:real^N,rho)
        ==> mfd_differential (open_set_atlas (ball(vec 0,rho))) atlas (Psi:real^N->A) w =
            (\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) w ** h)`
  (LABEL_TAC "dpsi") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Psi" THEN MATCH_MP_TAC CMPW_PSI_DIFF THEN
    ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `G:real^N->real^N^N`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `g:A->real^N^N`; `ball(vec 0:real^N,rho)`; `Psi:real^N->A`; `b1:real->real^N`;
    `M1:real->bool`] MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v1")) THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `G:real^N->real^N^N`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `g:A->real^N^N`; `ball(vec 0:real^N,rho)`; `Psi:real^N->A`; `b2:real->real^N`;
    `M2:real->bool`] MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v2")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(Psi:real^N->A) o (b1:real->real^N)`; `(Psi:real^N->A) o (b2:real->real^N)`;
                 `M1:real->bool`; `M2:real->bool`; `&0`] MFD_GEODESIC_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    USE_THEN "v1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&0 IN M1`)]) THEN
    USE_THEN "v2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&0 IN M2`)]) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "same")] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !s. abs(s - &1) < d ==> s IN M1 /\ s IN M2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open (M1:real->bool)` THEN UNDISCH_TAC `real_open (M2:real->bool)` THEN
    REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(Psi:real^N->A) o (b1:real->real^N)`; `(Psi:real^N->A) o (b2:real->real^N)`;
                 `M1:real->bool`; `M2:real->bool`; `&1`; `d:real`] CMPK_VEL_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real) IN M1 /\ s IN M2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "same" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  USE_THEN "v1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&1 IN M1`)]) THEN
  USE_THEN "v2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&1 IN M2`)]) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (open_set_atlas (ball(vec 0,rho))) (b1:real->real^N) (&1) =
    mfd_vel (open_set_atlas (ball(vec 0,rho))) (b2:real->real^N) (&1)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM
      `\z:real^N. matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) (vec 0)) ** z`) THEN
    SUBGOAL_THEN `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) (vec 0))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMPK_DEXP_INVERTIBLE THEN
      MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[NORM_0];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `b1:real->real^N`; `b2:real->real^N`; `M1:real->bool`; `M2:real->bool`;
                 `&1`] MFD_GEODESIC_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The broken-loop lift: a nonzero deck point of norm < 2 i. *)

let CMPK_LOOP = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R i w1 w2.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ &2 * i <= R /\
        norm w1 < i /\ norm w2 < i /\ ~(w1 = w2) /\
        cmp_psi (top,atlas) g x E w1 = cmp_psi (top,atlas) g x E w2
        ==> ?q. ~(q = vec 0) /\ norm q < &2 * i /\ cmp_psi (top,atlas) g x E q = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN ball(vec 0:real^N,rho)
                    ==> cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) z ** z = z`
  ASSUME_TAC THENL [REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w1:real^N) IN ball(vec 0,rho) /\ (w2:real^N) IN ball(vec 0,rho) /\
                norm(w1:real^N) < rho /\ norm(w2:real^N) < rho /\
                vec 0 IN ball(vec 0:real^N,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D1 = cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) w1` THEN
  ABBREV_TAC `D2 = cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) w2` THEN
  SUBGOAL_THEN `invertible(D1:real^N^N) /\ invertible(D2:real^N^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC CMPK_DEXP_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v1 = matrix_inv(D1:real^N^N) ** ((D2:real^N^N) ** --w2)` THEN
  SUBGOAL_THEN `(D1:real^N^N) ** v1 = (D2:real^N^N) ** --w2` ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
                 MATRIX_MUL_ASSOC; MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tnorm (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) w1 v1 = norm(w2:real^N)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tnorm; CMPK_EXPMETRIC_QUAD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((D2:real^N^N) ** --w2) dot
      ((g:A->real^N^N)(cmp_psi (top,atlas) g x (E:real^N^N) w2) ** (D2 ** --w2)) =
      (--w2) dot (cmp_expmetric (top,atlas) g x E w2 ** --w2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[CMPK_EXPMETRIC_QUAD]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
    ASM_SIMP_TAC[GSYM vector_norm];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,R) SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
                 `R:real`; `w1:real^N`; `v1:real^N`] CMPW_EXP_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seg1")) THEN
  ABBREV_TAC `q = mfd_exp (subtopology euclidean (ball(vec 0:real^N,rho)),
                           open_set_atlas (ball(vec 0,rho)))
                    (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) w1 v1` THEN
  EXISTS_TAC `q:real^N` THEN
  SUBGOAL_THEN `norm(q:real^N) < &2 * i` ASSUME_TAC THENL
   [USE_THEN "seg1" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`; `rho:real`;
                 `w2:real^N`] CMPK_RADIAL_BACK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> mfd_exp (subtopology euclidean (ball(vec 0:real^N,rho)),
                     open_set_atlas (ball(vec 0,rho)))
              (cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)) w2 (t % --w2) IN
            ball(vec 0,rho)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
                   `R:real`; `w2:real^N`; `--w2:real^N`] CMPW_EXP_DOM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[mfd_tnorm; MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
      ASM_SIMP_TAC[GSYM vector_norm] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `ball(vec 0:real^N,rho)`; `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `w1:real^N`; `v1:real^N`] MFD_LOCAL_ISOMETRY_EXP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "seg1" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `ball(vec 0:real^N,rho)`;
                 `w1:real^N`] CMPW_PSI_DIFF) THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (ball(vec 0:real^N,rho))`; `open_set_atlas (ball(vec 0:real^N,rho))`;
    `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `ball(vec 0:real^N,rho)`; `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
    `w2:real^N`; `--w2:real^N`] MFD_LOCAL_ISOMETRY_EXP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `ball(vec 0:real^N,rho)`;
                 `w2:real^N`] CMPW_PSI_DIFF) THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) q = x` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) (vec 0)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[cmp_psi; MATRIX_VECTOR_MUL_RZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(w1:real^N = w2)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPK_LOOP_NONZERO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                        `v1:real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

