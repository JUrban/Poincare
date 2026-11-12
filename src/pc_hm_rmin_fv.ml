(* ========================================================================= *)
(* The first variation of the G-energy (part of pc_hm_reg_min) along the     *)
(* projected variations closest_point S (w + e phi) for S-valued W^{1,2}     *)
(* maps w (no smoothness and no continuity needed), the localization of the  *)
(* energy to subsets, and: continuous S-valued energy minimizers are         *)
(* cm_wharmonic.                                                             *)
(* ========================================================================= *)

needs "src/pc_hm_reg_defs.ml";;
needs "src/pc_hm_reg_cov.ml";;
needs "src/pc_hm_dexist.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Euler-Lagrange density as a function of four vectors, the projected   *)
(* energy density, tube facts and the global smooth projection Pg of         *)
(* HMR_PI_GLOBAL in a usable form.                                           *)
(* ========================================================================= *)

(* hmrm_eld S G p q h k: the Euler-Lagrange density at the point p of S,   *)
(* with q the partial of the map, h the variation and k its partial; the   *)
(* density hmc_ld of pc_hm_convexity with the partial of the map given as  *)
(* an argument (classical for smooth maps, weak for W^{1,2} maps).          *)

let hmrm_eld = new_definition
 `hmrm_eld (S:real^K->bool) (G:real^K->real^K^K) (p:real^K) (q:real^K) (h:real^K)
           (k:real^K) =
    &2 * ((mderiv (\y. jacobian (closest_point S) (at y)) p h ** q +
           jacobian (closest_point S) (at p) ** k) dot (G p ** q)) +
    q dot (mderiv G p (jacobian (closest_point S) (at p) ** h) ** q)`;;

(* hmrm_q S G p q: the G-energy density of closest_point S along a map     *)
(* with value p and partial q (before the projection).                      *)

let hmrm_q = new_definition
 `hmrm_q (S:real^K->bool) (G:real^K->real^K^K) (p:real^K) (q:real^K) =
    (jacobian (closest_point S) (at p) ** q) dot
    (G(closest_point S p) ** (jacobian (closest_point S) (at p) ** q))`;;

let HMRM_ELD_HMC_LD = prove
 (`!S (G:real^K->real^K^K) (v:real^2->real^K) (phi:real^2->real^K) i x.
     hmc_ld S G v phi (\y. partial_derivative i phi y) i x =
     hmrm_eld S G (v x) (partial_derivative i v x) (phi x) (partial_derivative i phi x)`,
  REWRITE_TAC[hmc_ld; hmrm_eld]);;

let HMRM_TUBE_OPEN = prove
 (`!(S:real^K->bool) d. open(cm_tube S d)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `cm_tube (S:real^K->bool) d = UNIONS {ball(p,d) | p IN S}`
  SUBST1_TAC THENL
   [REWRITE_TAC[cm_tube; UNIONS_GSPEC; IN_BALL; EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[DIST_SYM];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL]]);;

let HMRM_TUBE_MONO = prove
 (`!(S:real^K->bool) d1 d. d1 <= d ==> cm_tube S d1 SUBSET cm_tube S d`,
  REWRITE_TAC[cm_tube; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

let HMRM_TUBE_NEAR = prove
 (`!(S:real^K->bool) d p q. p IN S /\ norm q < d ==> p + q IN cm_tube S d`,
  REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `p:real^K` THEN
  ASM_REWRITE_TAC[dist; VECTOR_ARITH `(p + q) - p:real^K = q`]);;

(* The global smooth projection: closest_point S on the d1-tube, with a    *)
(* uniformly bounded derivative there equal to the Jacobian of             *)
(* closest_point S.                                                          *)

let HMRM_PG = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?d1 B (Pg:real^K->real^K).
           &0 < d1 /\ d1 < d /\ &0 <= B /\
           continuously_differentiable 1 (:real^K) Pg /\
           (!y. onorm(frechet_derivative Pg (at y)) <= B) /\
           (!y v. norm(frechet_derivative Pg (at y) v) <= B * norm v) /\
           (!y z. norm(Pg y - Pg z) <= B * norm(y - z)) /\
           (!z. z IN cm_tube S d1
                ==> Pg z = closest_point S z /\ closest_point S z IN S /\
                    (!v. frechet_derivative Pg (at z) v =
                         jacobian (closest_point S) (at z) ** v)) /\
           (!z. z IN S ==> z IN cm_tube S d1 /\ Pg z = z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMR_PI_GLOBAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`d1:real`; `B:real`; `Pg:real^K->real^K`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^K) (Pg:real^K->real^K)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Pg:real^K->real^K) differentiable (at y)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. onorm(frechet_derivative (Pg:real^K->real^K) (at y)) <= B`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `frechet_derivative (Pg:real^K->real^K) (at y)` ONORM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Pg:real^K->real^K`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^K. z IN cm_tube S d1
               ==> !v. frechet_derivative Pg (at z) v =
                       jacobian (closest_point S) (at z) ** v`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `d1:real`] HMRM_TUBE_OPEN) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^K`) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(closest_point (S:real^K->bool) has_derivative frechet_derivative Pg (at z)) (at z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`Pg:real^K->real^K`; `r0:real`] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    SUBGOAL_THEN `linear(frechet_derivative (closest_point (S:real^K->bool)) (at z))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[jacobian; MATRIX_WORKS]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^K) IN cm_tube S d1` ASSUME_TAC THENL
   [REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `z:real^K` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSEST_POINT_SELF]);;

(* ========================================================================= *)
(* The energy of closest_point S (w + e phi) for a W^{1,2} map w (the        *)
(* W^{1,2} form of HMC_GEN_LINE): the chain rule through Pg identifies the   *)
(* weak partials almost everywhere.                                          *)
(* ========================================================================= *)

let HMRM_GEN_LINE = prove
 (`!S (G:real^K->real^K^K) d d1 B (Pg:real^K->real^K) s (w:real^2->real^K) phi e.
     cm_target S G d /\
     continuously_differentiable 1 (:real^K) Pg /\
     (!y. onorm(frechet_derivative Pg (at y)) <= B) /\
     (!z. z IN cm_tube S d1
          ==> Pg z = closest_point S z /\
              (!v. frechet_derivative Pg (at z) v = jacobian (closest_point S) (at z) ** v)) /\
     open s /\ bounded s /\ wan_w12 s w /\ wan_vtest s phi /\
     (!x. x IN s ==> w x + e % phi x IN cm_tube S d1)
     ==> wan_w12 s (\x. closest_point S (w x + e % phi x)) /\
         (!i. 1 <= i /\ i <= 2
              ==> negligible {x | x IN s /\
                     ~(wan_wd s i (\x. closest_point S (w x + e % phi x)) x =
                       jacobian (closest_point S) (at (w x + e % phi x)) **
                       (wan_wd s i w x + e % partial_derivative i phi x))}) /\
         (!i. 1 <= i /\ i <= 2
              ==> (\x. lift(hmrm_q S G (w x + e % phi x)
                              (wan_wd s i w x + e % partial_derivative i phi x)))
                  integrable_on s) /\
         cm_gen G s (\x. closest_point S (w x + e % phi x)) =
         sum(1..2) (\i. drop(integral s
              (\x. lift(hmrm_q S G (w x + e % phi x)
                          (wan_wd s i w x + e % partial_derivative i phi x))))) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `phi:real^2->real^K`] WAN_VTEST_W12) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (\x. (w:real^2->real^K) x + e % phi x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_ADD THEN ASM_SIMP_TAC[WAN_W12_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wpd s i (\x. (w:real^2->real^K) x + e % phi x)
              (\x. wan_wd s i w x + e % partial_derivative i phi x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
      ASM_SIMP_TAC[DIMINDEX_2; ETA_AX];
      MATCH_MP_TAC WAN_WPD_CMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\x. (w:real^2->real^K) x + e % phi x`;
                 `Pg:real^K->real^K`]
    (REWRITE_RULE[WAN_CHAIN_W12_STATEMENT]
      (ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_W12))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DIMINDEX_2] THEN BETA_TAC THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN s /\
                    ~(closest_point S ((w:real^2->real^K) x + e % phi x) =
                      Pg(w x + e % phi x))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_EQ_IMP_NULL THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\x. closest_point S ((w:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`;
                   `\x. closest_point S ((w:real^2->real^K) x + e % phi x)`;
                   `\x. (Pg:real^K->real^K)((w:real^2->real^K) x + e % phi x)`]
                  HMD_W12_AE_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> negligible {x | x IN s /\
               ~(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
                 jacobian (closest_point S) (at (w x + e % phi x)) **
                 (wan_wd s i w x + e % partial_derivative i phi x))}`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) =
      wan_wd s i (\x. (Pg:real^K->real^K)(w x + e % phi x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC HMD_WD_AE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`;
                   `\x. (Pg:real^K->real^K)((w:real^2->real^K) x + e % phi x)`;
                   `\x. frechet_derivative (Pg:real^K->real^K)
                          (at ((w:real^2->real^K) x + e % phi x))
                          (wan_wd s i (\x. w x + e % phi x) x)`] WAN_WD_UNIQUE) THEN
    ASM_SIMP_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x. (w:real^2->real^K) x + e % phi x`;
                   `\x. wan_wd s i (w:real^2->real^K) x + e % partial_derivative i phi x`]
                  WAN_WD_UNIQUE) THEN
    ASM_SIMP_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC
     `{x | x IN s /\
           ~(wan_wd s i (\x. (Pg:real^K->real^K)((w:real^2->real^K) x + e % phi x)) x =
             frechet_derivative Pg (at (w x + e % phi x))
               (wan_wd s i (\x. w x + e % phi x) x))} UNION
      {x | x IN s /\
           ~(wan_wd s i (\x. (w:real^2->real^K) x + e % phi x) x =
             wan_wd s i w x + e % partial_derivative i phi x)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN s` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^2->real^K) x + e % phi x IN cm_tube S d1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP HMD_TARGET_ELLIPTIC (ASSUME `cm_target S (G:real^K->real^K^K) d`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ell")))))) THEN
  SUBGOAL_THEN `!z xi. abs(xi dot ((G:real^K->real^K^K) z ** xi)) <= Lam * norm xi pow 2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^K`; `xi:real^K`] THEN
    USE_THEN "ell" (MP_TAC o SPECL [`z:real^K`; `xi:real^K`]) THEN
    SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x
                      dot (G(closest_point S (w x + e % phi x)) **
                           wan_wd s i (\x. closest_point S (w x + e % phi x)) x)))
            integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`;
                   `\x. closest_point S ((w:real^2->real^K) x + e % phi x)`;
                   `Lam:real`; `i:num`] HMD_GDIR_INTEGRABLE) THEN
    ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> !x. x IN s DIFF
                 {x | x IN s /\
                      ~(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
                        jacobian (closest_point S) (at (w x + e % phi x)) **
                        (wan_wd s i w x + e % partial_derivative i phi x))}
                ==> lift(hmrm_q S G (w x + e % phi x)
                           (wan_wd s i w x + e % partial_derivative i phi x)) =
                    lift(wan_wd s i (\x. closest_point S (w x + e % phi x)) x dot
                         (G(closest_point S (w x + e % phi x)) **
                          wan_wd s i (\x. closest_point S (w x + e % phi x)) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
      jacobian (closest_point S) (at (w x + e % phi x)) **
      (wan_wd s i w x + e % partial_derivative i phi x)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[hmrm_q];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC
     `\x. lift(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x
               dot (G(closest_point S (w x + e % phi x)) **
                    wan_wd s i (\x. closest_point S (w x + e % phi x)) x))` THEN
    EXISTS_TAC
     `{x | x IN s /\
           ~(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
             jacobian (closest_point S) (at (w x + e % phi x)) **
             (wan_wd s i w x + e % partial_derivative i phi x))}` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cm_gen; wan_gdir; DIMINDEX_2] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC
   `{x | x IN s /\
         ~(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
           jacobian (closest_point S) (at (w x + e % phi x)) **
           (wan_wd s i w x + e % partial_derivative i phi x))}` THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Weak partials of S-valued W^{1,2} maps are tangent almost everywhere, and *)
(* the first variation of the energy (the W^{1,2} form of                    *)
(* HMC_FIRST_VARIATION, with an L^1 majorant).                               *)
(* ========================================================================= *)

let HMRM_WD_TANGENT = prove
 (`!S (G:real^K->real^K^K) d s (w:real^2->real^K) i.
     cm_target S G d /\ open s /\ bounded s /\ wan_w12 s w /\
     (!x. x IN s ==> w x IN S) /\ 1 <= i /\ i <= 2
     ==> negligible {x | x IN s /\
                         ~(jacobian (closest_point S) (at (w x)) ** wan_wd s i w x =
                           wan_wd s i w x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMRM_PG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `s:real^2->bool`; `w:real^2->real^K`;
                 `\x:real^2. vec 0:real^K`; `&0`] HMRM_GEN_LINE) THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[wan_vtest; SMOOTH_MAP_ON_CONST] THEN
    EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `wan_wd s i (\x. closest_point S ((w:real^2->real^K) x)) = wan_wd s i w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HMD_WD_AE THEN MATCH_MP_TAC HMD_EQ_IMP_NULL THEN
    ASM_SIMP_TAC[CLOSEST_POINT_SELF];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The majorant of the e-derivative of the density, as a polynomial in the *)
(* norm of the weak partial.                                                 *)

let HMRM_FV_POLY = prove
 (`!c1 c2 c3 c4 N E Q.
     &2 * ((c1 * (N + E) + c2 * Q) * (c3 * (c2 * (N + E)))) +
     (c2 * (N + E)) * (c4 * (c2 * (N + E))) =
     (&2 * c1 * c3 * c2 + c2 * c2 * c4) * N pow 2 +
     (&2 * (&2 * c1 * c3 * c2 + c2 * c2 * c4) * E + &2 * c2 * Q * c3 * c2) * N +
     ((&2 * c1 * c3 * c2 + c2 * c2 * c4) * E pow 2 + &2 * c2 * Q * c3 * c2 * E)`,
  CONV_TAC REAL_RING);;

let HMRM_FV_MAJORANT_INTEGRABLE = prove
 (`!s (f:real^2->real^K) a b c.
     open s /\ bounded s /\ f IN lspace s (&2)
     ==> (\x. lift(a * norm(f x) pow 2 + b * norm(f x) + c)) integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measurable(s:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC INTEGRABLE_CMUL) THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
    MP_TAC(ISPECL [`f:real^2->real^K`; `s:real^2->bool`; `&1`] WAN_L2_L1_BOUND) THEN
    ASM_SIMP_TAC[REAL_LT_01];
    ASM_REWRITE_TAC[INTEGRABLE_ON_CONST]]);;

(* The pointwise bound of the e-derivative of the projected density (the    *)
(* expression of HMC_LINE_DERIV) by a quadratic polynomial in the norm of   *)
(* the weak partial pk, from bounds of the Jacobian of closest_point S and  *)
(* its derivative on a set T2, and of G and its derivative on S.            *)

let HMRM_FV_BOUND = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) T2 Mf M1 CJ0 CJ1 Lam1 CG
    (z:real^K) (h:real^K) (pk:real^K) (q:real^K) e e1 A B C.
     z IN T2 /\ closest_point S z IN S /\
     &0 <= Mf /\ &0 <= M1 /\ &0 <= CJ0 /\ &0 <= CJ1 /\ &0 <= Lam1 /\ &0 <= CG /\
     norm h <= Mf /\ norm q <= M1 /\ abs e <= e1 /\
     (!y. y IN T2
          ==> norm((vectorize:real^K^K->real^(K,K)finite_prod)
                   (jacobian (closest_point S) (at y))) <= CJ0) /\
     (!y a. y IN T2
            ==> norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                       (\y. jacobian (closest_point S) (at y))) (at y) a)
                <= CJ1 * norm a) /\
     (!y xi. y IN S ==> norm(G y ** xi) <= Lam1 * norm xi) /\
     (!y a xi. y IN S ==> norm(mderiv G y a ** xi) <= CG * norm a * norm xi) /\
     A = &2 * (CJ1 * Mf) * Lam1 * CJ0 + CJ0 * CJ0 * (CG * (CJ0 * Mf)) /\
     B = &2 * A * (e1 * M1) + &2 * CJ0 * M1 * Lam1 * CJ0 /\
     C = A * (e1 * M1) pow 2 + &2 * CJ0 * M1 * Lam1 * CJ0 * (e1 * M1)
     ==> abs(&2 * ((mderiv (\y. jacobian (closest_point S) (at y)) z h ** (pk + e % q) +
                    jacobian (closest_point S) (at z) ** q) dot
                   (G(closest_point S z) **
                    (jacobian (closest_point S) (at z) ** (pk + e % q)))) +
             (jacobian (closest_point S) (at z) ** (pk + e % q)) dot
             (mderiv G (closest_point S z) (jacobian (closest_point S) (at z) ** h) **
              (jacobian (closest_point S) (at z) ** (pk + e % q))))
         <= A * norm pk pow 2 + B * norm pk + C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= e1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(e:real)` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!xi. norm(jacobian (closest_point (S:real^K->bool)) (at z) ** xi) <= CJ0 * norm xi`
  ASSUME_TAC THENL
   [X_GEN_TAC `xi:real^K` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^K^K->real^(K,K)finite_prod)
                 (jacobian (closest_point (S:real^K->bool)) (at z))) * norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MAT_NORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * (((CJ1 * Mf) * (norm(pk:real^K) + e1 * M1) + CJ0 * M1) *
          (Lam1 * (CJ0 * (norm pk + e1 * M1)))) +
    (CJ0 * (norm pk + e1 * M1)) * ((CG * (CJ0 * Mf)) * (CJ0 * (norm pk + e1 * M1)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[HMRM_FV_POLY] THEN ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC HMC_FPRIME_BOUND THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_MUL];
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `xi:real^K` THEN REWRITE_TAC[mderiv] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `norm(frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
             (\y. jacobian (closest_point (S:real^K->bool)) (at y))) (at z) h) *
      norm(xi:real^K)` THEN
    REWRITE_TAC[HMC_MATRIFY_NORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CJ1 * norm(h:real^K)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    X_GEN_TAC `xi:real^K` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CG * norm(jacobian (closest_point (S:real^K->bool)) (at z) ** h) *
                norm(xi:real^K)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CJ0 * norm(h:real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(NORM_ARITH `norm(b:real^K) <= y ==> norm(a + b) <= norm a + y`) THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The first variation of the G-energy along closest_point S (w + e phi) for *)
(* an S-valued W^{1,2} map w on a bounded open set and a test map phi (no    *)
(* continuity of w needed).  This is the W^{1,2} form of                     *)
(* HMC_FIRST_VARIATION; the derivative is half the integral of the           *)
(* Euler-Lagrange density hmrm_eld with the weak partials.                   *)
(* ========================================================================= *)

let HMRM_FIRST_VARIATION_W12 = prove
 (`!S (G:real^K->real^K^K) d s (w:real^2->real^K) (phi:real^2->real^K).
     cm_target S G d /\ open s /\ bounded s /\ wan_w12 s w /\
     (!x. x IN s ==> w x IN S) /\ wan_vtest s phi
     ==> (!i. 1 <= i /\ i <= 2
              ==> (\x. lift(hmrm_eld S G (w x) (wan_wd s i w x) (phi x)
                                     (partial_derivative i phi x))) integrable_on s) /\
         ((\e. cm_gen G s (\x. closest_point S (w x + e % phi x))) has_real_derivative
          sum(1..2) (\i. drop(integral s
                       (\x. lift(hmrm_eld S G (w x) (wan_wd s i w x) (phi x)
                                          (partial_derivative i phi x))))) / &2)
         (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_SUBTUBE) THEN
  ABBREV_TAC `T2 = {p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)}` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMC_TARGET_CONSTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMRM_PG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^2->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`closure s:real^2->bool`; `phi:real^2->real^K`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `Mf:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`(:real^2)`; `closure s:real^2->bool`; `phi:real^2->real^K`]
                HMC_PARTIALS_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CLOSURE; SUBSET_UNIV; DIMINDEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`T2:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point (S:real^K->bool)) (at y))`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `CJ0:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`cm_tube S d:real^K->bool`; `T2:real^K->bool`;
                 `(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point (S:real^K->bool)) (at y))`] HMC_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CJ1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = d1 / (&2 * (Mf + &1))` THEN
  SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e x. abs e <= e1 /\ x IN s ==> norm(e % (phi:real^2->real^K) x) <= d1 / &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e1 * Mf` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      EXPAND_TAC "e1" THEN MATCH_MP_TAC HMC_E1_LEMMA THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e x. abs e <= e1 /\ x IN s
          ==> (w:real^2->real^K) x + e % phi x IN cm_tube S d1 /\
              w x + e % phi x IN T2 /\ w x + e % phi x IN cm_tube S d`
  (LABEL_TAC "TB") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(e % (phi:real^2->real^K) x) <= d1 / &2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->real^K) x IN S` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->real^K) x + e % phi x IN cm_tube S d1` ASSUME_TAC THENL
     [MATCH_MP_TAC HMRM_TUBE_NEAR THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `d1:real`; `d:real`] HMRM_TUBE_MONO) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; SUBSET]];
    ALL_TAC] THEN
  (* the energy along the line as a sum of integrals *)
  SUBGOAL_THEN
   `!e. abs e < e1
        ==> (!i. 1 <= i /\ i <= 2
                 ==> (\x. lift(hmrm_q S G ((w:real^2->real^K) x + e % phi x)
                                 (wan_wd s i w x + e % partial_derivative i phi x)))
                     integrable_on s) /\
            cm_gen G s (\x. closest_point S (w x + e % phi x)) =
            sum(1..2) (\i. drop(integral s
                (\x. lift(hmrm_q S G (w x + e % phi x)
                            (wan_wd s i w x + e % partial_derivative i phi x))))) / &2`
  (LABEL_TAC "EN") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                   `Pg:real^K->real^K`; `s:real^2->bool`; `w:real^2->real^K`;
                   `phi:real^2->real^K`; `e:real`] HMRM_GEN_LINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN USE_THEN "TB" (MP_TAC o SPECL [`e:real`; `x:real^2`]) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `FF' = \i e x.
      &2 * ((mderiv (\y. jacobian (closest_point (S:real^K->bool)) (at y))
                    ((w:real^2->real^K) x + e % phi x) (phi x) **
               (wan_wd s i w x + e % partial_derivative i phi x) +
             jacobian (closest_point S) (at (w x + e % phi x)) ** partial_derivative i phi x) dot
            ((G:real^K->real^K^K) (closest_point S (w x + e % phi x)) **
             (jacobian (closest_point S) (at (w x + e % phi x)) **
              (wan_wd s i w x + e % partial_derivative i phi x)))) +
      (jacobian (closest_point S) (at (w x + e % phi x)) **
       (wan_wd s i w x + e % partial_derivative i phi x)) dot
      (mderiv G (closest_point S (w x + e % phi x))
         (jacobian (closest_point S) (at (w x + e % phi x)) ** phi x) **
       (jacobian (closest_point S) (at (w x + e % phi x)) **
        (wan_wd s i w x + e % partial_derivative i phi x)))` THEN
  ABBREV_TAC `Aq = &2 * (CJ1 * Mf) * Lam1 * CJ0 + CJ0 * CJ0 * (CG * (CJ0 * Mf))` THEN
  ABBREV_TAC `Bq = &2 * Aq * (e1 * M1) + &2 * CJ0 * M1 * Lam1 * CJ0` THEN
  ABBREV_TAC `Cq = Aq * (e1 * M1) pow 2 + &2 * CJ0 * M1 * Lam1 * CJ0 * (e1 * M1)` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift((FF':num->real->real^2->real) i (&0) x)) integrable_on s /\
            ((\e. drop(integral s (\x. lift(hmrm_q S G ((w:real^2->real^K) x + e % phi x)
                                         (wan_wd s i w x + e % partial_derivative i phi x)))))
             has_real_derivative drop(integral s (\x. lift(FF' i (&0) x)))) (atreal (&0))`
  (LABEL_TAC "DER") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\e x. hmrm_q S G ((w:real^2->real^K) x + e % phi x)
                    (wan_wd s i w x + e % partial_derivative i phi x)`;
      `(FF':num->real->real^2->real) i`;
      `\x. Aq * norm(wan_wd s i (w:real^2->real^K) x) pow 2 +
           Bq * norm(wan_wd s i w x) + Cq`;
      `real_interval(--e1,e1)`; `s:real^2->bool`]
     GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        USE_THEN "EN" (MP_TAC o SPEC `e:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HMRM_FV_MAJORANT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
        ASM_SIMP_TAC[DIMINDEX_2; ETA_AX];
        MAP_EVERY X_GEN_TAC [`e:real`; `x:real^2`] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        EXPAND_TAC "FF'" THEN REWRITE_TAC[hmrm_q] THEN
        MATCH_MP_TAC HMC_LINE_DERIV THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "TB" (MP_TAC o SPECL [`e:real`; `x:real^2`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`e:real`; `x:real^2`] THEN STRIP_TAC THEN
        USE_THEN "TB" (MP_TAC o SPECL [`e:real`; `x:real^2`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN `(x:real^2) IN closure s` ASSUME_TAC THENL
         [MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `abs(e:real) <= e1` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`--e1 < e`; `e < e1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `norm((phi:real^2->real^K) x) <= Mf /\ norm(partial_derivative i phi x) <= M1`
        STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "FF'" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC HMRM_FV_BOUND THEN
        MAP_EVERY EXISTS_TAC [`T2:real^K->bool`; `Mf:real`; `M1:real`; `CJ0:real`;
                              `CJ1:real`; `Lam1:real`; `CG:real`; `e1:real`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `e1 / &2` THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `((\x. drop(integral s (\v. lift(hmrm_q S G ((w:real^2->real^K) v + x % phi v)
                     (wan_wd s i w v + x % partial_derivative i phi v)))))
       has_real_derivative drop(integral s (\v. lift((FF':num->real->real^2->real) i (&0) v))))
      (atreal (&0) within real_interval(--e1,e1))` THEN
    SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
             REAL_ARITH `&0 < e1 ==> --e1 < &0 /\ &0 < e1`; ASSUME `&0 < e1`];
    ALL_TAC] THEN
  (* FF' at e = 0 is the Euler-Lagrange density almost everywhere *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> !x. x IN s DIFF
                 {x | x IN s /\
                      ~(jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
                        wan_wd s i w x = wan_wd s i w x)}
                ==> lift(hmrm_eld S G (w x) (wan_wd s i w x) (phi x)
                                  (partial_derivative i phi x)) =
                    lift((FF':num->real->real^2->real) i (&0) x)`
  (LABEL_TAC "AE") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^2->real^K) x IN S` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `jacobian (closest_point S) (at ((w:real^2->real^K) x)) ** wan_wd s i w x =
      wan_wd s i w x`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "FF'" THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; hmrm_eld] THEN
    SIMP_TAC[CLOSEST_POINT_SELF; ASSUME `(w:real^2->real^K) x IN S`;
             ASSUME `jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
                     wan_wd s i w x = wan_wd s i w x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> negligible {x | x IN s /\
                            ~(jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
                              wan_wd s i w x = wan_wd s i w x)}`
  (LABEL_TAC "NT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRM_WD_TANGENT THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s i w x) (phi x)
                               (partial_derivative i phi x))) integrable_on s /\
            integral s (\x. lift((FF':num->real->real^2->real) i (&0) x)) =
            integral s (\x. lift(hmrm_eld S G (w x) (wan_wd s i w x) (phi x)
                                         (partial_derivative i phi x)))`
  (LABEL_TAC "IE") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. lift((FF':num->real->real^2->real) i (&0) x)` THEN
      EXISTS_TAC
       `{x | x IN s /\
             ~(jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
               wan_wd s i w x = wan_wd s i w x)}` THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "NT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        BETA_TAC THEN USE_THEN "AE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "DER" (MP_TAC o C MATCH_MP (ASSUME `1 <= i /\ i <= 2`)) THEN
        SIMP_TAC[]];
      MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC
       `{x | x IN s /\
             ~(jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
               wan_wd s i w x = wan_wd s i w x)}` THEN
      CONJ_TAC THENL
       [USE_THEN "NT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        BETA_TAC THEN USE_THEN "AE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "IE" (MP_TAC o C MATCH_MP (ASSUME `1 <= i /\ i <= 2`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC
   `\e. sum(1..2) (\i. drop(integral s
          (\x. lift(hmrm_q S G ((w:real^2->real^K) x + e % phi x)
                      (wan_wd s i w x + e % partial_derivative i phi x))))) / &2` THEN
  EXISTS_TAC `e1:real` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "EN" (MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `abs(e - &0) < e1` THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "IE" (MP_TAC o C MATCH_MP (ASSUME `1 <= i /\ i <= 2`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  USE_THEN "DER" (MP_TAC o C MATCH_MP (ASSUME `1 <= i /\ i <= 2`)) THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Locality of weak partials, splitting of the G-energy over an open subset  *)
(* and its complement.                                                       *)
(* ========================================================================= *)

(* Weak partials of two W^{1,2} maps that agree on an open subset t agree  *)
(* almost everywhere on t.                                                    *)

let HMRM_WD_LOCAL = prove
 (`!(s:real^N->bool) t (u:real^N->real^K) v i.
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u /\ wan_w12 s v /\
     (!x. x IN t ==> u x = v x) /\ 1 <= i /\ i <= dimindex(:N)
     ==> negligible {x | x IN t /\ ~(wan_wd s i u x = wan_wd s i v x)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `u:real^N->real^K`; `i:num`]
                WAN_WD_RESTRICT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `v:real^N->real^K`; `i:num`]
                WAN_WD_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `{x | x IN t /\ ~(wan_wd t i (u:real^N->real^K) x = wan_wd s i u x)} UNION
    {x | x IN t /\ ~(wan_wd t i (v:real^N->real^K) x = wan_wd s i v x)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd t i (u:real^N->real^K) = wan_wd t i v` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_WD_AE THEN MATCH_MP_TAC HMD_EQ_IMP_NULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The G-energy density of a W^{1,2} map: absolutely integrable.           *)

let HMRM_GDENS_ABSINT = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) i.
     cm_target S G d /\ open s /\ wan_w12 s u /\ 1 <= i /\ i <= 2
     ==> (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))
         absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP HMD_TARGET_ELLIPTIC (ASSUME `cm_target S (G:real^K->real^K^K) d`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ell")))))) THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(wan_wd s i (u:real^2->real^K) x) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      USE_THEN "ell" (fun th -> REWRITE_TAC[th])];
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`; `Lam:real`;
                   `i:num`] HMD_GDIR_INTEGRABLE) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`z:real^K`; `xi:real^K`] THEN
    USE_THEN "ell" (MP_TAC o SPECL [`z:real^K`; `xi:real^K`]) THEN
    SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      REAL_ARITH_TAC]]);;

(* Splitting the G-energy over an open subset s' of s.                       *)

let HMRM_GDIR_SPLIT = prove
 (`!S (G:real^K->real^K^K) d s s' (u:real^2->real^K).
     cm_target S G d /\ open s /\ open s' /\ s' SUBSET s /\ wan_w12 s u
     ==> wan_gdir s G u =
         wan_gdir s' G u +
         sum(1..2) (\i. drop(integral (s DIFF s')
                    (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir; DIMINDEX_2; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `i:num`] HMRM_GDENS_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral s' (\x. lift(wan_wd s' i (u:real^2->real^K) x dot
                          ((G:real^K->real^K^K)(u x) ** wan_wd s' i u x))) =
    integral s' (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN s' /\ ~(wan_wd s' i (u:real^2->real^K) x = wan_wd s i u x)}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^2->bool`; `s':real^2->bool`; `u:real^2->real^K`; `i:num`]
                    WAN_WD_RESTRICT) THEN
      ASM_SIMP_TAC[DIMINDEX_2];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. lift(wan_wd s i (u:real^2->real^K) x dot
                         ((G:real^K->real^K^K)(u x) ** wan_wd s i u x))) =
    integral (s' UNION (s DIFF s'))
             (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))`
  SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_UNION THEN
  REWRITE_TAC[SET_RULE `(s':real^2->bool) INTER (s DIFF s') = {}`; NEGLIGIBLE_EMPTY] THEN
  CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; LEBESGUE_MEASURABLE_DIFF] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Minimizers have a local minimum of the energy of an open subset along     *)
(* every projected variation, and continuous S-valued minimizers are         *)
(* cm_wharmonic.                                                             *)
(* ========================================================================= *)

let HMRM_MIN_LOCAL = prove
 (`!S (G:real^K->real^K^K) d s s' (w:real^2->real^K) (phi:real^2->real^K).
     cm_target S G d /\ open s /\ bounded s /\ cm_minimizer S G s w /\
     (!x. x IN s ==> w x IN S) /\ open s' /\ s' SUBSET s /\ wan_vtest s' phi
     ==> ?e0. &0 < e0 /\
              !e. abs e < e0
                  ==> cm_gen G s' w <= cm_gen G s' (\x. closest_point S (w x + e % phi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMRM_PG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `Pg:real^K->real^K` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^2->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `wan_vtest s (phi:real^2->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `kp:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kp:real^2->bool`; `phi:real^2->real^K`] HMC_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `Mf:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!x. norm((phi:real^2->real^K) x) <= Mf` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN ASM_CASES_TAC `(x:real^2) IN kp` THEN
    ASM_SIMP_TAC[NORM_0];
    ALL_TAC] THEN
  EXISTS_TAC `d1 / (Mf + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. norm(e % (phi:real^2->real^K) x) < d1` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs e * (Mf + &1) < d1` ASSUME_TAC THENL
     [UNDISCH_TAC `abs e < d1 / (Mf + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= Mf ==> &0 < Mf + &1`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs e * (Mf + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= m + &1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN s ==> (w:real^2->real^K) x + e % phi x IN cm_tube S d1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRM_TUBE_NEAR THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `d1:real`; `B:real`;
                 `Pg:real^K->real^K`; `s:real^2->bool`; `w:real^2->real^K`;
                 `phi:real^2->real^K`; `e:real`] HMRM_GEN_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]); DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `cm_wmap S s (\x. closest_point S ((w:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[cm_wmap] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `{}:real^2->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s /\ ~(x IN kp)
        ==> closest_point S ((w:real^2->real^K) x + e % phi x) = w x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; CLOSEST_POINT_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w120 s (\x. closest_point S ((w:real^2->real^K) x + e % phi x) - w x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN EXISTS_TAC `kp:real^2->bool` THEN
    ASM_SIMP_TAC[WAN_W12_SUB; VECTOR_SUB_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_gen G s (w:real^2->real^K) <=
    cm_gen G s (\x. closest_point S (w x + e % phi x))`
  MP_TAC THENL
   [UNDISCH_TAC `cm_minimizer S (G:real^K->real^K^K) s (w:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cm_gen] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `s':real^2->bool`; `w:real^2->real^K`] HMRM_GDIR_SPLIT) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `s':real^2->bool`;
                 `\x. closest_point S ((w:real^2->real^K) x + e % phi x)`] HMRM_GDIR_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. drop(integral (s DIFF s')
       (\x. lift(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x dot
                 (G(closest_point S (w x + e % phi x)) **
                  wan_wd s i (\x. closest_point S (w x + e % phi x)) x))))) =
    sum(1..2) (\i. drop(integral (s DIFF s')
       (\x. lift(wan_wd s i w x dot (G(w x) ** wan_wd s i w x)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{x | x IN s DIFF kp /\
           ~(wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
             wan_wd s i w x)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_WD_LOCAL THEN ASM_REWRITE_TAC[DIMINDEX_2; SUBSET_DIFF] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        REWRITE_TAC[IN_DIFF] THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((x:real^2) IN kp)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `wan_wd s i (\x. closest_point S ((w:real^2->real^K) x + e % phi x)) x =
        wan_wd s i w x`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    REAL_ARITH_TAC]);;

let HMRM_DERIV_LOCAL_MIN = prove
 (`!f D. (f has_real_derivative D) (atreal (&0))
         ==> (?e0. &0 < e0 /\ !e. abs e < e0 ==> f(&0) <= f e)
         ==> (f has_real_derivative &0) (atreal (&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `D = &0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `&0`; `real_interval(--e0,e0)`] THEN
    ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

(* Continuous S-valued energy minimizers on a bounded open set are weakly  *)
(* harmonic in the sense of pc_hm_reg_defs (cm_wharmonic).                 *)

let HMRM_CONT_MIN_WHARMONIC = prove
 (`!S (G:real^K->real^K^K) d s (w:real^2->real^K).
     cm_target S G d /\ open s /\ bounded s /\ cm_minimizer S G s w /\
     w continuous_on s /\ (!x. x IN s ==> w x IN S)
     ==> cm_wharmonic S G s w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 s (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cm_wharmonic] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s':real^2->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s':real^2->bool`;
                 `w:real^2->real^K`; `phi:real^2->real^K`] HMRM_FIRST_VARIATION_W12) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN(MP_TAC o MATCH_MP HMRM_DERIV_LOCAL_MIN o CONJUNCT2)] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `s':real^2->bool`; `w:real^2->real^K`; `phi:real^2->real^K`]
                HMRM_MIN_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `cm_gen G s' (\x. closest_point S ((w:real^2->real^K) x + &0 % phi x)) = cm_gen G s' w`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC HMD_GEN_AE THEN MATCH_MP_TAC HMD_EQ_IMP_NULL THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CLOSEST_POINT_SELF THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The weak Euler-Lagrange equation of a cm_wharmonic map (used for         *)
(* CM_REG01): the first variation vanishes for every test map.              *)

let HMRM_WHARMONIC_EL = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) s' (phi:real^2->real^K).
     cm_target S G d /\ cm_wharmonic S G s u /\
     open s' /\ bounded s' /\ closure s' SUBSET s /\ wan_vtest s' phi
     ==> sum(1..2) (\i. drop(integral s'
           (\x. lift(hmrm_eld S G (u x) (wan_wd s' i u x) (phi x)
                              (partial_derivative i phi x))))) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_wharmonic] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s':real^2->bool`;
                 `u:real^2->real^K`; `phi:real^2->real^K`] HMRM_FIRST_VARIATION_W12) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^2->real^K`; `s':real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  REAL_ARITH_TAC);;

