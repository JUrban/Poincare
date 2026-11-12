(* ========================================================================= *)
(* pc_p2a_l72b: O10, the view-chart link for p2a_admx curves: the s-form     *)
(* integrand in a region chart is the chart Lagrangian (P2AK_LSINT_CHART_X,  *)
(* the admx copy of P2A_LSINT_CHART), and the L-length over [s1^2,s2^2] is   *)
(* the integral of the chart Lagrangian over [s1,s2].                        *)
(* The first part: the s-form integrand in a region chart.                   *)
(* ========================================================================= *)

needs "src/pc_p2a_l72a.ml";;
needs "src/pc_p2a_rgx.ml";;
needs "src/pc_p2a_smth.ml";;

prioritize_real();;
type_invention_error := true;;

(* The copy of P2A_LSINT_CHART (pc_p2a_lgeo3) for p2a_admx curves: the      *)
(* L-geodesic is used there only for b > 0 and the continuity of the curve, *)
(* P2AXR_ADMX_SCONT gives the latter.                                       *)

(* The slice-chart curve of a p2a_admx curve has an s-derivative where a   *)
(* region-chart curve has one (the first half of P2AK_LSINT_CHART_X).       *)

let P2AK_SLICE_VEL_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) gamma b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ p2a_admx V tt x b gamma /\ &0 <= s /\ s pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> ?w. ((\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma(s pow 2)))
                      (gamma(drop v pow 2))) has_vector_derivative w)
             (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - s pow 2)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt - s pow 2`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                            ((gamma:real->A)(s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `p = (gamma:real->A)(s pow 2)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s pow 2`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `O2 = IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> (h:real^N->real^N)(phi q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) p IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* the velocity in the slice chart *)
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                        ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b'`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST];
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)`;
                     `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`]
                P2AXR_ADMX_SCONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `(U INTER W) INTER FST(c':(A->bool)#(A->real^N))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))) has_vector_derivative
     frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A)
    (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(h:real^N->real^N) o (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))`;
      `e:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^1` THEN
      REWRITE_TAC[IN_ELIM_THM; dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(gamma:real->A)(drop(v:real^1) pow 2) IN
                    (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
        can (find_term ((=) `phi:A->real^N`)) (concl th) &&
        not (can (find_term ((=) `O:real^N->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A` THEN
  ASM_REWRITE_TAC[]);;

let P2AK_LSINT_CHART_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) gamma b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ p2a_admx V tt x b gamma /\ &0 <= s /\ s pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> p2a_lsint V tt gamma b s =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2))) A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - s pow 2)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt - s pow 2`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_lsint; mfd_scalar] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                            ((gamma:real->A)(s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `p = (gamma:real->A)(s pow 2)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s pow 2`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `O2 = IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `G' = metric_local (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                              (real->A->real^N^N)) (tt - s pow 2))
                                c' (p2a_vmetric V (tt - s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> (h:real^N->real^N)(phi q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) p IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (tt - s pow 2) y =
            mpullback (h:real^N->real^N) G' y`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN EXPAND_TAC "G'" THEN
    MATCH_MP_TAC P2A_RLOCAL_SLICE THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field O2 (G':real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "G'" THEN
      UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "O2" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
            (phi p) =
    lscalar G' (SND(c':(A->bool)#(A->real^N)) p)`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `lscalar (mpullback (h:real^N->real^N) G') ((phi:A->real^N) p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`O2:real^N->bool`; `O:real^N->bool`; `h:real^N->real^N`;
                   `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)`;
                   `G':real^N->real^N^N`; `(phi:A->real^N) p`] LSCALAR_PULLBACK) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the velocity in the slice chart *)
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                        ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b'`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST];
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)`;
                     `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`]
                P2AXR_ADMX_SCONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `(U INTER W) INTER FST(c':(A->bool)#(A->real^N))`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))) has_vector_derivative
     frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A)
    (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(h:real^N->real^N) o (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))`;
      `e:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^1` THEN
      REWRITE_TAC[IN_ELIM_THM; dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(gamma:real->A)(drop(v:real^1) pow 2) IN
                    (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
        can (find_term ((=) `phi:A->real^N`)) (concl th) &&
        not (can (find_term ((=) `O:real^N->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative (\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2)))
      (at (lift s) within interval[vec 0,lift(sqrt b)]) =
    frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LE_RSQRT];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_llag] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[mpullback] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS (ASSUME
    `linear(frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)))`))] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;


(* The copy of P2A_LINT_SINT (pc_p2a_lgeo3) for p2a_admx curves at a point  *)
(* where the slice-chart curve has an s-derivative.                          *)

let P2AK_LINT_SINT_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) gamma b s.
     p2a_svs V /\ p2a_admx V tt x b gamma /\ &0 < s /\ s pow 2 <= b /\
     (?w. ((\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma(s pow 2)))
                    (gamma(drop v pow 2))) has_vector_derivative w)
          (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}))
     ==> &2 * s * p2a_L_integrand V tt gamma b (s pow 2) = p2a_lsint V tt gamma b s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ sqrt(s pow 2) = s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2 o
                                           CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) (tt - s pow 2))
                          (p2a_vatlas V (tt - s pow 2)) /\
    riemannian_metric (p2a_vatlas V (tt - s pow 2)) (p2a_vmetric V (tt - s pow 2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt - s pow 2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^N. &0 <= v dot (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2)
                                 ((gamma:real->A)(s pow 2)) ** v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `(gamma:real->A)(s pow 2)`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)) ((gamma:real->A)(s pow 2))`) THEN
    ASM_REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)) ((gamma:real->A)(s pow 2)))
                                ((gamma:real->A)(s pow 2))` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                            ((gamma:real->A)(s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\r. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))) has_vector_derivative
     (inv(&2 * s) % w)) (at (lift(s pow 2)) within interval[lift(&0),lift b])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))) o
       (lift o sqrt o drop)`; `&1`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_01];
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; o_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * s) % (w:real^N) =
                  drop(lift(inv(&2 * sqrt(s pow 2)))) % w` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
      (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; o_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_L_integrand; p2a_lsint; mfd_speed; mfd_velocity] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vector_derivative (\r. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
      (at (lift(s pow 2)) within interval[lift(&0),lift b]) = inv(&2 * s) % w /\
    vector_derivative (\v. SND c' (gamma(drop v pow 2)))
      (at (lift s) within interval[vec 0,lift(sqrt b)]) = w`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LE_RSQRT; REAL_LT_IMP_LE] THEN
    UNDISCH_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
      (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGD_QUAD_HOMOG; SQRT_POW_2; REAL_LE_MUL; REAL_LE_SQUARE] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;


(* Combined: where a region-chart curve of a p2a_admx curve has the         *)
(* s-derivative A, 2 s times the L-integrand is the chart Lagrangian.        *)

let P2AK_LINT_CHART_X = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) gamma b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ p2a_admx V tt x b gamma /\ &0 < s /\ s pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> &2 * s * p2a_L_integrand V tt gamma b (s pow 2) =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2))) A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`; `s:real`]
                P2AK_LINT_SINT_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AK_SLICE_VEL_X THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                          `phi:A->real^N`; `A:real^N`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2AK_LSINT_CHART_X THEN MAP_EVERY EXISTS_TAC [`x:A`; `a':real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The substitution tau = s^2 for absolutely integrable functions            *)
(* (HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_1; no continuity of the        *)
(* integrand is needed, so corners of the curve do not matter).              *)
(* ------------------------------------------------------------------------- *)

let P2AK_SQ_IMAGE = prove
 (`!a b. &0 <= a /\ a <= b
         ==> IMAGE (\x:real. x pow 2) (real_interval[a,b]) = real_interval[a pow 2,b pow 2]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `y:real` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `sqrt y` THEN
    SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
     [MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC]]);;

let P2AK_SQ_SUBST = prove
 (`!f s1 s2.
     &0 <= s1 /\ s1 <= s2 /\
     f absolutely_real_integrable_on real_interval[s1 pow 2,s2 pow 2]
     ==> (\s. &2 * s * f(s pow 2)) real_integrable_on real_interval[s1,s2] /\
         real_integral (real_interval[s1,s2]) (\s. &2 * s * f(s pow 2)) =
         real_integral (real_interval[s1 pow 2,s2 pow 2]) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `f real_integrable_on real_interval[s1 pow 2,s2 pow 2]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift o (\x:real. x pow 2) o drop`; `\x:real. &2 * x`;
                 `interval[lift s1,lift s2]`;
                 `integral (interval[lift(s1 pow 2),lift(s2 pow 2)]) (lift o f o drop)`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_1) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL; IN_INTERVAL_1] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
      REWRITE_TAC[o_THM; LIFT_EQ; LIFT_DROP] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ] THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      MP_TAC(ISPECL [`\x:real. x`; `&1`; `drop(x:real^1)`; `2`]
                    HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
      REWRITE_TAC[REAL_POW_1; REAL_MUL_RID; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (lift o (\x:real. x pow 2) o drop) (interval[lift s1,lift s2]) =
                interval[lift(s1 pow 2),lift(s2 pow 2)]` SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o; IMAGE_DROP_INTERVAL; LIFT_DROP] THEN
    ASM_SIMP_TAC[P2AK_SQ_IMAGE; IMAGE_LIFT_REAL_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `f absolutely_real_integrable_on real_interval[s1 pow 2,s2 pow 2]` THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^1. x IN interval[lift s1,lift s2]
               ==> abs(&2 * drop x) % (lift o f o drop) ((lift o (\x. x pow 2) o drop) x) =
                   (lift o (\s. &2 * s * f(s pow 2)) o drop) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs(&2 * drop(x:real^1)) = &2 * drop x` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x:real^1. abs(&2 * drop x) % (lift o f o drop) ((lift o (\x. x pow 2) o drop) x)` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. &2 * s * f(s pow 2)) real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x:real^1. abs(&2 * drop x) % (lift o f o drop) ((lift o (\x. x pow 2) o drop) x)` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[lift s1,lift s2])
                (\x:real^1. abs(&2 * drop x) % (lift o f o drop) ((lift o (\x. x pow 2) o drop) x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

(* With a locally constant atlas, a compact time interval contains only     *)
(* finitely many times where the atlas is not constant nearby.              *)

let P2AK_LC_FINITE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ta tb.
     p2a_atlas_lc V
     ==> FINITE {t | ta <= t /\ t <= tb /\
                     ~(?d. &0 < d /\
                           !t'. abs(t' - t) < d ==> p2a_vatlas V t' = p2a_vatlas V t)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_atlas_lc; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real->real` (LABEL_TAC "D")) THEN
  MP_TAC(ISPEC `interval[lift ta,lift tb]` COMPACT_IMP_HEINE_BOREL) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (\t. ball(lift t,(D:real->real) t)) (real_interval[ta,tb])`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; CENTRE_IN_BALL] THEN
    USE_THEN "D" (MP_TAC o SPEC `t:real`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^1->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\t. ball(lift t,(D:real->real) t)`; `real_interval[ta,tb]`;
                 `f':(real^1->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `T0:real->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `T0:real->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `interval[lift ta,lift tb] SUBSET UNIONS (f':(real^1->bool)->bool)` THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_BALL; DIST_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t:real = t0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(?d. &0 < d /\
                     !t'. abs(t' - t) < d
                          ==> p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                            (real->A->real^N^N)) t' = p2a_vatlas V t)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  USE_THEN "D" (MP_TAC o SPEC `t0:real`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "R"))) THEN
  SUBGOAL_THEN `t < t0 \/ t0 < t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `min (t0 - t) (t - (t0 - (D:real->real) t0))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t':real` THEN DISCH_TAC THEN USE_THEN "L" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `min (t - t0) ((t0 + (D:real->real) t0) - t)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t':real` THEN DISCH_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* An integrable function bounded below off a finite set is absolutely       *)
(* integrable.                                                                *)

let P2AK_ABS_INT_LOWER = prove
 (`!f a b C E.
     FINITE E /\ f real_integrable_on real_interval[a,b] /\ &0 <= C /\
     (!t. t IN real_interval[a,b] /\ ~(t IN E) ==> --C <= f t)
     ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \t. if t IN E then &0 else (f:real->real) t` THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] DIFF E ==> (g:real->real) t = f t` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real->real) real_integrable_on real_interval[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `E:real->bool`] THEN
    ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real->real) absolutely_real_integrable_on real_interval[a,b]` MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\t. (g:real->real) t + &2 * C` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_CONST; ETA_AX] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `C:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[absolutely_real_integrable_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`\t. abs((g:real->real) t)`; `E:real->bool`] THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* A region-chart curve of a p2a_admx curve is C^1 in s away from the        *)
(* corners and the times where the atlas changes (P2AXR_PC1X_TAU_C1 and the  *)
(* chain rule P2A_SQ_CURVE_VD).                                              *)
(* ------------------------------------------------------------------------- *)

let P2AK_PIECE_C1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) P W a' b' U (phi:A->real^N) s0.
     p2a_admx V tt x b gamma /\ p2a_pc1x V tt gamma (&0) b P /\
     &0 < s0 /\ s0 pow 2 < b /\ ~(s0 pow 2 IN P) /\
     (?d. &0 < d /\
          !t'. abs(t' - (tt - s0 pow 2)) < d
               ==> p2a_vatlas V t' = p2a_vatlas V (tt - s0 pow 2)) /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b' /\ gamma(s0 pow 2) IN U INTER W
     ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s0)) /\
         (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
           continuous (at (lift s0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `P:real->bool`; `s0 pow 2`; `d:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`] P2AXR_PC1X_TAU_C1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`s0 pow 2`; `O:A->bool`] o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2a_admx] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DIF") (LABEL_TAC "CONT")))) THEN
  ABBREV_TAC `Yt = \t:real^1. (phi:A->real^N)((gamma:real->A)(drop t))` THEN
  SUBGOAL_THEN `(\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) =
                (\v. (Yt:real^1->real^N)(lift(drop v pow 2)))` SUBST1_TAC THENL
   [EXPAND_TAC "Yt" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  (* near s0 the squared times stay in the e-window *)
  SUBGOAL_THEN `?h. &0 < h /\ !s. abs(s - s0) < h ==> abs(s pow 2 - s0 pow 2) < e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real. x pow 2) real_continuous atreal s0` MP_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID]; ALL_TAC] THEN
    REWRITE_TAC[real_continuous_atreal] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < h
        ==> ((\v. (Yt:real^1->real^N)(lift(drop v pow 2))) has_vector_derivative
             (&2 * s) % vector_derivative Yt (at (lift(s pow 2)))) (at (lift s))`
  (LABEL_TAC "VD") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2A_SQ_CURVE_VD THEN
    USE_THEN "DIF" MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h':real^1. drop h' % ((&2 * s0) % vector_derivative (Yt:real^1->real^N)
                                                      (at (lift(s0 pow 2))))` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN USE_THEN "VD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\v:real^1. (&2 * drop v) % vector_derivative (Yt:real^1->real^N)
                                                         (at (lift(drop v pow 2)))` THEN
  EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    USE_THEN "VD" (MP_TAC o SPEC `drop(v:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
    REWRITE_TAC[LIFT_DROP; CONTINUOUS_AT_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:real^1. vector_derivative (Yt:real^1->real^N) (at (lift(drop v pow 2)))) =
    (\t. vector_derivative Yt (at t)) o (\v. lift(drop v pow 2))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\v:real^1. lift(drop v pow 2)) = lift o (\x:real. x pow 2) o drop`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % lift(&2 * s0)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `s0:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN REWRITE_TAC[REAL_POW_1; REAL_MUL_RID; ETA_AX];
    REWRITE_TAC[LIFT_DROP] THEN USE_THEN "CONT" ACCEPT_TAC]);;

(* On a compact s-interval inside one region chart, the chart curve is      *)
(* continuous and C^1 off a finite set containing the end points.            *)

let P2AK_ADMX_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) W a' b' U (phi:A->real^N) s1 s2.
     p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN U INTER W /\ a' < tt - s pow 2 /\ tt - s pow 2 <= b')
     ==> ?K. FINITE K /\ s1 IN K /\ s2 IN K /\
             (\v. phi(gamma(drop v pow 2))) continuous_on interval[lift s1,lift s2] /\
             (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                  ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
                      (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                        continuous (at (lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?P. p2a_pc1x (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma (&0) b P`
  (X_CHOOSE_TAC `P:real->bool`) THENL [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(P:real->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_pc1x]; ALL_TAC] THEN
  ABBREV_TAC `CH = {t | tt - s2 pow 2 <= t /\ t <= tt - s1 pow 2 /\
                        ~(?d. &0 < d /\
                              !t'. abs(t' - t) < d
                                   ==> p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                                     (real->A->real^N^N)) t' = p2a_vatlas V t)}` THEN
  SUBGOAL_THEN `FINITE(CH:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "CH" THEN MATCH_MP_TAC P2AK_LC_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(s1:real) INSERT s2 INSERT (IMAGE sqrt P UNION IMAGE (\t. sqrt(tt - t)) CH)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; FINITE_IMAGE];
    REWRITE_TAC[IN_INSERT];
    REWRITE_TAC[IN_INSERT];
    MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `tt:real`; `b:real`; `W:A->bool`;
                          `a':real`; `b':real`; `U:A->bool`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2AXR_ADMX_SCONT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; IN_IMAGE; DE_MORGAN_THM; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `s2 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2AK_PIECE_C1 THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `P:real->bool`;
                        `W:A->bool`; `a':real`; `b':real`; `U:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN U INTER W /\ a' < tt - s pow 2 /\
                tt - s pow 2 <= b'` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sqrt`)) (concl th) &&
      can (find_term ((=) `P:real->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MP_TAC o SPEC `tt - s pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CH:real->bool`)) (concl th))) THEN
    REWRITE_TAC[REAL_ARITH `tt - (tt - x) = x`] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "CH" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `tt - s2 pow 2 <= tt - s pow 2 /\ tt - s pow 2 <= tt - s1 pow 2` MP_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[REAL_ARITH `tt - a <= tt - b <=> b <= a`] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* The L-length over [s1^2,s2^2] is the integral of the chart Lagrangian    *)
(* over [s1,s2] (off the finite set K the integrands agree by              *)
(* P2AK_LINT_CHART_X; the L-integrand is bounded below there, hence          *)
(* absolutely integrable, and P2AK_SQ_SUBST applies).                        *)

let P2AK_PIECE_INT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) W a' b' U (phi:A->real^N) s1 s2 sa sb K.
     p2a_svs V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> gamma(s pow 2) IN U INTER W) /\
     FINITE K /\
     (\v. phi(gamma(drop v pow 2))) continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)))
     ==> (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2)))
                (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
         real_integrable_on real_interval[s1,s2] /\
         real_integral (real_interval[s1,s2])
           (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2)))
                  (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))) =
         real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))` THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)` THEN
  ABBREV_TAC `f = p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b` THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (Y:real^1->real^N)(lift s) = phi((gamma:real->A)(s pow 2))`
  ASSUME_TAC THENL [EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  (* the s-family and the bounds on the image of the piece *)
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb (\s. (Gt:real->real^N->real^N^N)(tt - s pow 2))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (Y:real^1->real^N) (interval[lift s1,lift s2])) /\
                IMAGE Y (interval[lift s1,lift s2]) SUBSET IMAGE (phi:A->real^N) (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`;
                 `Gt:real->real^N->real^N^N`; `tt:real`;
                 `IMAGE (Y:real^1->real^N) (interval[lift s1,lift s2])`; `s1:real`; `s2:real`]
                P2AK_LLAG_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gm:real` (X_CHOOSE_THEN `Rm:real` STRIP_ASSUME_TAC)) THEN
  (* the integrands agree off K *)
  SUBGOAL_THEN
   `!s. s1 < s /\ s < s2 /\ ~(s IN K)
        ==> &2 * s * (f:real->real)(s pow 2) =
            p2a_llag (Gt:real->real^N->real^N^N) tt s (phi((gamma:real->A)(s pow 2)))
                     (vector_derivative (Y:real^1->real^N) (at (lift s)))`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["f"; "Gt"] THEN
    MATCH_MP_TAC P2AK_LINT_CHART_X THEN MAP_EVERY EXISTS_TAC [`x:A`; `a':real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s2 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* f is bounded below off the squares of the exceptional points *)
  ABBREV_TAC `E = IMAGE (\s:real. s pow 2) ((s1:real) INSERT s2 INSERT K)` THEN
  SUBGOAL_THEN `FINITE(E:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s2 pow 2 * Rm / s1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[s1 pow 2,s2 pow 2] /\ ~(t IN E)
        ==> --(s2 pow 2 * Rm / s1) <= (f:real->real) t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `s = sqrt t` THEN
    SUBGOAL_THEN `s pow 2 = t /\ &0 <= s` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `s1 <= s /\ s <= s2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s1 < s /\ s < s2 /\ ~(s IN K)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((t:real) IN E)` THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[IN_IMAGE; IN_INSERT; NOT_EXISTS_THM; DE_MORGAN_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `s:real = s1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `s:real = s2` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "EQ" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift s) IN IMAGE Y (interval[lift s1,lift s2])`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) =
                  (Y:real^1->real^N)(lift s)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^1->real^N`)) (concl th) &&
        can (find_term ((=) `phi:A->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(Y:real^1->real^N)(lift s)`;
                                  `vector_derivative (Y:real^1->real^N) (at (lift s))`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 <= vector_derivative (Y:real^1->real^N) (at (lift s)) dot
            ((Gt:real->real^N->real^N^N)(tt - s pow 2) (Y(lift s)) **
             vector_derivative Y (at (lift s)))`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o MATCH_MP P2A_LSMOOTH_BASIC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
      REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `(Y:real^1->real^N)(lift s)` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term ((=) `IMAGE (phi:A->real^N) (U INTER W)`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `vector_derivative (Y:real^1->real^N) (at (lift s))` o
                 CONJUNCT2) THEN
      ASM_CASES_TAC `vector_derivative (Y:real^1->real^N) (at (lift s)) = vec 0` THEN
      ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) t * (&2 * s) =
                  p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                           (vector_derivative Y (at (lift s)))` ASSUME_TAC THENL
     [UNDISCH_TAC `&2 * s * (f:real->real) (s pow 2) =
                   p2a_llag (Gt:real->real^N->real^N^N) tt s (phi((gamma:real->A)(s pow 2)))
                            (vector_derivative (Y:real^1->real^N) (at (lift s)))` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(s2 pow 2 * Rm) <= (f:real->real) t * s` MP_TAC THENL
     [SUBGOAL_THEN `s pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                      ((Y:real^1->real^N)(lift s)) >= --(s2 pow 2 * Rm)`
      MP_TAC THENL
       [REWRITE_TAC[real_ge] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(s pow 2 * Rm)` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH `--(a * b) <= a * c <=> a * --b <= a * c`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      UNDISCH_TAC `(f:real->real) t * (&2 * s) =
                   p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                            (vector_derivative Y (at (lift s)))` THEN
      REWRITE_TAC[p2a_llag] THEN
      UNDISCH_TAC `&0 <= vector_derivative (Y:real^1->real^N) (at (lift s)) dot
                         ((Gt:real->real^N->real^N^N)(tt - s pow 2) (Y(lift s)) **
                          vector_derivative Y (at (lift s)))` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `--(s2 pow 2 * Rm) / s <= (f:real->real) t` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `(s2 pow 2 * Rm) * inv s <= (s2 pow 2 * Rm) * inv s1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* absolute integrability and the substitution *)
  SUBGOAL_THEN `(f:real->real) absolutely_real_integrable_on real_interval[s1 pow 2,s2 pow 2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_ABS_INT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`s2 pow 2 * Rm / s1`; `E:real->bool`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "f" THEN
      UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b gamma` THEN
      REWRITE_TAC[p2a_admx] THEN SIMP_TAC[];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `s1:real`; `s2:real`] P2AK_SQ_SUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[s1,s2] DIFF ((s1:real) INSERT s2 INSERT K)
        ==> p2a_llag (Gt:real->real^N->real^N^N) tt s (phi((gamma:real->A)(s pow 2)))
                     (vector_derivative (Y:real^1->real^N) (at (lift s))) =
            &2 * s * (f:real->real)(s pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
    MAP_EVERY EXISTS_TAC [`\s. &2 * s * (f:real->real)(s pow 2)`;
                          `(s1:real) INSERT s2 INSERT K`] THEN
    ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[s1,s2]) (\s. &2 * s * (f:real->real)(s pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `(s1:real) INSERT s2 INSERT K` THEN
      ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The chart curve of a p2a_admx curve on a compact s-interval inside one    *)
(* region chart is a p2ak_sq curve (pc_p2a_l72a), with bad set the           *)
(* exceptional points in the interval, and its energy is bounded by its      *)
(* L-length (given a lower metric bound lam and a curvature bound Rm on a    *)
(* set C containing the curve).                                              *)
(* ------------------------------------------------------------------------- *)

(* Pointwise: |u|^2 <= (2 / lam)(llag + 2 s2^2 Rm) for the s-Lagrangian.     *)

let P2AK_LLAG_DOM_PT = prove
 (`!lam q n2 R Rm s s2.
     &0 < lam /\ lam * n2 <= q /\ abs R <= Rm /\ &0 <= s /\ s <= s2 /\ &0 <= n2
     ==> abs n2 <= &2 / lam * ((inv(&2) * q + &2 * s pow 2 * R) + &2 * s2 pow 2 * Rm)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(s pow 2 * R) <= s2 pow 2 * Rm` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n2 <= q * inv lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv lam * (s pow 2 * R + s2 pow 2 * Rm)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= n2 ==> abs n2 = n2`] THEN
  REWRITE_TAC[real_div] THEN
  UNDISCH_TAC `n2 <= q * inv lam` THEN
  UNDISCH_TAC `&0 <= inv lam * (s pow 2 * R + s2 pow 2 * Rm)` THEN
  REAL_ARITH_TAC);;

(* The energy of a chart curve is dominated by its Lagrangian; |Y'|^2 is    *)
(* measurable (continuous off a finite set), hence integrable.              *)

let P2AK_ENERGY_DOM = prove
 (`!(Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) s1 s2 K C lam Rm.
     &0 <= s1 /\ s1 <= s2 /\ FINITE K /\ &0 < lam /\
     (!s. s1 <= s /\ s <= s2 ==> Y(lift s) IN C) /\
     (!s y u. s1 <= s /\ s <= s2 /\ y IN C
              ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) y ** u) /\
                  abs(lscalar (Gt(tt - s pow 2)) y) <= Rm) /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (\v. vector_derivative Y (at v)) continuous (at (lift s))) /\
     (\s. p2a_llag Gt tt s (Y(lift s)) (vector_derivative Y (at (lift s))))
       real_integrable_on real_interval[s1,s2]
     ==> (\s. norm(vector_derivative Y (at (lift s))) pow 2)
           real_integrable_on real_interval[s1,s2] /\
         real_integral (real_interval[s1,s2])
           (\s. norm(vector_derivative Y (at (lift s))) pow 2)
         <= &2 / lam *
            (real_integral (real_interval[s1,s2])
               (\s. p2a_llag Gt tt s (Y(lift s)) (vector_derivative Y (at (lift s)))) +
             &2 * s2 pow 2 * Rm * (s2 - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = \s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                        (vector_derivative Y (at (lift s)))` THEN
  ABBREV_TAC `e = \s. norm(vector_derivative (Y:real^1->real^N) (at (lift s))) pow 2` THEN
  (* pointwise domination *)
  SUBGOAL_THEN
   `!s. s IN real_interval[s1,s2]
        ==> abs((e:real->real) s) <= &2 / lam * ((l:real->real) s + &2 * s2 pow 2 * Rm)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["e"; "l"] THEN REWRITE_TAC[p2a_llag] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(Y:real^1->real^N)(lift s)`;
                                  `vector_derivative (Y:real^1->real^N) (at (lift s))`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    MATCH_MP_TAC P2AK_LLAG_DOM_PT THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* measurability *)
  SUBGOAL_THEN `(e:real->real) real_measurable_on real_interval[s1,s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(s1:real) INSERT s2 INSERT K` THEN
    ASM_SIMP_TAC[REAL_LEBESGUE_MEASURABLE_INTERVAL; REAL_NEGLIGIBLE_FINITE; FINITE_INSERT] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON] THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    EXPAND_TAC "e" THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. &2 / lam * ((l:real->real) s + &2 * s2 pow 2 * Rm))
    real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real->real) real_integrable_on real_interval[s1,s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\s. &2 / lam * ((l:real->real) s + &2 * s2 pow 2 * Rm)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s1,s2])
                (\s. &2 / lam * ((l:real->real) s + &2 * s2 pow 2 * Rm))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((e:real->real) s)` THEN
    REWRITE_TAC[REAL_ABS_LE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (l:real->real) s + &2 * s2 pow 2 * Rm`; `&2 / lam`;
                 `real_interval[s1,s2]`] REAL_INTEGRAL_LMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`l:real->real`; `\s:real. &2 * s2 pow 2 * Rm`; `real_interval[s1,s2]`]
                REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]);;

(* A derivative continuous on the open interval off K is bounded on the     *)
(* points of [s1,s2] at distance >= e from the points of K in [s1,s2]       *)
(* (a compact set; s1 and s2 are in K).                                      *)

let P2AK_DERIV_BOUND_AWAY = prove
 (`!(w:real^1->real^N) s1 s2 K e.
     s1 IN K /\ s2 IN K /\ &0 < e /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K) ==> w continuous (at (lift s)))
     ==> ?M. !s. s1 <= s /\ s <= s2 /\ ~(s IN K) /\
                 (!c. c IN K INTER real_interval[s1,s2] ==> e <= abs(s - c))
                 ==> norm(w(lift s)) <= M`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ss = interval[lift s1,lift s2] INTER
                   INTERS (IMAGE (\c. (:real^1) DIFF ball(lift c,e))
                                 (K INTER real_interval[s1,s2]))` THEN
  SUBGOAL_THEN `compact(Ss:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ss" THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CLOSED_INTERS THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2 /\ ~(s IN K) /\
        (!c. c IN K INTER real_interval[s1,s2] ==> e <= abs(s - c))
        ==> lift s IN Ss`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    EXPAND_TAC "Ss" THEN
    REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP; INTERS_IMAGE; IN_ELIM_THM;
                IN_DIFF; IN_UNIV; IN_BALL; DIST_LIFT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^1->real^N) continuous_on Ss` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `v:real^1` THEN EXPAND_TAC "Ss" THEN
    REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP; INTERS_IMAGE; IN_ELIM_THM;
                IN_DIFF; IN_UNIV; IN_BALL] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(drop v IN K)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `e:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL; LIFT_DROP; DIST_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `s1 < drop v /\ drop v < s2` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~(drop v = s1) /\ ~(drop v = s2)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^1->real^N`; `Ss:real^1->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `M:real`)) (concl th))) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Ss:real^1->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* The chart piece of a p2a_admx curve on [s1,s2] inside one region chart  *)
(* (time window (sa,sb) around [s1,s2]): a p2ak_sq curve with exceptional   *)
(* set K (finite, containing s1 and s2) and bad set the points of K in      *)
(* [s1,s2]; its Lagrangian integral is the L-length over [s1^2,s2^2]; with  *)
(* a lower metric bound lam and a curvature bound Rm on a set C containing *)
(* the piece, its energy is at most (2 / lam)(L + 2 s2^2 Rm (s2 - s1)).    *)

let P2AK_PIECE_SQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) W a' b' U (phi:A->real^N) s1 s2 sa sb C lam Rm.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> gamma(s pow 2) IN U INTER W /\ phi(gamma(s pow 2)) IN C) /\
     &0 < lam /\
     (!s y u. s1 <= s /\ s <= s2 /\ y IN C
              ==> lam * norm u pow 2 <=
                  u dot (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2) y ** u) /\
                  abs(lscalar (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) y) <= Rm)
     ==> ?K. s1 IN K /\ s2 IN K /\
             p2ak_sq (IMAGE phi (U INTER W)) s1 s2 (\v. phi(gamma(drop v pow 2)))
                     (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                     K (K INTER real_interval[s1,s2]) /\
             (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2)))
                    (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))))
             real_integrable_on real_interval[s1,s2] /\
             real_integral (real_interval[s1,s2])
               (\s. p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2)))
                      (vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))) =
             real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b) /\
             real_integral (real_interval[s1,s2])
               (\s. norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) pow 2)
             <= &2 / lam *
                (real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b) +
                 &2 * s2 pow 2 * Rm * (s2 - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`] P2AK_ADMX_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:real->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `sa:real`; `sb:real`; `K:real->bool`] P2AK_PIECE_INT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `s1:real`; `s2:real`; `K:real->bool`; `C:real^N->bool`; `lam:real`; `Rm:real`]
                P2AK_ENERGY_DOM) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    STRIP_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[p2ak_sq] THEN
  ASM_REWRITE_TAC[INTER_SUBSET; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AK_DERIV_BOUND_AWAY THEN ASM_SIMP_TAC[]]);;

