(* ========================================================================= *)
(* pc_p2a_lconv: the L-integrand of an arbitrary curve in a region chart     *)
(* (for the regularity of minimizers, L2, and corner smoothing, L12).  The   *)
(* lemmas P2A_LGEOD_SLICE_VEL, P2A_LSINT_CHART and P2A_LINT_SINT of          *)
(* pc_p2a_lgeo2/3 assume p2a_Lgeod only for continuity, topspace membership  *)
(* and the existence of velocities; here those are hypotheses, so the        *)
(* identities hold for any curve with a velocity in a region chart.          *)
(*                                                                           *)
(* First: velocities in slice charts and the s-form of the integrand.        *)
(* ========================================================================= *)

needs "src/pc_p2a_lext.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_SLICE_VEL_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b s0 W1 a1 b1 U1 (phi1:A->real^N) A1 (c0:(A->bool)#(A->real^N)).
     &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     p2a_region V W1 a1 b1 /\ (U1,phi1) IN p2a_vatlas V b1 /\
     a1 < tt - s0 pow 2 /\ tt - s0 pow 2 <= b1 /\ gamma(s0 pow 2) IN U1 INTER W1 /\
     (!O. open_in (p2a_vtop V (tt - s0 pow 2)) O /\ gamma(s0 pow 2) IN O
          ==> ?e. &0 < e /\
                  !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s0) < e ==> gamma(r pow 2) IN O) /\
     ((\v. phi1(gamma(drop v pow 2))) has_vector_derivative A1)
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
     c0 IN p2a_vatlas V (tt - s0 pow 2) /\ gamma(s0 pow 2) IN FST c0
     ==> ((\v. SND c0 (gamma(drop v pow 2))) has_vector_derivative
          frechet_derivative (chart_trans (U1 INTER W1,phi1) c0)
                             (at (phi1(gamma(s0 pow 2)))) A1)
         (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) t0`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) t0`; `c0:(A->bool)#(A->real^N)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) t0)
                        (FST(c0:(A->bool)#(A->real^N)) INTER (U1 INTER W1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W1:A->bool`; `a1:real`; `b1:real`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `(U1:A->bool,phi1:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `FST(c0:(A->bool)#(A->real^N)) INTER (U1 INTER W1)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) c0 o
     (\v:real^1. phi1((gamma:real->A)(drop v pow 2)))`; `e1:real`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; chart_trans; SND] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)(drop v pow 2) IN U1 INTER W1` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(v:real^1,lift s0) < e1` THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
        SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`;
                   `(gamma:real->A)(drop v pow 2)`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER FST(c0:(A->bool)#(A->real^N)))`;
    `IMAGE (SND(c0:(A->bool)#(A->real^N))) ((U1 INTER W1) INTER FST c0)`;
    `chart_trans (c0:(A->bool)#(A->real^N)) (U1 INTER W1,phi1)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SLICE_CHART THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)`; `a1:real`; `b1:real`; `t0:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]]);;

let P2A_LSINT_CHART_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ &0 < b /\ &0 <= s /\ s pow 2 <= b /\
     (!O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
          ==> ?e. &0 < e /\
                  !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O) /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> p2a_lsint V tt gamma b s =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2))) A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W) INTER FST(c':(A->bool)#(A->real^N))` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "r")) (concl th))) THEN
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

let P2A_LINT_SINT_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s.
     p2a_svs V /\ &0 < b /\ &0 < s /\ s pow 2 <= b /\
     gamma(s pow 2) IN topspace(p2a_vtop V (tt - s pow 2)) /\
     (?w. ((\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma(s pow 2)))
                   (gamma(drop v pow 2))) has_vector_derivative w)
            (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}))
     ==> &2 * s * p2a_L_integrand V tt gamma b (s pow 2) = p2a_lsint V tt gamma b s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ sqrt(s pow 2) = s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN

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

(* The combined identity: the s-form of the L-integrand of any curve with a  *)
(* velocity in a region chart (no p2a_Lgeod needed).                         *)

let P2A_LINT_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ &0 < b /\ &0 < s /\ s pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     (!O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
          ==> ?e. &0 < e /\
                  !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> &2 * s * p2a_L_integrand V tt gamma b (s pow 2) =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2))) A`,
  REPEAT STRIP_TAC THEN
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
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`]
                P2A_LINT_SINT_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `frechet_derivative
                  (chart_trans (U INTER W:A->bool,phi:A->real^N)
                     (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                              (real->A->real^N^N)) (tt - s pow 2))
                               ((gamma:real->A)(s pow 2))))
                  (at (phi(gamma(s pow 2)))) (A:real^N)` THEN
    MATCH_MP_TAC P2A_SLICE_VEL_GEN THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)`; `tt:real`; `a':real`; `b':real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2A_LSINT_CHART_GEN THEN EXISTS_TAC `a':real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* The metric families of a region chart (time and s-families; the Ricci     *)
(* flow), and the L-length of a piece of a curve as the chart L-functional   *)
(* p2a_cL of its region chart curve, for chart curves that are C^1 off a     *)
(* finite set with bounded derivative.                                       *)
(* ========================================================================= *)

let P2A_REGION_RCHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W b U (phi:A->real^N).
     (U,phi) IN p2a_vatlas V b ==> (U INTER W,phi) IN restrict_atlas (p2a_vatlas V b) W`,
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN MESON_TAC[]);;

let P2A_REGION_SFAMILY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b U (phi:A->real^N) tt sa sb.
     p2a_region V W a b /\ (U,phi) IN p2a_vatlas V b /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> a < tt - s pow 2 /\ tt - s pow 2 <= b)
     ==> p2a_lsmooth (IMAGE phi (U INTER W)) sa sb
                     (\s. p2a_rlocal V W b (U INTER W,phi) (tt - s pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b) W`;
    `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b) W`;
    `a:real`; `b:real`; `p2a_rmetric (V:(real->A topology)#
                             (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b`;
    `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `sa:real`; `sb:real`]
   P2A_UPTO_SFAMILY) THEN
  REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[P2A_REGION_RCHART] THEN
  UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) W a b` THEN
  SIMP_TAC[p2a_region]);;

let P2A_REGION_LRICCI = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b U (phi:A->real^N).
     p2a_region V W a b /\ (U,phi) IN p2a_vatlas V b
     ==> lricci_flow (IMAGE phi (U INTER W)) a b (p2a_rlocal V W b (U INTER W,phi)) /\
         p2a_lsmooth (IMAGE phi (U INTER W)) a b (p2a_rlocal V W b (U INTER W,phi))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b) W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b) W`;
      `a:real`; `b:real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b`;
      `(U INTER W:A->bool,phi:A->real^N)`] LRG_RICCI_FLOW_ON_CHART) THEN
    REWRITE_TAC[FST; SND] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[P2A_REGION_RCHART] THEN
      UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W a b` THEN
      SIMP_TAC[p2a_region; p2a_flow_upto];
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; p2a_rlocal]];
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
    ASM_REWRITE_TAC[p2a_lsmooth]]);;

(* The L-length of a piece.                                                  *)

let P2A_LINT_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b s1 s2 W a' b' U (phi:A->real^N) K sa sb M.
     p2a_svs V /\ &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!s. s1 <= s /\ s <= s2 ==> gamma(s pow 2) IN U INTER W) /\
     (!s O. s1 < s /\ s < s2 /\ open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
            ==> ?e. &0 < e /\
                    !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O) /\
     FINITE K /\
     (\v. phi(gamma(drop v pow 2))) continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift s)) /\
              norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) <= M)
     ==> (p2a_L_integrand V tt gamma b has_real_integral
          p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt (\v. phi(gamma(drop v pow 2))) s1 s2)
         (real_interval[s1 pow 2,s2 pow 2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))` THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `s2 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb
                            (\s. (Gt:real->real^N->real^N^N)(tt - s pow 2))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN MATCH_MP_TAC P2A_REGION_SFAMILY THEN
    EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (Y:real^1->real^N)(lift s) IN IMAGE (phi:A->real^N) (U INTER W)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the s-integrand *)
  ABBREV_TAC `Fs = \s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                               (vector_derivative Y (at (lift s)))` THEN
  SUBGOAL_THEN `(Fs:real->real) real_integrable_on real_interval[s1,s2]` ASSUME_TAC THENL
   [ABBREV_TAC `z' = \x:real^1. if s1 < drop x /\ drop x < s2 /\ ~(drop x IN K)
                                then vector_derivative (Y:real^1->real^N) (at x) else vec 0` THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb:real`;
                   `Gt:real->real^N->real^N^N`; `tt:real`; `Y:real^1->real^N`;
                   `z':real^1->real^N`; `K:real->bool`; `s1:real`; `s2:real`; `abs M`]
                  P2A_LLAG_PW_INTEGRABLE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "z'" THEN
        ASM_REWRITE_TAC[LIFT_DROP; GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_MESON_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "z'" THEN REWRITE_TAC[LIFT_DROP] THEN
        COND_CASES_TAC THEN REWRITE_TAC[NORM_0; REAL_ABS_POS] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs m`) THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SPIKE THEN
    EXISTS_TAC `(s1:real) INSERT s2 INSERT K` THEN
    ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT] THEN
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "Fs" THEN EXPAND_TAC "z'" THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `s1 < s /\ s < s2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* continuity of the s-integrand off K *)
  SUBGOAL_THEN `!s. s1 < s /\ s < s2 /\ ~(s IN K) ==> (Fs:real->real) real_continuous atreal s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
    SUBGOAL_THEN
     `lift o (Fs:real->real) o drop =
      (\z. lift(p2a_llag (Gt:real->real^N->real^N^N) tt (drop(fstcart z)) (fstcart(sndcart z))
                         (sndcart(sndcart z)))) o
      (\v. pastecart v (pastecart ((Y:real^1->real^N) v) (vector_derivative Y (at v))))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fs" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      MATCH_MP_TAC CONTINUOUS_PASTECART THEN ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\z. lift(p2a_llag (Gt:real->real^N->real^N^N) tt (drop(fstcart z)) (fstcart(sndcart z))
                          (sndcart(sndcart z)))`;
      `interval(lift sa,lift sb) PCROSS (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`]
     CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_UNIV] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* substitution tau = s^2 *)
  SUBGOAL_THEN `s1 pow 2 <= s2 pow 2 /\ s1 <= s2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fs:real->real`; `sqrt`; `\x. inv(&2 * sqrt x)`; `s1 pow 2`; `s2 pow 2`;
                 `s1:real`; `s2:real`;
                 `IMAGE (\s:real. s pow 2) K UNION {s1 pow 2,s2 pow 2}`]
                HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
  SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COUNTABLE_UNION] THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; FINITE_IMP_COUNTABLE; FINITE_INSERT; FINITE_EMPTY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:real` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL;
                  DE_MORGAN_THM; NOT_EXISTS_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&0 < y /\ s1 < sqrt y /\ sqrt y < s2 /\ ~(sqrt y IN K)`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `s1 pow 2 < y /\ y < s2 pow 2` STRIP_ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s1 pow 2` THEN
          ASM_REWRITE_TAC[REAL_LE_POW_2];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(s1 pow 2)` THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[REAL_LE_REFL];
            MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(s2 pow 2)` THEN CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
          DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `sqrt y` o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `K:real->bool`)) (concl th) &&
            can (find_term ((=) `y:real`)) (concl th))) THEN
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_cL] THEN
  SUBGOAL_THEN
   `(\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                  (vector_derivative Y (at (lift s)))) = Fs`
  SUBST1_TAC THENL [EXPAND_TAC "Fs" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC] HAS_REAL_INTEGRAL_SPIKE)) THEN
  EXISTS_TAC `IMAGE (\s:real. s pow 2) K UNION {s1 pow 2,s2 pow 2}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN REWRITE_TAC[COUNTABLE_UNION] THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FINITE_IMP_COUNTABLE; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL;
              DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s1 pow 2 < y /\ y < s2 pow 2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s1 pow 2` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt y` THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 < s /\ s < s2 /\ ~(s IN K)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(s <= s1) ==> s1 < s`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `s pow 2 <= s1 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `~(s2 <= s) ==> s < s2`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `s2 pow 2 <= s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K:real->bool`)) (concl th) &&
        can (find_term ((=) `y:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(s:real) pow 2 = y`)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXPAND_TAC "Fs" THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `vector_derivative (Y:real^1->real^N) (at (lift s))`] P2A_LINT_REGION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s2 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b':real`)) (concl th) &&
        can (find_term ((=) `sa:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b':real`)) (concl th) &&
        can (find_term ((=) `sa:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) = (Y:real^1->real^N)(lift s)`
  SUBST1_TAC THENL [EXPAND_TAC "Y" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

