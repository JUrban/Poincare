(* ========================================================================= *)
(* Unit pc_rfa_smax1: the strong maximum principle for scalar supersolutions *)
(* on a connected manifold, no completeness (CLN Thm 6.54, MT Thm 4.16):     *)
(* RFA_STRONG_MAXP_SCALAR.  The local spreading lemma of pc_rfa_spread in    *)
(* charts, then the set of points where ff stays positive after t0 is open   *)
(* and closed.                                                               *)
(* ========================================================================= *)

needs "src/pc_rfa_spread.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The statement constant RFA_STRONG_MAXP_SCALAR_STATEMENT.                  *)
(* ========================================================================= *)

(* Strong maximum principle for scalar supersolutions (CLN Thm 6.54,        *)
(* MT Thm 4.16 / Prop 4.17), connected manifold, no completeness: a          *)
(* nonnegative u with du/dt >= Lap u + c u, c locally bounded, positive at   *)
(* (t0,x0) is positive at every later time.                                  *)

let RFA_STRONG_MAXP_SCALAR_STATEMENT = new_definition
 `RFA_STRONG_MAXP_SCALAR_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g:real->A->real^N^N) (ff:real->A->real) (c:real->A->real) t0 x0.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       connected_space top /\ a < b /\
       (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
       (!cc. cc IN atlas
             ==> smooth_map_on
                   (interval(lift a,lift b) PCROSS IMAGE (SND cc) (FST cc))
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas cc (g (drop(fstcart z))) (sndcart z))) /\
                 smooth_map_on
                   (interval(lift a,lift b) PCROSS IMAGE (SND cc) (FST cc))
                   (\z. lift(ff (drop(fstcart z)) (chart_inv cc (sndcart z))))) /\
       (!K t1 t2. compact_in top K /\ a < t1 /\ t2 < b
                  ==> ?B. !t x. t1 <= t /\ t <= t2 /\ x IN K ==> abs(c t x) <= B) /\
       (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= ff t x) /\
       (!t x. a < t /\ t < b /\ x IN topspace top
              ==> ?D. ((\s. ff s x) has_real_derivative D) (atreal t) /\
                      rfa_lap atlas (g t) (ff t) x + c t x * ff t x <= D) /\
       a < t0 /\ t0 < b /\ x0 IN topspace top /\ &0 < ff t0 x0
       ==> !t x. t0 < t /\ t < b /\ x IN topspace top ==> &0 < ff t x`;;


(* ========================================================================= *)
(* Chart independence of the Laplacian rfa_lap.                              *)
(* ========================================================================= *)

(* The Laplacian rfa_lap (computed in chart_at x) in any other chart.      *)

let RFA_LAP_CHART = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c /\
     (!cc. cc IN atlas
           ==> smooth_map_on (IMAGE (SND cc) (FST cc)) (\y. lift(f(chart_inv cc y))))
     ==> rfa_lap atlas g f x =
         llap (metric_local atlas c g) (\y. f(chart_inv c y)) (SND c x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "sm rm cat xc fsm" THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_lap] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) x` THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  MP_TAC(ISPEC `c0:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
         CHART_TRANS_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "civ") THEN DISCH_THEN(LABEL_TAC "ciu") THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) (U INTER V))
                             (metric_local atlas (V,psi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ASM_MESON_TAC[diffeomorphism_on];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
                 `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
                 `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                 `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                 `\y. (f:A->real) (chart_inv (V:A->bool,psi:A->real^N) y)`;
                 `(phi:A->real^N) x`] LLAP_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
      USE_THEN "fsm" (fun th ->
        MP_TAC(MATCH_MP th (ASSUME `(V:A->bool,psi:A->real^N) IN atlas`))) THEN
      REWRITE_TAC[FST; SND];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x) = psi x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi w) = psi w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN U /\ (w:A) IN V` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "civ" (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 th) (ASSUME `(w:A) IN V`)]) THEN
  USE_THEN "ciu" (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 th) (ASSUME `(w:A) IN U`)]));;


(* ========================================================================= *)
(* The bundled hypotheses and the spreading lemma in a chart.                *)
(* ========================================================================= *)

(* The hypotheses of the scalar strong maximum principle, bundled: a      *)
(* time-dependent metric and a nonnegative supersolution ff of             *)
(* dff/dt >= Lap ff + cf ff, jointly smooth in charts, cf locally bounded. *)

let rfa_ssup = new_definition
 `rfa_ssup (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
           (g:real->A->real^N^N) (ff:real->A->real) (cf:real->A->real) <=>
    smooth_manifold_atlas top atlas /\ a < b /\
    (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
    (!cc. cc IN atlas
          ==> smooth_map_on
                (interval(lift a,lift b) PCROSS IMAGE (SND cc) (FST cc))
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (metric_local atlas cc (g (drop(fstcart z))) (sndcart z))) /\
              smooth_map_on
                (interval(lift a,lift b) PCROSS IMAGE (SND cc) (FST cc))
                (\z. lift(ff (drop(fstcart z)) (chart_inv cc (sndcart z))))) /\
    (!K t1 t2. compact_in top K /\ a < t1 /\ t2 < b
               ==> ?B. !t x. t1 <= t /\ t <= t2 /\ x IN K ==> abs(cf t x) <= B) /\
    (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= ff t x) /\
    (!t x. a < t /\ t < b /\ x IN topspace top
           ==> ?D. ((\s. ff s x) has_real_derivative D) (atreal t) /\
                   rfa_lap atlas (g t) (ff t) x + cf t x * ff t x <= D)`;;

let RFA_SSUP_SLICE = prove
 (`!top atlas a b (g:real->A->real^N^N) ff cf t.
     rfa_ssup (top,atlas) a b g ff cf /\ a < t /\ t < b
     ==> !cc. cc IN atlas
              ==> smooth_map_on (IMAGE (SND cc) (FST cc))
                    (\y. lift(ff t (chart_inv cc y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_ssup] THEN STRIP_TAC THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum.
                   lift((ff:real->A->real) (drop(fstcart z)) (chart_inv cc (sndcart z)))`;
                 `a:real`; `b:real`; `IMAGE (SND(cc:(A->bool)#(A->real^N))) (FST cc)`;
                 `t:real`] RFA_SMOOTH_MAP_ON_SLICE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

let RFA_MFD_SPREAD = prove
 (`!top atlas a b (g:real->A->real^N^N) ff cf (U:A->bool) (phi:A->real^N) z0 R t1 t2.
     rfa_ssup (top,atlas) a b g ff cf /\
     (U,phi) IN atlas /\ z0 IN U /\ &0 < R /\
     cball(phi z0,R) SUBSET IMAGE phi U /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ &0 < ff t1 z0
     ==> !x. x IN U /\ phi x IN ball(phi z0,R) ==> &0 < ff t2 x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ss") (fun th ->
    STRIP_ASSUME_TAC th THEN ASSUME_TAC th)) THEN
  USE_THEN "ss" (fun th ->
    MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
      (zip ["sm";"ab";"rm";"csm";"cb";"fpos";"fsup"]
           (CONJUNCTS(REWRITE_RULE[rfa_ssup] th)))) THEN
  UNDISCH_THEN `(U:A->bool,phi:A->real^N) IN atlas /\ z0 IN U /\ &0 < R /\
                cball((phi:A->real^N) z0,R) SUBSET IMAGE phi U /\
                a < t1 /\ t1 < t2 /\ t2 < b /\ &0 < (ff:real->A->real) t1 z0`
    (K ALL_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `y0 = (phi:A->real^N) z0` THEN
  ABBREV_TAC `Om = IMAGE (phi:A->real^N) U` THEN
  (* chart-level data *)
  SUBGOAL_THEN
   `lrg_lsmooth Om a b (\t. metric_local atlas (U:A->bool,phi:A->real^N) ((g:real->A->real^N^N) t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[lrg_lsmooth] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
      EXPAND_TAC "Om" THEN ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    USE_THEN "csm" (MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    EXPAND_TAC "Om" THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS Om)
      (\w. lift((ff:real->A->real) (drop(fstcart w))
                (chart_inv (U:A->bool,phi:A->real^N) (sndcart w))))`
  ASSUME_TAC THENL
   [USE_THEN "csm" (MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    EXPAND_TAC "Om" THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top (IMAGE (chart_inv (U:A->bool,phi:A->real^N)) (cball(y0,R)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (Om:real^N->bool)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
      EXPAND_TAC "Om" THEN MATCH_MP_TAC GRGD_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cb" (MP_TAC o SPECL
   [`IMAGE (chart_inv (U:A->bool,phi:A->real^N)) (cball(y0,R))`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "Bb")) THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ rho < R /\
          !z. z IN ball(y0,rho)
              ==> (ff:real->A->real) t1 z0 / &2 <= ff t1 (chart_inv (U:A->bool,phi:A->real^N) z)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `ff:real->A->real`; `cf:real->A->real`;
                   `t1:real`] RFA_SSUP_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\y. lift((ff:real->A->real) t1 (chart_inv (U:A->bool,phi:A->real^N) y)))
      continuous at y0`
    MP_TAC THENL
     [SUBGOAL_THEN `(y0:real^N) IN Om` ASSUME_TAC THENL
       [ASM SET_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]; ALL_TAC] THEN
      UNDISCH_TAC `smooth_map_on Om
        (\y. lift((ff:real->A->real) t1 (chart_inv (U:A->bool,phi:A->real^N) y)))` THEN
      DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `(ff:real->A->real) t1 z0 / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (R / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) y0 = z0` SUBST1_TAC THENL
     [EXPAND_TAC "y0" THEN USE_THEN "ci1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`;
                 `\t. metric_local atlas (U:A->bool,phi:A->real^N) ((g:real->A->real^N^N) t)`;
                 `\t z. (ff:real->A->real) t (chart_inv (U:A->bool,phi:A->real^N) z)`;
                 `B:real`; `y0:real^N`; `rho:real`; `R:real`; `t1:real`; `t2:real`;
                 `(ff:real->A->real) t1 z0 / &2`] RFA_SPREAD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      USE_THEN "fpos" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^N) IN Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x = chart_inv (U:A->bool,phi:A->real^N) z` THEN
    SUBGOAL_THEN `(x:A) IN U /\ (phi:A->real^N) x = z` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN USE_THEN "ci2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "fsup" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`; `(ff:real->A->real) t`;
                   `(U:A->bool,phi:A->real^N)`; `x:A`] RFA_LAP_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FST] THEN CONJ_TAC THENL
       [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RFA_SSUP_SLICE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`;
                            `g:real->A->real^N^N`; `cf:real->A->real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SND] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((cf:real->A->real) t x) <= B` ASSUME_TAC THENL
     [USE_THEN "Bb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "x" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (ff:real->A->real) t x` ASSUME_TAC THENL
     [USE_THEN "fpos" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `--B * (ff:real->A->real) t x <= cf t x * ff t x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `llap (metric_local atlas (U:A->bool,phi:A->real^N) ((g:real->A->real^N^N) t))
           (\z. (ff:real->A->real) t (chart_inv (U,phi) z)) z =
      rfa_lap atlas (g t) (ff t) x`
    SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfa_lap atlas ((g:real->A->real^N^N) t) ((ff:real->A->real) t) x +
                 (cf:real->A->real) t x * ff t x <= D` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ci1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN U`)]));;


(* ========================================================================= *)
(* Local neighbourhoods and the connectedness argument.                      *)
(* ========================================================================= *)

(* Around every point there is an open set N such that positivity of ff  *)
(* at one point of N at some time gives positivity on all of N at every   *)
(* later time.                                                            *)

let RFA_SSUP_LOCAL = prove
 (`!top atlas a b (g:real->A->real^N^N) ff cf x.
     rfa_ssup (top,atlas) a b g ff cf /\ x IN topspace top
     ==> ?N. open_in top N /\ x IN N /\ N SUBSET topspace top /\
             !z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                          &0 < ff t1 z
                          ==> &0 < ff t2 z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfa_ssup]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?R. &0 < R /\ cball((phi:A->real^N) x,R) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (phi:A->real^N) U)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{z | z IN U /\ (phi:A->real^N) z IN ball(phi x,R / &3)}` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{z | z IN U /\ (phi:A->real^N) z IN ball(phi x,R / &3)} =
      {z | z IN topspace(subtopology top U) /\
           phi z IN IMAGE phi U INTER ball(phi x,R / &3)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN
      SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
      MP_TAC(ISPECL [`phi:A->real^N`; `U:A->bool`; `z:A`] FUN_IN_IMAGE) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CONTINUOUS_MAP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `z':A`; `t1:real`; `t2:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `ff:real->A->real`; `cf:real->A->real`;
                 `U:A->bool`; `phi:A->real^N`; `z:A`; `&2 * R / &3`; `t1:real`; `t2:real`]
         RFA_MFD_SPREAD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) x,R)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`(phi:A->real^N) x`; `(phi:A->real^N) z`; `w:real^N`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN
  MP_TAC(ISPECL [`(phi:A->real^N) z`; `(phi:A->real^N) x`; `(phi:A->real^N) z'`]
         DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(phi:A->real^N) z`; `(phi:A->real^N) x`] DIST_SYM) THEN
  ASM_REAL_ARITH_TAC);;

(* The strong maximum principle (CLN Thm 6.54, MT Thm 4.16): the set of   *)
(* points where ff stays positive at all times after t0 is open and       *)
(* closed and contains x0.                                                *)

let RFA_STRONG_MAXP_SCALAR = prove
 (`!(u:A->bool) (n:N->bool). RFA_STRONG_MAXP_SCALAR_STATEMENT u n`,
  REWRITE_TAC[RFA_STRONG_MAXP_SCALAR_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfa_ssup (top,atlas) a b (g:real->A->real^N^N) ff c` ASSUME_TAC THENL
   [REWRITE_TAC[rfa_ssup] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?N. open_in top N /\ x IN N /\ N SUBSET topspace top /\
                !z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                             &0 < (ff:real->A->real) t1 z
                             ==> &0 < ff t2 z'`
  (LABEL_TAC "loc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SSUP_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `g:real->A->real^N^N`; `c:real->A->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x:A | x IN topspace top /\
                         !t. t0 < t /\ t < b ==> &0 < (ff:real->A->real) t x}` THEN
  SUBGOAL_THEN
   `!x N. x IN topspace top /\ open_in top N /\ x IN N /\ N SUBSET topspace top /\
          (!z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                        &0 < (ff:real->A->real) t1 z
                        ==> &0 < ff t2 z') /\
          ~(N INTER S = {})
          ==> N SUBSET S`
  (LABEL_TAC "spread") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "nn") MP_TAC))))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z':A` THEN DISCH_TAC THEN
    UNDISCH_TAC `(z:A) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "nn" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `(t0 + t) / &2`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x0:A`; `t0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (S:A->bool) /\ closed_in top S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "spread" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `N INTER (S:A->bool) = {}` THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `N SUBSET (S:A->bool)` MP_TAC THENL
     [USE_THEN "spread" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `S = topspace top:A->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `connected_space (top:A topology)` THEN
    REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN(MP_TAC o SPEC `S:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN S` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

