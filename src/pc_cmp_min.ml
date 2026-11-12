(* ========================================================================= *)
(* Unit pc_cmp_min (comparison-geometry layer CMP): minimizing curves and    *)
(* minimizing geodesics.  The no-corner lemma MFD_MINIMIZING_IMP_GEODESIC (a *)
(* C^1 constant-speed minimizer is a geodesic) by local radiality inside     *)
(* uniformly normal neighbourhoods (MFD_UNIFORMLY_NORMAL,                    *)
(* MFD_EXP_DIST_EQUALITY) and gluing (GEOM_GEODESIC_GLUE).  S5               *)
(* (MT Prop 1.20) is proved in pc_cmp_mgeo.                                  *)
(* ========================================================================= *)

needs "src/pc_cmp_index.ml";;
needs "src/pc_geo_hr.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Subarcs of a minimizing C^1 curve are minimizing.                         *)
(* ========================================================================= *)

let CMPM_SUBARC_MIN = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b p q.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\
        mfd_length atlas g gamma a b = mfd_dist (top,atlas) g (gamma a) (gamma b) /\
        a <= p /\ p <= q /\ q <= b
        ==> mfd_c1_curve (top,atlas) gamma p q /\
            mfd_joinable (top,atlas) (gamma p) (gamma q) /\
            mfd_dist (top,atlas) g (gamma p) (gamma q) = mfd_length atlas g gamma p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p <= b /\ a <= q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `p:real`; `b:real`]
    MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `p:real`; `q:real`; `b:real`]
    MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) a) (gamma p) /\
    mfd_joinable (top,atlas) (gamma p) (gamma q) /\
    mfd_joinable (top,atlas) (gamma q) (gamma b)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CMPI_C1_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (u,v) ->
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; u; v] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [(`a:real`,`p:real`); (`p:real`,`q:real`); (`q:real`,`b:real`)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) p`; `(gamma:real->A) q`;
                 `(gamma:real->A) b`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) a`; `(gamma:real->A) p`;
                 `(gamma:real->A) b`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((gamma:real->A) p) (gamma b)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) q` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* A short arc of a constant-speed minimizer, starting at a                  *)
(* point with an injectivity ball containing it, is the radial geodesic.     *)
(* ========================================================================= *)

let CMPM_ARC_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t1 t2 r c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\
        mfd_length atlas g gamma a b = mfd_dist (top,atlas) g (gamma a) (gamma b) /\
        (!t. t IN real_interval[a,b] ==> mfd_speed atlas g gamma a b t = c) /\
        a <= t1 /\ t1 < t2 /\ t2 <= b /\
        mfd_inj_ball (top,atlas) g (gamma t1) r /\ c * (t2 - t1) < r
        ==> ?w. mfd_tnorm g (gamma t1) w = c * (t2 - t1) /\
                (!s. &0 <= s /\ s <= &1
                     ==> s % w IN mfd_exp_dom (top,atlas) g (gamma t1)) /\
                !s. &0 <= s /\ s <= &1
                    ==> gamma(t1 + (t2 - t1) * s) =
                        mfd_exp (top,atlas) g (gamma t1) (s % w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!q. t1 <= q /\ q <= t2
        ==> mfd_joinable (top,atlas) ((gamma:real->A) t1) (gamma q) /\
            mfd_dist (top,atlas) (g:A->real^N^N) (gamma t1) (gamma q) = c * (q - t1)`
  (LABEL_TAC "dq") THENL
   [X_GEN_TAC `q:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t1:real`;
                   `q:real`] CMPM_SUBARC_MIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t1:real`;
                   `q:real`] GRGD_LENGTH_SUBINTERVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[t1,q]) (\t:real. c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b`))
            (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "dq" (MP_TAC o SPEC `t2:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t2 IN mfd_ball (top,atlas) (g:A->real^N^N) (gamma t1) r`
  MP_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`; `r:real`] MFD_EXP_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE; mfd_tball; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`; `r:real`; `w:real^N`]
    MFD_EXP_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t1) w = c * (t2 - t1)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(gamma:real->A) t2 =
                 mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                   (gamma t1) (w:real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `mfd_inj_ball (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) r`) THEN
  REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * (t2 - t1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real^N`
      (ASSUME `!v. &0 <= mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t1) v`)) THEN
    REWRITE_TAC[ASSUME `mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t1) w =
                        c * (t2 - t1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= &1
                    ==> s % w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) /\
                        mfd_tnorm g (gamma t1) (s % w) = s * c * (t2 - t1) /\
                        mfd_tnorm g (gamma t1) (s % w) < r`
  (LABEL_TAC "sw") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t1) (s % w) =
                  s * c * (t2 - t1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
      ALL_TAC] THEN
    SUBGOAL_THEN `s * c * (t2 - t1) <= c * (t2 - t1)` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t1) (s % w) < r`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                  check (is_binary "SUBSET" o concl)) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "sw" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t1:real`;
                 `t2:real`] CMPM_SUBARC_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_AFFINE_CURVE o
    check (fun th -> concl th = `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                                   (gamma:real->A) t1 t2`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `t1:real`; `t2:real`]
    GRGD_AFFINE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`; `r:real`; `w:real^N`;
                 `(gamma:real->A) o (\x. t1 + (t2 - t1) * x)`] MFD_EXP_DIST_EQUALITY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) (gamma t2) =
                 mfd_length atlas g gamma t1 t2` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "eq") THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "eq" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[o_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s' % (w:real^N) = s % w` (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "dq" (MP_TAC o SPEC `t1 + (t2 - t1) * s`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> t1 <= t1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= (t2 - t1) * &1 ==> t1 + x <= t2`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "sw" (MP_TAC o SPEC `s':real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`; `r:real`; `s' % (w:real^N)`]
    MFD_EXP_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s' * c * (t2 - t1) = s * c * (t2 - t1)` MP_TAC THENL
   [UNDISCH_TAC `c * ((t1 + (t2 - t1) * s) - t1) = s' * c * (t2 - t1)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `c * (t2 - t1) = &0` THENL
   [SUBGOAL_THEN `w:real^N = vec 0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t1`; `w:real^N`] GEOD_TNORM_EQ_0) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL]);;

(* ========================================================================= *)
(* Local geodesic pieces of a constant-speed minimizer.                      *)
(* ========================================================================= *)

(* A union of real intervals, each meeting a fixed interval that the union  *)
(* covers, is an interval.                                                   *)

let CMPM_UNIONS_REALINTERVAL = prove
 (`!(fam:(real->bool)->bool) (s:real->bool).
        is_realinterval s /\ s SUBSET UNIONS fam /\
        (!k. k IN fam ==> is_realinterval k /\ ~(k INTER s = {}))
        ==> is_realinterval(UNIONS fam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [is_realinterval] THEN REWRITE_TAC[IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k1:real->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k2:real->bool` STRIP_ASSUME_TAC)
                     STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `k1:real->bool` th) THEN
                          MP_TAC(SPEC `k2:real->bool` th)) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; is_realinterval] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i2")
    (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1")
    (X_CHOOSE_THEN `p:real` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `z <= p` THENL
   [EXISTS_TAC `k1:real->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "i1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `p:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `q <= z` THENL
   [EXISTS_TAC `k2:real->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "i2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`q:real`; `y:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real) IN s` MP_TAC THENL
   [UNDISCH_TAC `is_realinterval (s:real->bool)` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(s:real->bool) SUBSET UNIONS fam` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[]);;

(* Continuity of a curve on [a,b] at a point, in neighbourhood form.         *)

let CMPM_CONT_NEAR = prove
 (`!top (gamma:real->A) a b (w:A->bool) t0.
        continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
        open_in top w /\ t0 IN real_interval[a,b] /\ gamma t0 IN w
        ==> ?e. &0 < e /\
                !t. t IN real_interval[a,b] /\ abs(t - t0) < e ==> gamma t IN w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`gamma:real->A`; `subtopology euclideanreal (real_interval[a,b])`;
                 `top:A topology`; `w:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t0:real) IN u` MP_TAC THENL
   [UNDISCH_TAC `{x | x IN real_interval[a,b] /\ (gamma:real->A) x IN w} =
                 u INTER real_interval[a,b]` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in euclideanreal (u:real->bool)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `{x | x IN real_interval[a,b] /\ (gamma:real->A) x IN w} =
               u INTER real_interval[a,b]` THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Around each parameter t0 of a constant-speed minimizer there is a        *)
(* subinterval [t1,t2] (with t0 interior relative to [a,b]) on which the   *)
(* curve agrees with a geodesic defined on an open interval containing      *)
(* [t1,t2]: an affinely reparametrized radial geodesic.                      *)

let CMPM_LOCAL_PIECE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b c t0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
        mfd_length atlas g gamma a b = mfd_dist (top,atlas) g (gamma a) (gamma b) /\
        (!t. t IN real_interval[a,b] ==> mfd_speed atlas g gamma a b t = c) /\
        t0 IN real_interval[a,b]
        ==> ?t1 t2 K (G:real->A).
              a <= t1 /\ t1 <= t0 /\ t0 <= t2 /\ t2 <= b /\ t1 < t2 /\
              (a < t0 ==> t1 < t0) /\ (t0 < b ==> t0 < t2) /\
              mfd_geodesic (top,atlas) g G K /\ real_interval[t1,t2] SUBSET K /\
              !t. t IN real_interval[t1,t2] ==> G t = gamma t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                  (gamma:real->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (gamma:real->A) t IN topspace top`
  (LABEL_TAC "intop") THENL
   [MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[a,b])`; `top:A topology`;
                   `gamma:real->A`] CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t0`] MFD_UNIFORMLY_NORMAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "intop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `r:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `a:real`; `b:real`; `W:A->bool`;
                 `t0:real`] CMPM_CONT_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN `?e. &0 < e /\ e < eta /\ (abs c + &1) * (&2 * e) <= r`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * (abs c + &1)` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r / (&2 * (abs c + &1))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    EXISTS_TAC `min (eta / &2) (r / (&2 * (abs c + &1)))` THEN
    SUBGOAL_THEN `min (eta / &2) (r / (&2 * (abs c + &1))) <= r / (&2 * (abs c + &1))`
    MP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `min (eta / &2) (r / (&2 * (abs c + &1))) * &2 * (abs c + &1) <= r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t1 = max a (t0 - e)` THEN
  ABBREV_TAC `t2 = min b (t0 + e)` THEN
  SUBGOAL_THEN `a <= t1 /\ t1 <= t0 /\ t0 <= t2 /\ t2 <= b /\ t1 < t2 /\
                (a < t0 ==> t1 < t0) /\ (t0 < b ==> t0 < t2) /\
                abs(t1 - t0) < eta /\ t2 - t1 <= &2 * e`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN
    MAP_EVERY UNDISCH_TAC [`a < b`; `&0 < e`; `e < eta`;
                           `t0 IN real_interval[a,b]`] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `t1:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPEC `(gamma:real->A) t1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN topspace top` ASSUME_TAC THENL
   [USE_THEN "intop" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t1:real`;
                 `t2:real`; `r:real`; `c:real`] CMPM_ARC_RADIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs c * (t2 - t1)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(abs c + &1) * (&2 * e)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(abs c + &1) * (t2 - t1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dom") (LABEL_TAC "rad")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t1`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) w`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) w`;
                 `inv(t2 - t1)`; `--(t1 * inv(t2 - t1))`] MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[t1,t2]
        ==> &0 <= inv(t2 - t1) * t + --(t1 * inv(t2 - t1)) /\
            inv(t2 - t1) * t + --(t1 * inv(t2 - t1)) <= &1 /\
            t1 + (t2 - t1) * (inv(t2 - t1) * t + --(t1 * inv(t2 - t1))) = t`
  (LABEL_TAC "aff") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv(t2 - t1) * t + --(t1 * inv(t2 - t1)) = (t - t1) / (t2 - t1)`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t2 - t1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[t1,t2]
        ==> inv(t2 - t1) * t + --(t1 * inv(t2 - t1)) IN
              mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) w /\
            mfd_geo (top,atlas) g (gamma t1) w
              (inv(t2 - t1) * t + --(t1 * inv(t2 - t1))) = gamma t`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "aff" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `t IN real_interval[t1,t2]`))) THEN
    ABBREV_TAC `s = inv(t2 - t1) * t + --(t1 * inv(t2 - t1))` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `s % w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1)`
    ASSUME_TAC THENL
     [USE_THEN "dom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME `t1 + (t2 - t1) * s = t`)) THEN
    USE_THEN "rad" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `&0 <= s`) (ASSUME `s <= &1`))]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t1`; `w:real^N`; `s:real`]
      MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`t1:real`; `t2:real`;
    `{t | inv(t2 - t1) * t + --(t1 * inv(t2 - t1)) IN
          mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) w}`;
    `\t. mfd_geo (top,atlas) (g:A->real^N^N) ((gamma:real->A) t1) w
           (inv(t2 - t1) * t + --(t1 * inv(t2 - t1)))`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN USE_THEN "key" (fun th -> MESON_TAC[th]);
    USE_THEN "key" (fun th -> MESON_TAC[th])]);;

(* ========================================================================= *)
(* A constant-speed minimizer is a geodesic (no corners): the lemma          *)
(* MFD_MINIMIZING_IMP_GEODESIC of the geodesic interface pc_geo_iface.       *)
(* ========================================================================= *)

(* Cutting a geodesic piece down to a window (lo,hi) around t0.             *)

let CMPM_GEODESIC_WINDOW = prove
 (`!top atlas (g:A->real^N^N) (G':real->A) (G:real->A) K lo hi t0.
        mfd_geodesic (top,atlas) g G' K /\ t0 IN K /\ lo < t0 /\ t0 < hi /\
        (!t. t IN K /\ lo < t /\ t < hi ==> G' t = G t)
        ==> t0 IN K INTER real_interval(lo,hi) /\
            is_realinterval (K INTER real_interval(lo,hi)) /\
            real_open (K INTER real_interval(lo,hi)) /\
            mfd_geodesic (top,atlas) g G' (K INTER real_interval(lo,hi)) /\
            !t. t IN K INTER real_interval(lo,hi) ==> G' t = G t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_realinterval (K:real->bool) /\ real_open K` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N) (G':real->A) K` THEN
    REWRITE_TAC[mfd_geodesic] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_realinterval (K INTER real_interval(lo,hi)) /\
                real_open (K INTER real_interval(lo,hi))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IS_REALINTERVAL_INTER; IS_REALINTERVAL_INTERVAL; REAL_OPEN_INTER;
                 REAL_OPEN_REAL_INTERVAL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `K:real->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]]);;

(* A constant-speed minimizer is (the restriction of) a geodesic: glue the  *)
(* local radial pieces (CMPM_LOCAL_PIECE) with GEOM_GEODESIC_GLUE, using    *)
(* the end pieces to extend the curve past a and b.                         *)

let MFD_MINIMIZING_IMP_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
        mfd_length atlas g gamma a b = mfd_dist (top,atlas) g (gamma a) (gamma b) /\
        (!t. t IN real_interval[a,b]
             ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a))
        ==> ?J gamma'. mfd_geodesic (top,atlas) g gamma' J /\
                       real_interval[a,b] SUBSET J /\
                       !t. t IN real_interval[a,b] ==> gamma' t = gamma t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b / (b - a)`;
                 `a:real`] CMPM_LOCAL_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_REFL; ASSUME `a < b`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real` (X_CHOOSE_THEN `p2:real`
    (X_CHOOSE_THEN `KA:real->bool` (X_CHOOSE_THEN `GA:real->A`
      (fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "ga" (last(CONJUNCTS th))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b / (b - a)`;
                 `b:real`] CMPM_LOCAL_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_REFL; ASSUME `a < b`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real` (X_CHOOSE_THEN `q2:real`
    (X_CHOOSE_THEN `KB:real->bool` (X_CHOOSE_THEN `GB:real->A`
      (fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "gb" (last(CONJUNCTS th))))))) THEN
  ABBREV_TAC `G = \t. if t < a then (GA:real->A) t
                      else if b < t then (GB:real->A) t else gamma t` THEN
  ABBREV_TAC
   `fam = {K | is_realinterval K /\ real_open K /\
               ~(K INTER real_interval[a,b] = {}) /\
               ?G'. mfd_geodesic (top,atlas) (g:A->real^N^N) G' K /\
                    !t. t IN K ==> G' t = (G:real->A) t}` THEN
  SUBGOAL_THEN `!t0. t0 IN real_interval[a,b] ==> ?K. K IN fam /\ t0 IN K`
  (LABEL_TAC "cover") THENL
   [X_GEN_TAC `t0:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!K0 G' lo hi.
        mfd_geodesic (top,atlas) (g:A->real^N^N) G' K0 /\ t0 IN K0 /\
        lo < t0 /\ t0 < hi /\
        (!t. t IN K0 /\ lo < t /\ t < hi ==> G' t = (G:real->A) t)
        ==> ?K. K IN fam /\ t0 IN K`
    (LABEL_TAC "win") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `G':real->A`; `G:real->A`; `K0:real->bool`;
                     `lo:real`; `hi:real`; `t0:real`] CMPM_GEODESIC_WINDOW) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXISTS_TAC `K0 INTER real_interval(lo,hi)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "fam" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `t0:real` THEN
        ASM_REWRITE_TAC[IN_INTER];
        EXISTS_TAC `G':real->A` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `t0:real = a` THENL
     [USE_THEN "win" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`KA:real->bool`; `GA:real->A`; `a - &1`; `p2:real`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `real_interval[p1,p2] SUBSET (KA:real->bool)` THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
        ASM_CASES_TAC `t < a` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(b < t)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "ga" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `t0:real = b` THENL
     [USE_THEN "win" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`KB:real->bool`; `GB:real->A`; `q1:real`; `b + &1`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `real_interval[q1,q2] SUBSET (KB:real->bool)` THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(t < a)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `b < t` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "gb" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                   `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b / (b - a)`;
                   `t0:real`] CMPM_LOCAL_PIECE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a < t0 /\ t0 < b` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `t0 IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real`
      (X_CHOOSE_THEN `K1:real->bool` (X_CHOOSE_THEN `G1:real->A`
        (fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "g1" (last(CONJUNCTS th))))))) THEN
    USE_THEN "win" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`K1:real->bool`; `G1:real->A`; `t1:real`; `t2:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `real_interval[t1,t2] SUBSET (K1:real->bool)` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(t < a) /\ ~(b < t)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "g1" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J. J IN fam ==> ?G'. mfd_geodesic (top,atlas) (g:A->real^N^N) G' J /\
                          !t. t IN J ==> G' t = (G:real->A) t`
  MP_TAC THENL
   [EXPAND_TAC "fam" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `gam:(real->bool)->real->A` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `fam:(real->bool)->bool`;
                 `gam:(real->bool)->real->A`; `G:real->A`] GEOM_GEODESIC_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC CMPM_UNIONS_REALINTERVAL THEN
      EXISTS_TAC `real_interval[a,b]` THEN
      REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNIONS] THEN USE_THEN "cover" (fun th -> MESON_TAC[th]);
        EXPAND_TAC "fam" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`UNIONS fam:real->bool`; `G:real->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN USE_THEN "cover" (fun th -> MESON_TAC[th]);
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(t < a) /\ ~(b < t)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC]);;

