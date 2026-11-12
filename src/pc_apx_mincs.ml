(* ========================================================================= *)
(* pc_apx_mincs: MT Appendix statements about constant-speed minimizing      *)
(* geodesics in necks, in the constant-speed forms of pc_p2b_defs            *)
(* (P2B_APX_A4_CS_STATEMENT and its companions) and of pc_apx_csreq: A.4-CS  *)
(* (the s-function increases at nearly full speed along a long minimizer     *)
(* inside a neck), A.6-CS, A.7-CS, A.8-CS.  Route of A.4 (MT's proof relies  *)
(* on a continuous dependence of minimal geodesics on the metric, which      *)
(* fails in general): in the neck chart the minimizer is a geodesic of the   *)
(* pullback metric (MFD_MINIMIZING_IMP_GEODESIC in the domain); along it s'' *)
(* is bounded by the C^2 closeness to the cylinder (the model geodesics have *)
(* s'' = 0), and a window argument against the N2 upper bound replaces MT's  *)
(* continuity argument.                                                      *)
(* ========================================================================= *)

needs "src/pc_apx_short.ml";;
needs "src/pc_p2b_defs.ml";;
needs "src/pc_p3_s13plane.ml";;
needs "src/pc_cmp_min.ml";;
needs "src/pc_apx_csreq.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Minimizers in a neck are geodesics of the pullback metric.                *)
(* ------------------------------------------------------------------------- *)

(* Speeds are natural under parametrizations (the pointwise form of       *)
(* MFD_PARAM_C1_CURVE_LENGTH, same proof).                                 *)

let APXM_PARAM_SPEED = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) G c a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\
     (!y. y IN s
          ==> G y = mpullback (SND(chart_at atlas (e y)) o e)
                              (metric_local atlas (chart_at atlas (e y)) g) y) /\
     mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\ a < b
     ==> mfd_c1_curve (top,atlas) (e o c) a b /\
         !t. t IN real_interval[a,b]
             ==> mfd_speed atlas g (e o c) a b t = mfd_speed (open_set_atlas s) G c a b t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "G")
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^N->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool,\x:real^N. x) IN open_set_atlas s` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (c:real->real^N) t IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `c:real->real^N`;
                   `a:real`; `b:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean s) (s:real^N->bool) /\
    continuous_map (subtopology (subtopology euclidean s) s,top) (e:real^N->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; OPEN_IN_SUBTOPOLOGY_REFL;
                    TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                 ((e:real^N->A) o (c:real->real^N)) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (s:real^N->bool)`;
                          `open_set_atlas (s:real^N->bool)`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real->real^N) t IN s` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->A)((c:real->real^N) t) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET topspace top` THEN
    UNDISCH_TAC `(c:real->real^N) t IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGD_OPEN_SET_SPEED] THEN
  USE_THEN "G"
   (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(c:real->real^N) t IN s`)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)((c:real->real^N) t)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool)
                     ((e:real^N->A)((c:real->real^N) t))`,
           `k:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(e:real^N->A) o (c:real->real^N)`;
                 `a:real`; `b:real`; `t:real`; `V:A->bool`; `psi:A->real^N`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `((psi:A->real^N) o (e:real^N->A) o chart_inv (s:real^N->bool,\x:real^N. x))
    differentiable (at ((c:real->real^N) t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC
     `frechet_derivative ((psi:A->real^N) o (e:real^N->A) o
                          chart_inv (s:real^N->bool,\x:real^N. x))
                         (at ((c:real->real^N) t))` THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^N))->bool`; `s:real^N->bool`;
                   `e:real^N->A`; `(s:real^N->bool,\x:real^N. x)`;
                   `(V:A->bool,psi:A->real^N)`; `(c:real->real^N) t`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(psi:A->real^N) o (e:real^N->A) o chart_inv (s:real^N->bool,\x:real^N. x)`;
    `(psi:A->real^N) o (e:real^N->A)`; `s:real^N->bool`;
    `(c:real->real^N) t`] GRGD_FRECHET_EQ_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (\r. (psi:A->real^N)((e:real^N->A)((c:real->real^N)(drop r))))
      (at (lift t) within interval[lift a,lift b]) =
    frechet_derivative (psi o e o chart_inv (s:real^N->bool,\x:real^N. x))
      (at (c t))
      (vector_derivative (\r. c(drop r))
         (at (lift t) within interval[lift a,lift b]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`;
                   `open_set_atlas (s:real^N->bool)`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^N))->bool`; `s:real^N->bool`;
                   `e:real^N->A`; `c:real->real^N`; `a:real`; `b:real`;
                   `(s:real^N->bool,\x:real^N. x)`; `(V:A->bool,psi:A->real^N)`;
                   `lift t`] GRGD_PUSH_VD) THEN
    ASM_REWRITE_TAC[FST; SND; LIFT_DROP; GRGD_IN_INTERVAL_LIFT];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN
  ASM_MESON_TAC[has_derivative]);;

(* The derivative within [a,b] of a curve that agrees on [a,b] with a      *)
(* curve differentiable at t.                                              *)

let APXM_VD_WITHIN_EQ = prove
 (`!(c0:real->real^N) c1 v a b t.
     a < b /\ t IN real_interval[a,b] /\
     (!r. r IN real_interval[a,b] ==> c1 r = c0 r) /\
     ((\r. c1(drop r)) has_vector_derivative v) (at (lift t))
     ==> vector_derivative (\r. c0(drop r)) (at (lift t) within interval[lift a,lift b]) = v`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\r. (c1:real->real^N)(drop r)`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]]);;

(* A constant-speed minimizer of M inside a neck is, in the neck           *)
(* coordinates, a geodesic of the pullback metric on an open interval      *)
(* containing [a,b] (its lift minimizes in the neck domain, so             *)
(* MFD_MINIMIZING_IMP_GEODESIC applies there), with constant speed.        *)

let APXM_CS_NECK_GEODESIC = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b.
     hausdorff_space top /\ riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps))
     ==> ?J (c:real->real^3) v.
           is_realinterval J /\ real_open J /\ real_interval[a,b] SUBSET J /\
           (!t. t IN J
                ==> c t IN rfs_neck_dom eps /\
                    ((\s. c(drop s)) has_vector_derivative v t) (at (lift t)) /\
                    ((\s. v(drop s)) has_vector_derivative
                     --(christoffel (rfs_pullback atlas e g) (c t) (v t) (v t)))
                    (at (lift t))) /\
           (!t. a <= t /\ t <= b ==> gamma t = e(c t)) /\
           (!t. a <= t /\ t <= b
                ==> v t dot (rfs_pullback atlas e g (c t) ** v t) =
                    (mfd_length atlas g gamma a b / (b - a)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s = rfs_neck_dom eps` THEN
  ABBREV_TAC `G = rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas s (e:real^3->A) /\ open (s:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    EXPAND_TAC "s" THEN SIMP_TAC[rfs_neck; rfs_neck_dom; OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  (* the dom manifold *)
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean s) (open_set_atlas (s:real^3->bool)) /\
                riemannian_metric (open_set_atlas s) (G:real^3->real^3^3) /\
                hausdorff_space (subtopology euclidean (s:real^3->bool)) /\
                metric_field s G /\
                (!y. y IN s ==> G y = mpullback (SND(chart_at atlas ((e:real^3->A) y)) o e)
                                   (metric_local atlas (chart_at atlas (e y)) g) y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field s (G:real^3->real^3^3)` ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[open_set_atlas] THEN MATCH_MP_TAC GRGD_EUCLID_ATLAS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
      EXPAND_TAC "G" THEN REWRITE_TAC[rfs_pullback]];
    ALL_TAC] THEN
  (* the lift *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> ((e:real^3->A) o (c0:real->real^3)) t = gamma t`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = mfd_length atlas (g:A->real^3^3) gamma a b` THEN
  (* length and speed of the lift *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `G:real^3->real^3^3`; `c0:real->real^3`;
                 `a:real`; `b:real`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `G:real^3->real^3^3`; `c0:real->real^3`;
                 `a:real`; `b:real`] APXM_PARAM_SPEED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_length (open_set_atlas s) (G:real^3->real^3^3) c0 a b = L` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       can (find_term (fun t -> t = `mfd_length (open_set_atlas s) (G:real^3->real^3^3) c0 a b`))
           (concl th) then REWRITE_TAC[GSYM th] else failwith "no") THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC MFD_LENGTH_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b]
                    ==> mfd_speed (open_set_atlas s) (G:real^3->real^3^3) c0 a b t = L / (b - a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_speed")) (concl th) &&
       can (find_term (fun t -> t = `open_set_atlas (s:real^3->bool)`)) (concl th)
       then REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `t IN real_interval[a,b]`))]
       else failwith "no") THEN
    REWRITE_TAC[mfd_speed] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) o (c0:real->real^3)`;
                   `gamma:real->A`; `a:real`; `b:real`; `t:real`] GRGD_VELOCITY_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `((e:real^3->A) o (c0:real->real^3)) t = gamma t` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM mfd_speed] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the lift minimizes in the neck domain *)
  SUBGOAL_THEN `mfd_length (open_set_atlas s) (G:real^3->real^3^3) c0 a b =
                mfd_dist (subtopology euclidean s,open_set_atlas s) G (c0 a) (c0 b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC(GEN_ALL REAL_LE_INF) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `mfd_length (open_set_atlas s) (G:real^3->real^3^3)
                    ((c0:real->real^3) o (\x. a + (b - a) * x)) (&0) (&1)` THEN
      EXISTS_TAC `(c0:real->real^3) o (\x. a + (b - a) * x)` THEN REWRITE_TAC[] THEN
      REWRITE_TAC[o_THM; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
                  REAL_ARITH `a + (b - a) = b:real`] THEN
      MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `\x:real. b - a`] THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_CONTINUOUS_ON_CONST] THEN
      MP_TAC(SPECL [`a:real`; `b:real`] GRGD_AFFINE_FACTS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c2:real->real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `s:real^3->bool`; `e:real^3->A`; `G:real^3->real^3^3`; `c2:real->real^3`;
                   `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       can (find_term (fun t -> t = `c2:real->real^3`)) (concl th) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th)
       then REWRITE_TAC[GSYM th] else failwith "no") THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(e:real^3->A) o (c2:real->real^3)`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC(REAL_ARITH `L = d ==> d <= l ==> L <= l`) THEN
    SUBGOAL_THEN `(e:real^3->A)(c0(a:real)) = gamma a /\ e(c0 b) = gamma b`
    (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(SPEC `a:real` (ASSUME `!t. t IN real_interval[a,b]
                    ==> ((e:real^3->A) o (c0:real->real^3)) t = gamma t`)) THEN
      MP_TAC(SPEC `b:real` (ASSUME `!t. t IN real_interval[a,b]
                    ==> ((e:real^3->A) o (c0:real->real^3)) t = gamma t`)) THEN
      REWRITE_TAC[o_THM; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the geodesic of the neck domain *)
  MP_TAC(ISPECL [`subtopology euclidean (s:real^3->bool)`; `open_set_atlas (s:real^3->bool)`;
                 `G:real^3->real^3^3`; `c0:real->real^3`; `a:real`; `b:real`]
                MFD_MINIMIZING_IMP_GEODESIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` (X_CHOOSE_THEN `c1:real->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ASSUME `mfd_geodesic (subtopology euclidean s,open_set_atlas s)
                   (G:real^3->real^3^3) c1 J`) THEN
  REWRITE_TAC[mfd_geodesic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `(s:real^3->bool),(\x:real^3. x)`)))) THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^3` (LABEL_TAC "geo")) THEN
  SUBGOAL_THEN `!t. t IN J ==> (c1:real->real^3) t IN s` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
      (ASSUME `continuous_map (subtopology euclideanreal J,subtopology euclidean s)
                 (c1:real->real^3)`)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y u w. y IN s
                  ==> christoffel (metric_local (open_set_atlas s) (s,(\x:real^3. x))
                                     (G:real^3->real^3^3)) y u w =
                      christoffel G y u w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`J:real->bool`; `c1:real->real^3`; `v:real->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c1:real->real^3) t IN s` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "geo" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_MESON_TAC[IN_REAL_INTERVAL];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t IN real_interval[a,b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    SUBGOAL_THEN `(c1:real->real^3) t = c0 t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `t IN (J:real->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(c0:real->real^3) t IN s` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "geo" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`c0:real->real^3`; `c1:real->real^3`; `(v:real->real^3) t`;
                   `a:real`; `b:real`; `t:real`] APXM_VD_WITHIN_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (v:real->real^3) t dot ((G:real^3->real^3^3)(c0 t) ** v t)`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `(v:real->real^3) t = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ASSUME `metric_field s (G:real^3->real^3^3)`) THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `(c0:real->real^3) t` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `G:real^3->real^3^3`; `c0:real->real^3`;
                   `a:real`; `b:real`; `t:real`] GRGD_OPEN_SET_SPEED) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP (ASSUME `!t. t IN real_interval[a,b]
                     ==> mfd_speed (open_set_atlas s) (G:real^3->real^3^3) c0 a b t = L / (b - a)`)
                    (ASSUME `t IN real_interval[a,b]`)) THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[SQRT_POW_2]]);;


(* ------------------------------------------------------------------------- *)
(* The s-function along a geodesic of the pullback metric and               *)
(* the window argument.                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A.4 Part II.  Along a curve c with velocity field v in the neck domain:  *)
(* the s-function s(c) = sqrt 2 log|c| has derivative                        *)
(* sqrt 2 (c.v)/(c.c); if v' = -Gamma_G(c)(v,v), that derivative has         *)
(* derivative -sqrt 2 (c.dGamma)/(c.c), dGamma = Gamma_G - Gamma_G0 (G0 the  *)
(* cylinder metric, whose geodesics have s'' = 0), and that second           *)
(* derivative is at most 2 D |v|^2_G0 when R G is D-close to G0 in C^2.     *)
(* ------------------------------------------------------------------------- *)

let APXM_SIGMA_DERIV = prove
 (`!(c:real->real^3) v t.
     ~(c t = vec 0) /\
     ((\r. c(drop r)) has_vector_derivative v) (at (lift t))
     ==> ((\r. apx_sval(c r)) has_real_derivative
          (sqrt(&2) * (c t dot v) / (c t dot c t))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (c:real->real^3) t dot c t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `((\r. (c:real->real^3) r dot c r) has_real_derivative
                 (&2 * (c t dot v))) (atreal t)` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`c:real->real^3`; `c:real->real^3`; `v:real^3`; `v:real^3`; `t:real`]
                  CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`v:real^3`; `(c:real->real^3) t`] DOT_SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((sqrt o (\r. (c:real->real^3) r dot c r)) has_real_derivative
                 (inv(&2 * sqrt(c t dot c t)) * &2 * (c t dot v))) (atreal t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT];
    ALL_TAC] THEN
  SUBGOAL_THEN `((log o sqrt o (\r. (c:real->real^3) r dot c r)) has_real_derivative
                 (inv(sqrt(c t dot c t)) * inv(&2 * sqrt(c t dot c t)) * &2 * (c t dot v)))
                (atreal t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[SQRT_LT_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\r. apx_sval((c:real->real^3) r)) =
                (\r. sqrt(&2) * (log o sqrt o (\r. c r dot c r)) r)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; apx_sval; vector_norm]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!f a b net. (f has_real_derivative a) net /\ a = b
                                    ==> (f has_real_derivative b) net`) THEN
  EXISTS_TAC `sqrt(&2) * inv(sqrt(c t dot c t)) * inv(&2 * sqrt(c t dot c t)) * &2 *
              ((c:real->real^3) t dot v)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((c:real->real^3) t dot c t) /\
                sqrt(c t dot c t) pow 2 = c t dot c t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_LT_0; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = (c:real->real^3) t dot c t` THEN ABBREV_TAC `sq = sqrt q` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sq pow 2 = q`)) THEN
  UNDISCH_TAC `&0 < sq` THEN CONV_TAC REAL_FIELD);;

let APXM_SIGMA1_DERIV = prove
 (`!(G:real^3->real^3^3) (c:real->real^3) v t.
     ~(c t = vec 0) /\
     ((\r. c(drop r)) has_vector_derivative v t) (at (lift t)) /\
     ((\r. v(drop r)) has_vector_derivative
      --(christoffel G (c t) (v t) (v t))) (at (lift t))
     ==> ((\r. sqrt(&2) * (c r dot v r) / (c r dot c r)) has_real_derivative
          (--(sqrt(&2)) * (c t dot (christoffel G (c t) (v t) (v t) -
                                     christoffel (cylinder_flow (&0)) (c t) (v t) (v t))) /
           (c t dot c t))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `w = christoffel (G:real^3->real^3^3) (c t) ((v:real->real^3) t) (v t)` THEN
  SUBGOAL_THEN `((\r. (c:real->real^3) r dot v r) has_real_derivative
                 (c t dot --w + v t dot v t)) (atreal t)` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`c:real->real^3`; `v:real->real^3`; `(v:real->real^3) t`; `--w:real^3`;
                   `t:real`] CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\r. (c:real->real^3) r dot c r) has_real_derivative
                 (c t dot v t + v t dot c t)) (atreal t)` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`c:real->real^3`; `c:real->real^3`; `(v:real->real^3) t`;
                   `(v:real->real^3) t`; `t:real`] CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!f a b net. (f has_real_derivative a) net /\ a = b
                                    ==> (f has_real_derivative b) net`) THEN
  EXISTS_TAC `sqrt(&2) * (((c:real->real^3) t dot --w + (v:real->real^3) t dot v t) *
                          (c t dot c t) -
                          (c t dot v t) * (c t dot v t + v t dot c t)) /
                         (c t dot c t) pow 2` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\r. (c:real->real^3) r dot v r`;
                   `(c:real->real^3) t dot --w + (v:real->real^3) t dot v t`;
                   `\r. (c:real->real^3) r dot c r`; `(c:real->real^3) t dot v t + v t dot c t`;
                   `t:real`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `sqrt(&2)` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_CYL0_CHRISTOFFEL; NORM_POW_2; DOT_RSUB; DOT_RADD; DOT_RMUL; DOT_RNEG] THEN
  SUBGOAL_THEN `(v:real->real^3) t dot c t = c t dot v t` SUBST1_TAC THENL
   [REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real->real^3) t dot c t = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  ABBREV_TAC `q = (c:real->real^3) t dot c t` THEN
  ABBREV_TAC `p = (c:real->real^3) t dot v t` THEN
  ABBREV_TAC `n2 = (v:real->real^3) t dot v t` THEN
  ABBREV_TAC `cw = (c:real->real^3) t dot w` THEN
  CONV_TAC REAL_FIELD);;

let APXM_SIGMA2_BOUND = prove
 (`!s (G:real^3->real^3^3) R D y u.
     open s /\ s SUBSET ((:real^3) DELETE vec 0) /\ metric_field s G /\ &0 < R /\ y IN s /\
     &0 <= D /\ D <= &1 / &10 /\
     lck_dist2 2 (cylinder_flow (&0)) (\z. R %% G z) y <= D pow 2
     ==> abs(--(sqrt(&2)) *
             (y dot (christoffel G y u u - christoffel (cylinder_flow (&0)) y u u)) /
             (y dot y))
         <= &2 * D * (u dot (cylinder_flow (&0) y ** u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s (\z. R %% (G:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `christoffel (\z. R %% (G:real^3->real^3^3) z) y u u = christoffel G y u u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_SCALE THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = sqrt(&2) / norm(y:real^3)` THEN
  SUBGOAL_THEN `&0 < k /\ k pow 2 = &2 / norm(y:real^3) pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; SQRT_LT_0; NORM_POS_LT; REAL_POW_DIV; SQRT_POW_2; REAL_POS;
                 REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `u dot (cylinder_flow (&0) y ** u) = k pow 2 * (u dot u)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `cylinder_flow (&0)`; `\z. R %% (G:real^3->real^3^3) z`;
                 `y:real^3`; `k %% mat 1:real^3^3`; `D:real`] P3S_PERT_CHRIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LRG_CYL0_EQ; TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
                MATRIX_MUL_LID; MATRIX_CMUL_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM REAL_POW_2];
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `u:real^3`])] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; NORM_MUL] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
  ABBREV_TAC `dg = christoffel (G:real^3->real^3^3) y u u -
                   christoffel (cylinder_flow (&0)) y u u` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs(--(sqrt(&2)) * (y dot dg) / (y dot y)) =
                k * abs(y dot dg) / norm(y:real^3)` SUBST1_TAC THENL
   [EXPAND_TAC "k" THEN
    REWRITE_TAC[GSYM NORM_POW_2; REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_NORM;
                REAL_ABS_POW] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; SQRT_POS_LE; REAL_POS] THEN
    UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k * norm(dg:real^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `a <= b ==> b = c ==> a <= c`)) THEN
    SUBST1_TAC(SYM(ASSUME `k pow 2 = &2 / norm(y:real^3) pow 2`)) THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* A.4 Part III: the window argument (a quantitative argument in place of    *)
(* MT's continuity argument).  If f'' is bounded by B on [a,b]               *)
(* and the increments of f control the elapsed time as in the N2 upper      *)
(* bound (W (u2 - u1) <= K (|f u2 - f u1| + P)), then |f'| > (1 - alpha) W   *)
(* on [a,b] once a window of normalized length Lam with                      *)
(* K ((1 - alpha) Lam + B (Lam/W)^2 + P) < Lam fits into [a,b].  With        *)
(* f(a) < f(b), f' is then positive throughout (IVT).                        *)
(* ------------------------------------------------------------------------- *)

let APXM_WINDOW = prove
 (`!f f1 f2 a b W B K P Lam alpha.
     a < b /\ &0 < W /\ &0 <= B /\ &0 <= K /\ &0 < Lam /\ Lam <= W * (b - a) /\
     K * ((&1 - alpha) * Lam + B * (Lam / W) pow 2 + P) < Lam /\
     (!t. a <= t /\ t <= b
          ==> (f has_real_derivative f1 t) (atreal t) /\
              (f1 has_real_derivative f2 t) (atreal t) /\ abs(f2 t) <= B) /\
     (!u1 u2. a <= u1 /\ u1 <= u2 /\ u2 <= b
              ==> W * (u2 - u1) <= K * (abs(f u2 - f u1) + P))
     ==> !t. a <= t /\ t <= b ==> (&1 - alpha) * W < abs(f1 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `tw = Lam / W` THEN
  SUBGOAL_THEN `&0 < tw /\ tw <= b - a /\ W * tw = Lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tw" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ta = max a (t0 - tw)` THEN
  SUBGOAL_THEN `a <= ta /\ ta <= t0 /\ t0 <= ta + tw /\ ta + tw <= b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b]
                      ==> abs((f1:real->real) x - f1 y) <= B * abs(x - y)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_BOUND THEN EXISTS_TAC `f2:real->real` THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    ASM_MESON_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ta <= t /\ t <= ta + tw
                    ==> abs((f1:real->real) t) <= (&1 - alpha) * W + B * tw`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`t:real`; `t0:real`] (ASSUME
     `!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b]
            ==> abs((f1:real->real) x - f1 y) <= B * abs(x - y)`)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x0) <= c /\ e <= d ==> abs(x - x0) <= e ==> abs x <= c + d`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real->real)(ta + tw) - f ta) <= ((&1 - alpha) * W + B * tw) * tw`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `real_interval[ta,ta + tw]`;
                   `(&1 - alpha) * W + B * tw`] REAL_DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        SUBGOAL_THEN `a <= x /\ x <= b` (fun th -> ASM_MESON_TAC[th]) THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`ta + tw`; `ta:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(ta + tw) - ta = tw:real`] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < tw ==> abs tw = tw`]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ta:real`; `ta + tw`] (ASSUME
   `!u1 u2. a <= u1 /\ u1 <= u2 /\ u2 <= b
            ==> W * (u2 - u1) <= K * (abs((f:real->real) u2 - f u1) + P)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(ta + tw) - ta = tw:real`; ASSUME `W * tw = Lam`] THEN
  MATCH_MP_TAC(REAL_ARITH `!y z Lam:real. y <= z /\ z < Lam ==> ~(Lam <= y)`) THEN
  EXISTS_TAC `K * ((&1 - alpha) * Lam + B * tw pow 2 + P)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y u v P:real. x <= y /\ y = u + v ==> x + P <= u + v + P`) THEN
  EXISTS_TAC `((&1 - alpha) * W + B * tw) * tw` THEN ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(ASSUME `W * tw = Lam`)) THEN CONV_TAC REAL_RING);;

let APXM_POS_DERIV = prove
 (`!f f1 f2 a b m.
     a < b /\ &0 <= m /\ f a < f b /\
     (!t. a <= t /\ t <= b
          ==> (f has_real_derivative f1 t) (atreal t) /\
              (f1 has_real_derivative f2 t) (atreal t) /\ m < abs(f1 t))
     ==> !t. a <= t /\ t <= b ==> m < f1 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u w. a <= u /\ u <= w /\ w <= b
                      ==> (f1:real->real) real_continuous_on real_interval[u,w]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(f2:real->real) z` THEN
    SUBGOAL_THEN `a <= z /\ z <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `a:real`; `b:real`]
                REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (f1:real->real) xi` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 * (b - a) < (f1:real->real) xi * (b - a)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_SUB_LT]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `m < abs((f1:real->real) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real->real) t <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?z. a <= z /\ z <= b /\ (f1:real->real) z = &0` STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `t <= xi \/ xi <= t:real`) THENL
     [MP_TAC(ISPECL [`f1:real->real`; `t:real`; `xi:real`; `&0`] REAL_IVT_INCREASING) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `z:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`f1:real->real`; `xi:real`; `t:real`; `&0`] REAL_IVT_DECREASING) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `z:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `m < abs((f1:real->real) z)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The constants of A.4: window length 20/alpha, eps <= alpha^2/2000.        *)

let APXM_A4_ARITH = prove
 (`!al eps. &0 < al /\ al <= &1 / &2 /\ &0 < eps /\ eps <= al pow 2 / &2000
            ==> sqrt(&1 + eps) *
                ((&1 - al) * (&20 / al) + &3 * eps * (&20 / al) pow 2 + sqrt(&2) * pi)
                < &20 / al`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `Lam = &20 / al` THEN
  SUBGOAL_THEN `al * Lam = &20` ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&40 <= Lam` ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps * Lam pow 2 <= &1 / &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `al pow 2 / &2000 * Lam pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `al pow 2 / &2000 * Lam pow 2 = &1 / &5` SUBST1_TAC THENL
       [UNDISCH_TAC `al * Lam = &20` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * Lam <= &1 / &200` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `al pow 2 / &2000 * Lam` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `al pow 2 / &2000 * Lam = al / &100` SUBST1_TAC THENL
       [UNDISCH_TAC `al * Lam = &20` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - al) * Lam = Lam - &20` SUBST1_TAC THENL
   [UNDISCH_TAC `al * Lam = &20` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `X = (Lam - &20) + &3 * eps * Lam pow 2 + sqrt(&2) * pi` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= Lam - &14` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MP_TAC APX_SQRT2_PI THEN
    SUBGOAL_THEN `&0 <= sqrt(&2) * pi /\ &0 <= eps * Lam pow 2` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) <= &1 + eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC(SPEC `eps:real` REAL_LE_SQUARE) THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 + eps) * X` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eps * X <= eps * Lam` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* A.4-CS.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A.4-CS assembled.  APXM_NECK_C2_CLOSE: the C^2 closeness at every point  *)
(* of a neck.  APXM_A4_SFUN_DERIVS: the s-function along a constant-speed   *)
(* minimizer inside a neck extends to a C^2 function with                    *)
(* |s''| <= 3 eps R V^2 (R = R(x), V the speed).  APXM_A4_INCREMENT: the N2  *)
(* upper bound in the form used by the window argument.  APXM_A4_CONSTS:    *)
(* the constants.  APXM_A4_CS: P2B_APX_A4_CS_STATEMENT.                      *)
(* ------------------------------------------------------------------------- *)

let APXM_NECK_C2_CLOSE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &2 /\
     y IN rfs_neck_dom eps
     ==> lck_dist2 2 (cylinder_flow (&0))
           (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y <= eps pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
      (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN MATCH_MP_TAC APX_KREG_TWO THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let APXM_A4_BOUND_ARITH = prove
 (`!eps Q0 P X. &0 <= eps /\ eps <= &1 / &10 /\ &0 <= Q0 /\ (&1 - eps) * Q0 <= P /\
                X <= &2 * eps * Q0
                ==> X <= &3 * eps * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `eps * ((&1 - eps) * Q0) <= eps * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eps * (eps * Q0) <= eps * ((&1 / &10) * Q0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APXM_A4_SFUN_DERIVS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b.
     eps <= &1 / &10 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps))
     ==> ?f f1 f2.
           !t. a <= t /\ t <= b
               ==> f t = apx_sfun (rfs_neck_dom eps) e (gamma t) /\
                   (f has_real_derivative f1 t) (atreal t) /\
                   (f1 has_real_derivative f2 t) (atreal t) /\
                   abs(f2 t) <= &3 * eps * mfd_scalar atlas g x *
                                (mfd_length atlas g gamma a b / (b - a)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`]
                APXM_CS_NECK_GEODESIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` (X_CHOOSE_THEN `c:real->real^3`
    (X_CHOOSE_THEN `v:real->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "geo")
          (CONJUNCTS_THEN2 (LABEL_TAC "gam") (LABEL_TAC "spd"))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  EXISTS_TAC `\t. apx_sval((c:real->real^3) t)` THEN
  EXISTS_TAC `\t. sqrt(&2) * ((c:real->real^3) t dot v t) / (c t dot c t)` THEN
  EXISTS_TAC `\t. --(sqrt(&2)) *
                  ((c:real->real^3) t dot
                   (christoffel (rfs_pullback atlas (e:real^3->A) (g:A->real^3^3))
                                (c t) (v t) (v t) -
                    christoffel (cylinder_flow (&0)) (c t) (v t) (v t))) / (c t dot c t)` THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `t IN (J:real->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET (J:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "geo" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "gam" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "spd" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((c:real->real^3) t = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SFUN_AT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_PARAM_INJ];
    MATCH_MP_TAC APXM_SIGMA_DERIV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC APXM_SIGMA1_DERIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 2 (cylinder_flow (&0))
      (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z)
      ((c:real->real^3) t) <= eps pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APXM_NECK_C2_CLOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v:real->real^3) t dot (cylinder_flow (&0) (c t) ** v t)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `(v:real->real^3) t = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(SPEC `eps:real` APX_NECK_CYL_FIELD) THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `(c:real->real^3) t` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `eps:real`; `(c:real->real^3) t`;
                 `(v:real->real^3) t`] APXM_SIGMA2_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `(c:real->real^3) t`;
                `(v:real->real^3) t`] APX_NECK_C0_BOUNDS) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC APXM_A4_BOUND_ARITH THEN
  EXISTS_TAC `(v:real->real^3) t dot (cylinder_flow (&0) (c t) ** v t)` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APXM_A4_INCREMENT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b f u1 u2.
     eps < &1 /\ riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
     (!t. a <= t /\ t <= b ==> f t = apx_sfun (rfs_neck_dom eps) e (gamma t)) /\
     a <= u1 /\ u1 <= u2 /\ u2 <= b
     ==> (sqrt(mfd_scalar atlas g x) * mfd_length atlas g gamma a b / (b - a)) * (u2 - u1)
         <= sqrt(&1 + eps) * (abs(f u2 - f u1) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma u1 u2 =
                (mfd_length atlas g gamma a b / (b - a)) * (u2 - u1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `a:real`; `b:real`; `u1:real`; `u2:real`]
                  GRGD_LENGTH_SUBINTERVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS
     `real_integral (real_interval[u1,u2])
        (\t. mfd_length atlas (g:A->real^3^3) gamma a b / (b - a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST]];
    ALL_TAC] THEN
  MP_TAC(SPEC `u1:real` (ASSUME
   `!t. a <= t /\ t <= b ==> gamma t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `u2:real` (ASSUME
   `!t. a <= t /\ t <= b ==> gamma t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real->real) u1 = apx_sval y /\ f u2 = apx_sval z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `u1:real` (ASSUME
       `!t. a <= t /\ t <= b
            ==> (f:real->real) t = apx_sfun (rfs_neck_dom eps) (e:real^3->A) (gamma t)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SFUN_AT THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MFD_PARAM_INJ];
      MP_TAC(SPEC `u2:real` (ASSUME
       `!t. a <= t /\ t <= b
            ==> (f:real->real) t = apx_sfun (rfs_neck_dom eps) (e:real^3->A) (gamma t)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SFUN_AT THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MFD_PARAM_INJ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `z:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma u1 u2 =
                mfd_dist (top,atlas) g (gamma u1) (gamma u2)` MP_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    REWRITE_TAC[apx_shortest] THEN
    DISCH_THEN(MP_TAC o SPECL [`u1:real`; `u2:real`] o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
              (sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) *
               (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval y - apx_sval z) = abs(apx_sval z - apx_sval y)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas (g:A->real^3^3) x)` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_LT_0]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let APXM_A4_CONSTS = prove
 (`!al eps R L a b.
     &0 < al /\ al <= &1 / &2 /\ &0 < eps /\ eps <= al pow 2 / &2000 /\
     &0 < R /\ a < b /\ inv(&100 * eps) * inv(sqrt R) < L
     ==> &0 < sqrt R * L / (b - a) /\
         &0 <= &3 * eps * R * (L / (b - a)) pow 2 /\
         &0 < &20 / al /\
         &20 / al <= (sqrt R * L / (b - a)) * (b - a) /\
         sqrt(&1 + eps) *
         ((&1 - al) * &20 / al +
          (&3 * eps * R * (L / (b - a)) pow 2) * (&20 / al / (sqrt R * L / (b - a))) pow 2 +
          sqrt(&2) * pi) < &20 / al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt R /\ sqrt R pow 2 = R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_LT_0; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&100 * eps) * inv(sqrt R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &100`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L / (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `al * al <= al * (&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2000 * eps <= al` ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= al pow 2 / &2000` THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(sqrt R * L / (b - a)) * (b - a) = sqrt R * L` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(b - a = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&100 * eps)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `inv(al) <= inv(&2000 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&20 * inv(&2000 * eps) = inv(&100 * eps)` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `inv(&100 * eps) * inv(sqrt R) < L` THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&3 * eps * R * (L / (b - a)) pow 2) * (&20 / al / (sqrt R * L / (b - a))) pow 2 =
    &3 * eps * (&20 / al) pow 2`
  SUBST1_TAC THENL
   [ABBREV_TAC `s = sqrt R` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s pow 2 = R`)) THEN
    ABBREV_TAC `V = L / (b - a)` THEN
    MAP_EVERY UNDISCH_TAC [`&0 < V`; `&0 < s`; `&0 < al`] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC APXM_A4_ARITH THEN ASM_REWRITE_TAC[]]);;

let APXM_A4_CS = prove
 (`!u:A->bool. P2B_APX_A4_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_APX_A4_CS_STATEMENT] THEN
  X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  ABBREV_TAC `al = min alpha (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < al /\ al <= &1 / &2 /\ al <= alpha` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `al pow 2 / &2000` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `al * al <= al * (&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ eps < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= al pow 2 / &2000` THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`]
                APXM_A4_SFUN_DERIVS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real->real` (X_CHOOSE_THEN `f1:real->real`
    (X_CHOOSE_THEN `f2:real->real` (LABEL_TAC "fd")))) THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b
                    ==> (f:real->real) t = apx_sfun (rfs_neck_dom eps) (e:real^3->A) (gamma t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                     (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`al:real`; `eps:real`; `mfd_scalar atlas (g:A->real^3^3) x`;
                 `mfd_length atlas (g:A->real^3^3) gamma a b`; `a:real`; `b:real`]
                APXM_A4_CONSTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `a:real`; `b:real`;
                 `sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                  mfd_length atlas g gamma a b / (b - a)`;
                 `&3 * eps * mfd_scalar atlas (g:A->real^3^3) x *
                  (mfd_length atlas g gamma a b / (b - a)) pow 2`;
                 `sqrt(&1 + eps)`; `sqrt(&2) * pi`; `&20 / al`; `al:real`] APXM_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `&0 < eps ==> &0 <= &1 + eps`]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                       (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC APXM_A4_INCREMENT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `e:real^3->A`] THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `a:real`; `b:real`;
                 `(&1 - al) * (sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                               mfd_length atlas g gamma a b / (b - a))`] APXM_POS_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                       (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t IN real_interval[a,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(vector_derivative
          (\s. lift(apx_sfun (rfs_neck_dom eps) (e:real^3->A) (gamma(drop s))))
          (at (lift t) within interval[lift a,lift b])) = (f1:real->real) t`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\r. lift(apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) r))`;
                   `\r. lift((f:real->real) r)`; `lift((f1:real->real) t)`;
                   `a:real`; `b:real`; `t:real`] APXM_VD_WITHIN_EQ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC[];
        USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                         (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (ASSUME `!t. t IN real_interval[a,b]
                              ==> mfd_speed atlas (g:A->real^3^3) gamma a b t =
                                  mfd_length atlas g gamma a b / (b - a)`)
                  (ASSUME `t IN real_interval[a,b]`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - al) * (sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                           mfd_length atlas g gamma a b / (b - a))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The core of A.4 for alpha' in (0,1/2], strict monotonicity,              *)
(* A.6-CS.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The core of A.4 for any alpha' in (0,1/2]: along a long constant-speed    *)
(* minimizer inside an eps-neck with eps <= alpha'^2/2000, the s-function   *)
(* extends to a C^2 function f with |f'| > (1 - alpha') R^(1/2) V.  With     *)
(* Rolle it is injective on [a,b] (A.6), with the IVT strictly monotone.     *)
(* ------------------------------------------------------------------------- *)

let APXM_A4_CORE = prove
 (`!al top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b.
     &0 < al /\ al <= &1 / &2 /\ &0 < eps /\ eps <= al pow 2 / &2000 /\
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
     inv(&100 * eps) * inv(sqrt(mfd_scalar atlas g x)) < mfd_length atlas g gamma a b
     ==> &0 < sqrt(mfd_scalar atlas g x) * mfd_length atlas g gamma a b / (b - a) /\
         ?f f1 f2.
           !t. a <= t /\ t <= b
               ==> f t = apx_sfun (rfs_neck_dom eps) e (gamma t) /\
                   (f has_real_derivative f1 t) (atreal t) /\
                   (f1 has_real_derivative f2 t) (atreal t) /\
                   (&1 - al) * (sqrt(mfd_scalar atlas g x) *
                                mfd_length atlas g gamma a b / (b - a)) < abs(f1 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `al * al <= al * (&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ eps < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= al pow 2 / &2000` THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`al:real`; `eps:real`; `mfd_scalar atlas (g:A->real^3^3) x`;
                 `mfd_length atlas (g:A->real^3^3) gamma a b`; `a:real`; `b:real`]
                APXM_A4_CONSTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`]
                APXM_A4_SFUN_DERIVS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real->real` (X_CHOOSE_THEN `f1:real->real`
    (X_CHOOSE_THEN `f2:real->real` (LABEL_TAC "fd")))) THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `f1:real->real`; `f2:real->real`] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b
                    ==> (f:real->real) t = apx_sfun (rfs_neck_dom eps) (e:real^3->A) (gamma t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                     (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `a:real`; `b:real`;
                 `sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                  mfd_length atlas g gamma a b / (b - a)`;
                 `&3 * eps * mfd_scalar atlas (g:A->real^3^3) x *
                  (mfd_length atlas g gamma a b / (b - a)) pow 2`;
                 `sqrt(&1 + eps)`; `sqrt(&2) * pi`; `&20 / al`; `al:real`] APXM_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `&0 < eps ==> &0 <= &1 + eps`]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                       (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC APXM_A4_INCREMENT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `e:real^3->A`] THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                   (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Strict monotonicity from a nonvanishing continuous derivative: the       *)
(* derivative has constant sign (IVT), then the MVT.                        *)

let APXM_STRICT_MONO = prove
 (`!f f1 f2 a b.
     a <= b /\
     (!t. a <= t /\ t <= b
          ==> (f has_real_derivative f1 t) (atreal t) /\
              (f1 has_real_derivative f2 t) (atreal t) /\ ~(f1 t = &0))
     ==> (!t. a <= t /\ t <= b ==> &0 < f1 t) /\
         (!s t. a <= s /\ s < t /\ t <= b ==> f s < f t) \/
         (!t. a <= t /\ t <= b ==> f1 t < &0) /\
         (!s t. a <= s /\ s < t /\ t <= b ==> f t < f s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u w. a <= u /\ u <= w /\ w <= b
                      ==> (f1:real->real) real_continuous_on real_interval[u,w]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(f2:real->real) z` THEN
    SUBGOAL_THEN `a <= z /\ z <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. a <= s /\ s < t /\ t <= b
                      ==> ?xi. s <= xi /\ xi <= t /\
                               (f:real->real) t - f s = f1 xi * (t - s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `s:real`; `t:real`]
                  REAL_MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL] THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `a <= z /\ z <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f1:real->real) a = &0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `a <= a /\ a <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (f1:real->real) a` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `!t. a <= t /\ t <= b ==> &0 < (f1:real->real) t` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f1:real->real`; `a:real`; `t:real`; `&0`] REAL_IVT_DECREASING) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `a <= z /\ z <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`] o check (fun th ->
      can (find_term (fun u -> u = `xi:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < (f1:real->real) xi * (t - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    DISJ2_TAC THEN
    SUBGOAL_THEN `!t. a <= t /\ t <= b ==> (f1:real->real) t < &0` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f1:real->real`; `a:real`; `t:real`; `&0`] REAL_IVT_INCREASING) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `a <= z /\ z <= b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`] o check (fun th ->
      can (find_term (fun u -> u = `xi:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < --((f1:real->real) xi) * (t - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < &0 ==> &0 < --x`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC]]);;

(* The s-function on a level sphere of the neck domain.                     *)

let APXM_SFUN_SPHERE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) r p.
     rfs_neck (top,atlas) g eps x e /\ sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
     p IN IMAGE e (sphere(vec 0,r))
     ==> apx_sfun (rfs_neck_dom eps) e p = sqrt(&2) * log r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps) (e:real^3->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (sphere(vec 0,r))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`] APX_SFUN_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_PARAM_INJ]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[apx_sval] THEN
  UNDISCH_TAC `(y:real^3) IN sphere(vec 0,r)` THEN SIMP_TAC[IN_SPHERE_0]);;

let APXM_A6_CS = prove
 (`!u:A->bool. P2B_APX_A6_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_APX_A6_CS_STATEMENT] THEN
  EXISTS_TAC `(&1 / &2) pow 2 / &2000` THEN CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&1 / &2`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `a:real`; `b:real`] APXM_A4_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:real->real`
    (X_CHOOSE_THEN `f1:real->real` (X_CHOOSE_THEN `f2:real->real` (LABEL_TAC "fd"))))) THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `a:real`; `b:real`]
                APXM_STRICT_MONO) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                     (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real) t1 = f t2` ASSUME_TAC THENL
   [SUBGOAL_THEN `!t. a <= t /\ t <= b /\ gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,r))
                      ==> (f:real->real) t = sqrt(&2) * log r`
    (fun th -> ASM_MESON_TAC[th]) THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                     (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)))) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN MATCH_MP_TAC APXM_SFUN_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1:real = t2` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t1 < t2 \/ t1 = t2 \/ t2 < t1:real`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_REFL]);;


(* ------------------------------------------------------------------------- *)
(* A.7-CS (pieces, levels, exits).                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A.7 infrastructure.  APXM_CS_RESTRICT: a constant-speed minimizer        *)
(* restricts to one on every subinterval, with the same speed.  APXM_PIECE: *)
(* the maximal piece in an open set around an interval mapped into it.      *)
(* APXM_LEVEL_HIT: a strictly monotone C^1 function with |f'| > m whose     *)
(* values stay in (lo,hi) attains the levels near f(t0) on the side away    *)
(* from the nearer bound.                                                   *)
(* ------------------------------------------------------------------------- *)

let APXM_CS_RESTRICT = prove
 (`!top atlas (g:A->real^3^3) gamma a b c d.
     smooth_manifold_atlas top atlas /\ apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     a <= c /\ c < d /\ d <= b
     ==> apx_shortest (top,atlas) g gamma c d /\
         mfd_length atlas g gamma c d = (mfd_length atlas g gamma a b / (b - a)) * (d - c) /\
         mfd_length atlas g gamma c d / (d - c) = mfd_length atlas g gamma a b / (b - a) /\
         (!t. t IN real_interval[c,d]
              ==> mfd_speed atlas g gamma c d t = mfd_length atlas g gamma c d / (d - c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma c d =
                (mfd_length atlas g gamma a b / (b - a)) * (d - c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `a:real`; `b:real`; `c:real`; `d:real`]
                  GRGD_LENGTH_SUBINTERVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS
     `real_integral (real_interval[c,d])
        (\t. mfd_length atlas (g:A->real^3^3) gamma a b / (b - a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma c d / (d - c) =
                mfd_length atlas g gamma a b / (b - a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(d - c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[apx_shortest] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
      REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `b:real`; `\t:real. t`; `\t:real. &1`;
                 `c:real`; `d:real`; `t:real`] GRGD_SPEED_REPARAM) THEN
  SUBGOAL_THEN `(gamma:real->A) o (\t. t) = gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
    UNDISCH_TAC `t IN real_interval[c,d]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `t IN real_interval[c,d]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

let APXM_PIECE = prove
 (`!top atlas (gamma:real->A) a b N p q.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < b /\ open_in top N /\
     a <= p /\ p <= q /\ q <= b /\ (!t. p <= t /\ t <= q ==> gamma t IN N)
     ==> ?c d. a <= c /\ c <= p /\ q <= d /\ d <= b /\ c < d /\
               (!t. c < t /\ t < d ==> gamma t IN N) /\
               (c = a \/ ~(gamma c IN N)) /\ (d = b \/ ~(gamma d IN N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed_in top (topspace top DIFF (N:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) p IN N /\ gamma q IN N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?c. a <= c /\ c <= p /\ (c = a \/ ~((gamma:real->A) c IN N)) /\
                    (!t. c < t /\ t <= p ==> gamma t IN N)`
  (X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THENL
   [ASM_CASES_TAC `!t. a <= t /\ t <= p ==> (gamma:real->A) t IN N` THENL
     [EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `w < p` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `gamma:real->A`; `w:real`; `p:real`;
                     `topspace top DIFF (N:A->bool)`] APXS_LAST_IN_CLOSED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
         [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. q <= d /\ d <= b /\ (d = b \/ ~((gamma:real->A) d IN N)) /\
                    (!t. q <= t /\ t < d ==> gamma t IN N)`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THENL
   [ASM_CASES_TAC `!t. q <= t /\ t <= b ==> (gamma:real->A) t IN N` THENL
     [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `q < w` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool)
                      (\t. (gamma:real->A)(q + w - t)) q w` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(\x. mat 1):A->real^3^3`; `gamma:real->A`; `q:real`; `w:real`]
                      MFD_LENGTH_REVERSE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          SIMP_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `\t. (gamma:real->A)(q + w - t)`; `q:real`; `w:real`;
                     `topspace top DIFF (N:A->bool)`] APXS_LAST_IN_CLOSED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF; REAL_ARITH `q + w - q:real = w`;
                        REAL_ARITH `q + w - w:real = q`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(X_CHOOSE_THEN `cs:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q + w - cs` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q + w - t:real` o check (fun th ->
        is_forall(concl th) && can (find_term (fun u -> u = `cs:real`)) (concl th))) THEN
      REWRITE_TAC[REAL_ARITH `q + w - (q + w - t):real = t`] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c:real = p /\ d:real = q` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c:real = a /\ d:real = b` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t <= p` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `t <= q` THENL
     [MATCH_MP_TAC(ASSUME `!t. p <= t /\ t <= q ==> (gamma:real->A) t IN N`) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(ASSUME `!t. q <= t /\ t < d ==> (gamma:real->A) t IN N`) THEN
      ASM_REAL_ARITH_TAC]]);;

let APXM_LEVEL_HIT = prove
 (`!f f1 f2 c d t0 m lo hi y.
     c < d /\ c <= t0 /\ t0 <= d /\ &0 <= m /\
     (!t. c <= t /\ t <= d
          ==> (f has_real_derivative f1 t) (atreal t) /\
              (f1 has_real_derivative f2 t) (atreal t) /\
              m < abs(f1 t) /\ lo < f t /\ f t < hi) /\
     (y <= f t0 /\ hi - m * (d - c) <= y \/ f t0 <= y /\ y <= lo + m * (d - c))
     ==> ?t. c <= t /\ t <= d /\ f t = y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "fd") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(f:real->real) real_continuous_on real_interval[c,d]` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(f1:real->real) z` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lo < (f:real->real) c /\ f c < hi /\ lo < f d /\ f d < hi /\
                lo < f t0 /\ f t0 < hi` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    USE_THEN "fd" (MP_TAC o SPEC `c:real`) THEN USE_THEN "fd" (MP_TAC o SPEC `d:real`) THEN
    USE_THEN "fd" (MP_TAC o SPEC `t0:real`) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `c:real`; `d:real`]
                APXM_STRICT_MONO) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "fd" (fun th -> MP_TAC(MP (SPEC `t:real` th)
                                     (CONJ (ASSUME `c <= t`) (ASSUME `t <= d`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `c:real`; `d:real`] REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL] THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m < abs((f1:real->real) xi)` ASSUME_TAC THENL
   [USE_THEN "fd" (MP_TAC o SPEC `xi:real`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [SUBGOAL_THEN `m * (d - c) <= (f:real->real) d - f c` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      SUBGOAL_THEN `&0 < (f1:real->real) xi` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `&0 < (f1:real->real) t`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) c <= f t0 /\ f t0 <= f d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `c:real = t0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_CASES_TAC `t0:real = d` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `c:real`; `d:real`; `y:real`] REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]];
    SUBGOAL_THEN `m * (d - c) <= (f:real->real) c - f d` ASSUME_TAC THENL
     [SUBGOAL_THEN `(f:real->real) c - f d = --((f1:real->real) xi) * (d - c)` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SUBGOAL_THEN `(f1:real->real) xi < &0` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `(f1:real->real) t < &0`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) d <= f t0 /\ f t0 <= f c` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `t0:real = d` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_CASES_TAC `c:real = t0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `c:real`; `d:real`; `y:real`] REAL_IVT_DECREASING) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]]]);;

let APXM_A7_ARITH = prove
 (`!h k1 k2 P D L1 L2 L.
     &0 < h /\ &1 / &2 <= k1 /\ &0 <= k2 /\ k2 <= &2 /\ &0 <= P /\ P <= &24 / &5 /\
     &10 <= D /\ k1 * h * D <= L1 /\ k1 * h * D <= L2 /\ L = L1 + L2 /\ L <= k2 * h * P
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 * &10 <= k1 * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k2 * P <= &2 * &24 / &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * (&1 / &2 * &10) <= h * (k1 * D) /\ h * (k2 * P) <= h * (&2 * &24 / &5)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k1 * h * D = h * (k1 * D) /\ k2 * h * P = h * (k2 * P)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APXM_A7_EXIT_CONTRA = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b s1 u s2 sg.
     &0 < eps /\ eps <= &1 / &2 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ apx_shortest (top,atlas) g gamma a b /\
     a <= s1 /\ s1 < u /\ u < s2 /\ s2 <= b /\
     gamma s1 IN IMAGE e (rfs_neck_dom eps) /\ gamma s2 IN IMAGE e (rfs_neck_dom eps) /\
     ~(gamma u IN IMAGE e (rfs_neck_dom eps)) /\
     apx_sfun (rfs_neck_dom eps) e (gamma s1) = sg /\
     apx_sfun (rfs_neck_dom eps) e (gamma s2) = sg /\
     &10 <= inv eps - abs sg
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  UNDISCH_TAC `(gamma:real->A) s1 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(gamma:real->A) s2 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `apx_sval y1 = sg /\ apx_sval y2 = sg` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) s1) = sg`;
      UNDISCH_TAC `apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) s2) = sg`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC APX_SFUN_AT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_PARAM_INJ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `s1:real`; `u:real`; `s2:real`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y1:real^3`; `gamma:real->A`;
                 `s1:real`; `u:real`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `apx_sval y1 = sg`])] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `u:real`; `s2:real`] MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y2:real^3`;
                 `\t. (gamma:real->A)(u + s2 - t)`; `u:real`; `s2:real`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `u + s2 - u:real = s2`; REAL_ARITH `u + s2 - s2:real = u`] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `apx_sval y2 = sg`; ASSUME
      `mfd_length atlas (g:A->real^3^3) (\t. gamma(u + s2 - t)) u s2 =
       mfd_length atlas g gamma u s2`])] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y1:real^3`; `y2:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `apx_sval y1 = sg`; ASSUME `apx_sval y2 = sg`;
                                         REAL_SUB_REFL; REAL_ABS_NUM; REAL_ADD_LID] o
               CONJUNCT2)] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma s1 s2 <=
                sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) * sqrt(&2) * pi`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma s1 s2 =
                  mfd_dist (top,atlas) g (gamma s1) (gamma s2)` SUBST1_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
      REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &1 / &2 <= sqrt(&1 - eps) /\ &0 <= sqrt(&1 + eps) /\ sqrt(&1 + eps) <= &2 /\
                &0 <= sqrt(&2) * pi /\ sqrt(&2) * pi <= &24 / &5` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SQRT2_PI] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_LT_0];
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC APXM_A7_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))`; `sqrt(&1 - eps)`; `sqrt(&1 + eps)`;
    `sqrt(&2) * pi`; `inv eps - abs sg`;
    `mfd_length atlas (g:A->real^3^3) gamma s1 u`; `mfd_length atlas (g:A->real^3^3) gamma u s2`;
    `mfd_length atlas (g:A->real^3^3) gamma s1 s2`] THEN
  ASM_REWRITE_TAC[]);;

(* A closed sub-piece around [p,q] inside the neck, half as long as the     *)
(* maximal piece (so of normalized length >= 1/(16 eps) when the maximal    *)
(* pieces around [p,q] are long), on which the core of A.4 applies          *)
(* (alpha' = 1/2).                                                          *)

let APXM_A7_SUBPIECE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b p q.
     &0 < eps /\ eps <= &1 / &8000 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!c d. a <= c /\ c <= p /\ q <= d /\ d <= b /\ c < d /\
            (!t. c < t /\ t < d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
            (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
            (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
            ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x))
                <= mfd_length atlas g gamma c d) /\
     a <= p /\ p <= q /\ q <= b /\
     (!t. p <= t /\ t <= q ==> gamma t IN IMAGE e (rfs_neck_dom eps))
     ==> ?c d f f1 f2.
           a <= c /\ c <= p /\ q <= d /\ d <= b /\ c < d /\
           (c < p \/ p = a) /\ (q < d \/ q = b) /\
           (!t. c <= t /\ t <= d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
           inv(&16 * eps) <=
           (sqrt(mfd_scalar atlas g x) * mfd_length atlas g gamma a b / (b - a)) * (d - c) /\
           !t. c <= t /\ t <= d
               ==> f t = apx_sfun (rfs_neck_dom eps) e (gamma t) /\
                   (f has_real_derivative f1 t) (atreal t) /\
                   (f1 has_real_derivative f2 t) (atreal t) /\
                   (&1 - &1 / &2) *
                   (sqrt(mfd_scalar atlas g x) * mfd_length atlas g gamma a b / (b - a))
                   < abs(f1 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                 `p:real`; `q:real`] APXM_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  SUBGOAL_THEN `inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
                <= mfd_length atlas g gamma c d` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `b:real`; `c:real`; `d:real`] APXM_CS_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c' = (c + p) / &2` THEN ABBREV_TAC `d' = (q + d) / &2` THEN
  SUBGOAL_THEN `a <= c' /\ c' <= p /\ q <= d' /\ d' <= b /\ c' < d' /\ c <= c' /\ d' <= d /\
                (d - c) / &2 <= d' - c'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c'"; "d'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) p IN IMAGE (e:real^3->A) (rfs_neck_dom eps) /\
                (gamma:real->A) q IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ASSUME `!t. p <= t /\ t <= q
                             ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c' < p \/ p = a) /\ (q < d' \/ q = b)` ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `c < p` THENL
       [DISJ1_TAC THEN EXPAND_TAC "c'" THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN SUBGOAL_THEN `c:real = p` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]];
      ASM_CASES_TAC `q < d` THENL
       [DISJ1_TAC THEN EXPAND_TAC "d'" THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN SUBGOAL_THEN `d:real = q` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c' <= t /\ t <= d'
                    ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `p <= t /\ t <= q` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `p:real`)) (concl th) &&
        can (find_term (fun u -> u = `q:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!t. c < t /\ t < d
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`) THEN
      MAP_EVERY EXPAND_TAC ["c'"; "d'"] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `a:real`; `b:real`; `c':real`; `d':real`] APXM_CS_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `V = mfd_length atlas (g:A->real^3^3) gamma a b / (b - a)` THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&16 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
                <= mfd_length atlas g gamma c' d'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&16 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) =
                  (inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x))) / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(V * (d - c)) / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x / &2 <= y / &2`) THEN ASM_MESON_TAC[];
      REWRITE_TAC[REAL_ARITH `(V * x) / &2 = V * x / &2`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_LT_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1 / &2`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `c':real`; `d':real`] APXM_A4_CORE) THEN
  SUBGOAL_THEN `inv(&100 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
                < mfd_length atlas g gamma c' d'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&16 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[prove(`(&1 / &2) pow 2 / &2000 = &1 / &8000`, CONV_TAC REAL_RAT_REDUCE_CONV)] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:real->real`
    (X_CHOOSE_THEN `f1:real->real` (X_CHOOSE_THEN `f2:real->real` ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`c':real`; `d':real`; `f:real->real`; `f1:real->real`;
                        `f2:real->real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
              (inv(&16 * eps) * inv(sqrt(mfd_scalar atlas g x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas (g:A->real^3^3) x)` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_LT_0]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(mfd_scalar atlas (g:A->real^3^3) x) * V) * (d' - c') =
                sqrt(mfd_scalar atlas g x) * mfd_length atlas g gamma c' d'` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]);;

let APXM_SFUN_BOUND = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) p.
     rfs_neck (top,atlas) g eps x e /\ p IN IMAGE e (rfs_neck_dom eps)
     ==> abs(apx_sfun (rfs_neck_dom eps) e p) < inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps)
                          (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`] APX_SFUN_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_PARAM_INJ]; DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[APX_SVAL_NECK_DOM]);;

(* Two times t1 < t2 on one level sphere are impossible: in one piece by    *)
(* strict monotonicity of s; across an exit, both pieces reach a common     *)
(* level at least 10 away from the ends (each piece is long), and the arc   *)
(* between the two crossings leaves the neck (APXM_A7_EXIT_CONTRA).         *)

let APXM_A7_ORDERED = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b r t1 t2.
     &0 < eps /\ eps <= &1 / &8000 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     (!c d. a <= c /\ c < d /\ d <= b /\ (c <= t1 /\ t1 <= d \/ c <= t2 /\ t2 <= d) /\
            (!t. c < t /\ t < d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
            (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
            (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
            ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x))
                <= mfd_length atlas g gamma c d) /\
     sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
     a <= t1 /\ t1 < t2 /\ t2 <= b /\
     gamma t1 IN IMAGE e (sphere(vec 0,r)) /\ gamma t2 IN IMAGE e (sphere(vec 0,r))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!c d. a <= c /\ c <= t1 /\ t2 <= d /\ d <= b /\ c < d /\
           (!t. c < t /\ t < d ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
           (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
           (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
           ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
               <= mfd_length atlas g gamma c d) /\
    (!c d. a <= c /\ c <= t1 /\ t1 <= d /\ d <= b /\ c < d /\
           (!t. c < t /\ t < d ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
           (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
           (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
           ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
               <= mfd_length atlas g gamma c d) /\
    (!c d. a <= c /\ c <= t2 /\ t2 <= d /\ d <= b /\ c < d /\
           (!t. c < t /\ t < d ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
           (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
           (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
           ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
               <= mfd_length atlas g gamma c d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN IMAGE (e:real^3->A) (rfs_neck_dom eps) /\
                gamma t2 IN IMAGE e (rfs_neck_dom eps)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t1) =
                sqrt(&2) * log r /\
                apx_sfun (rfs_neck_dom eps) e (gamma t2) = sqrt(&2) * log r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APXM_SFUN_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sg = sqrt(&2) * log r` THEN
  SUBGOAL_THEN `abs sg < inv eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t1) = sg`)) THEN
    MATCH_MP_TAC APXM_SFUN_BOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8000 <= inv eps /\ &500 <= inv(&16 * eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `inv(&1 / &8000)`; EXISTS_TAC `inv(&1 / &500)`] THEN
    (CONJ_TAC THENL
      [CONV_TAC REAL_RAT_REDUCE_CONV;
       MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                     mfd_length atlas g gamma a b / (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
      SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
        UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
        SIMP_TAC[rfs_neck; apx_shortest] THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `W = sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                  mfd_length atlas g gamma a b / (b - a)` THEN
  ASM_CASES_TAC `!t. t1 <= t /\ t <= t2
                     ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                   `a:real`; `b:real`; `t1:real`; `t2:real`] APXM_A7_SUBPIECE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `f:real->real`
      (X_CHOOSE_THEN `f1:real->real` (X_CHOOSE_THEN `f2:real->real`
        (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
    MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `c:real`; `d:real`]
                  APXM_STRICT_MONO) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) t1 = sg /\ f t2 = sg` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `!t. c <= t /\ t <= d
                        ==> (f:real->real) t =
                            apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t)`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
        MESON_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`); FIRST_X_ASSUM(MP_TAC o SPEC `t2:real`)] THEN
      ANTS_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t1:real`; `t2:real`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`t1:real`; `t2:real`])] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP] o check (fun th ->
    is_neg(concl th) && is_forall(rand(concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t1 <= b /\ a <= t2 /\
                (!t. t1 <= t /\ t <= t1
                     ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
                (!t. t2 <= t /\ t <= t2
                     ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `t:real = t1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `t:real = t2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `a:real`; `b:real`; `t1:real`; `t1:real`] APXM_A7_SUBPIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `f:real->real`
    (X_CHOOSE_THEN `f1:real->real` (X_CHOOSE_THEN `f2:real->real`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `a:real`; `b:real`; `t2:real`; `t2:real`] APXM_A7_SUBPIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `k:real->real`
    (X_CHOOSE_THEN `k1:real->real` (X_CHOOSE_THEN `k2:real->real`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  SUBGOAL_THEN `d1 < u /\ u < c2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) u IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
    REWRITE_TAC[] THENL
     [MATCH_MP_TAC(ASSUME `!t. c1 <= t /\ t <= d1
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`);
      MATCH_MP_TAC(ASSUME `!t. c2 <= t /\ t <= d2
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&10 <= inv eps - abs sg` THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                         `a:real`; `b:real`; `t1:real`; `u:real`; `t2:real`; `sg:real`]
                        APXM_A7_EXIT_CONTRA) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?sgs. &10 <= inv eps - abs sgs /\
                      (sgs <= sg /\ inv eps - &250 <= sgs \/
                       sg <= sgs /\ sgs <= --inv eps + &250)`
  (X_CHOOSE_THEN `sgs:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [ASM_CASES_TAC `&0 < sg` THENL
     [EXISTS_TAC `sg - &20`; EXISTS_TAC `sg + &20`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&250 <= ((&1 - &1 / &2) * W) * (d1 - c1) /\
                &250 <= ((&1 - &1 / &2) * W) * (d2 - c2)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. c1 <= t /\ t <= d1
                    ==> (f:real->real) t =
                        apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t) /\
                        --inv eps < f t /\ f t < inv eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `(gamma:real->A) t`]
                  APXM_SFUN_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2
                    ==> (k:real->real) t =
                        apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t) /\
                        --inv eps < k t /\ k t < inv eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `k1:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `(gamma:real->A) t`]
                  APXM_SFUN_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) t1 = sg /\ (k:real->real) t2 = sg` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `f:real->real`)) (concl th) &&
        not(can (find_term (fun u -> u = `f1:real->real`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPEC `t2:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `k:real->real`)) (concl th) &&
        not(can (find_term (fun u -> u = `k1:real->real`)) (concl th))))] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `c1:real`; `d1:real`;
                 `t1:real`; `(&1 - &1 / &2) * W`; `--inv eps`; `inv eps`; `sgs:real`]
                APXM_LEVEL_HIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`k:real->real`; `k1:real->real`; `k2:real->real`; `c2:real`; `d2:real`;
                 `t2:real`; `(&1 - &1 / &2) * W`; `--inv eps`; `inv eps`; `sgs:real`]
                APXM_LEVEL_HIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `k1:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                       `a:real`; `b:real`; `s1:real`; `u:real`; `s2:real`; `sgs:real`]
                      APXM_A7_EXIT_CONTRA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) s1 IN IMAGE (e:real^3->A) (rfs_neck_dom eps) /\
                (gamma:real->A) s2 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!t. c1 <= t /\ t <= d1
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`);
      MATCH_MP_TAC(ASSUME `!t. c2 <= t /\ t <= d2
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) s1) = sgs /\
                apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) s2) = sgs`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `f:real->real`)) (concl th) &&
        not(can (find_term (fun u -> u = `f1:real->real`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPEC `s2:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `k:real->real`)) (concl th) &&
        not(can (find_term (fun u -> u = `k1:real->real`)) (concl th))))] THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APXM_A7_CS = prove
 (`!u:A->bool. P2B_APX_A7_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_APX_A7_CS_STATEMENT] THEN
  EXISTS_TAC `&1 / &8000` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`] THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t1 < t2 \/ t1 = t2 \/ t2 < t1:real`) THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                         `a:real`; `b:real`; `r:real`; `t1:real`; `t2:real`]
                        APXM_A7_ORDERED) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                         `a:real`; `b:real`; `r:real`; `t2:real`; `t1:real`]
                        APXM_A7_ORDERED) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* A.8-CS (cap orientation, Y-hat, one crossing of the central              *)
(* sphere).                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A.8 infrastructure.  APXM_CAP_W0: for a neck e0 of a cap, oriented as the *)
(* end neck of APX22_CAP_ENDS_RAW (its low end inside the collar), the core  *)
(* K with the negative half e0(slab(-1/eps,0)) is open and its closure adds  *)
(* only the central sphere (the level t = 0 of APX21_CAP_ENDS, for a given   *)
(* neck).  APXM_A8_SETUP: the given neck of A.8-CS is so oriented (its       *)
(* negative half touches the core).                                          *)
(* ------------------------------------------------------------------------- *)

let APXM_CAP_W0 = prove
 (`!top atlas (e0:real^3->A) eps K U Cl CS d.
     hausdorff_space top /\ mfd_param top atlas (rfs_neck_dom eps) e0 /\
     &0 < eps /\ eps <= &1 / &1024 /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ closed_in top K /\
     open_in top (K UNION Cl) /\ Cl SUBSET CS /\ Cl SUBSET topspace top /\
     top closure_of Cl SUBSET K UNION CS /\
     &0 < d /\ d <= &1 /\
     IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl /\
     CS SUBSET IMAGE e0 (apx_slab (--inv eps) (--inv eps + &11))
     ==> open_in top (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) /\
         top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
         K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + &11))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--inv eps / sqrt(&2)) < exp((--inv eps + d / &2) / sqrt(&2)) /\
    exp((--inv eps + d / &2) / sqrt(&2)) <= exp((--inv eps + d) / sqrt(&2)) /\
    exp(&0 / sqrt(&2)) = &1 /\ &1 < exp(inv eps / sqrt(&2))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT; REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Mt = {y:real^3 | exp((--inv eps + d / &2) / sqrt(&2)) <= norm y /\
                               norm y <= &1}` THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e0:real^3->A) Mt)` ASSUME_TAC THENL
   [EXPAND_TAC "Mt" THEN MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_slab (--inv eps) (&0) SUBSET apx_slab (--inv eps) (--inv eps + d) UNION Mt /\
    Mt SUBSET apx_slab (--inv eps) (&0) UNION sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Mt" THEN
    REWRITE_TAC[apx_slab; SUBSET; annulus; IN_ELIM_THM; IN_UNION; IN_SPHERE_0] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) =
                  (K UNION Cl) UNION IMAGE e0 (apx_slab (--inv eps) (&0))` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(Cl:A->bool) SUBSET CS`;
                             `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))`] THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
        MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `K UNION top closure_of (Cl:A->bool) UNION IMAGE (e0:real^3->A) Mt` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[CLOSED_IN_UNION; CLOSED_IN_CLOSURE_OF] THEN
    MP_TAC(ISPECL [`top:A topology`; `Cl:A->bool`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET
                  IMAGE e0 (apx_slab (--inv eps) (--inv eps + d)) UNION IMAGE e0 Mt`
    MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (e0:real^3->A) (apx_slab (--inv eps) (--inv eps + d)) SUBSET Cl`;
        `(Cl:A->bool) SUBSET top closure_of Cl`] THEN
      SET_TAC[]];
    SUBGOAL_THEN `IMAGE (e0:real^3->A) Mt SUBSET
                  IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1))`
    MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`top closure_of (Cl:A->bool) SUBSET K UNION CS`;
        `(CS:A->bool) SUBSET IMAGE e0 (apx_slab (--inv eps) (&0))`] THEN
      SET_TAC[]]]);;

let APXM_A8_SETUP = prove
 (`!C top atlas (g:A->real^3^3) eps U Y x (e:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     rfs_cap (top,atlas) g C eps U Y /\
     rfs_neck (top,atlas) g eps x e /\
     IMAGE e (rfs_neck_dom eps) = U DIFF top closure_of Y /\
     ~(top closure_of (IMAGE e (apx_slab (--inv eps) (&0))) INTER top closure_of Y = {})
     ==> Y SUBSET top closure_of Y /\
         DISJOINT (top closure_of Y) (IMAGE e (rfs_neck_dom eps)) /\
         open_in top (top closure_of Y UNION IMAGE e (apx_slab (--inv eps) (&0))) /\
         top closure_of (top closure_of Y UNION IMAGE e (apx_slab (--inv eps) (&0))) SUBSET
         top closure_of Y UNION IMAGE e (apx_slab (--inv eps) (&0)) UNION
         IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  APX22_UNFOLD_ASM_TAC "apx_ch_ctx" apx_ch_ctx THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CAP_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ec:real^3->A` (X_CHOOSE_THEN `zc:A` (X_CHOOSE_THEN `e1:real^3->A`
      (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `top closure_of Y = (K:A->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `top closure_of Y = (K:A->bool)`
                          then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
                          else failwith "no") THEN
  SUBGOAL_THEN `closed_in top (K:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z1:A`; `e1:real^3->A`; `K:A->bool`;
                 `U:A->bool`] APX22_CAP_ENDS_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `Cl = IMAGE (e1:real^3->A) (annulus (&1) (&3 / &2))` THEN
  ABBREV_TAC `CS = IMAGE (e1:real^3->A) {y | &1 < norm y /\ norm y <= &3 / &2}` THEN
  SUBGOAL_THEN `(Cl:A->bool) SUBSET CS /\ (Cl:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Cl"; "CS"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K UNION Cl:A->bool` THEN
      REWRITE_TAC[SUBSET_UNION] THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e0:real^3->A) = e` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
      is_disj(concl th) && can (find_term (fun u -> u = `e0:real^3->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(e0:real^3->A) = apx_rev e`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APX_REV_IMAGE_SLAB; REAL_NEG_NEG;
                                REAL_ARITH `--(--x + &11) = x - &11`]) THEN
    UNDISCH_TAC `~(top closure_of (IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))) INTER K =
                   {})` THEN
    REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `K UNION Cl:A->bool` o CONJUNCT2) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
     [UNDISCH_TAC `(q:A) IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))` THEN
      SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET U DIFF K` MP_TAC THENL
       [FIRST_X_ASSUM(fun th -> if concl th = `IMAGE (e:real^3->A) (rfs_neck_dom eps) = U DIFF K`
          then REWRITE_TAC[SYM th] else failwith "no") THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(q:A) IN K` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) IN IMAGE (e:real^3->A) (apx_slab (inv eps - &11) (inv eps))` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(q:A) IN Cl`; `(Cl:A->bool) SUBSET CS`;
        `(CS:A->bool) SUBSET IMAGE (e:real^3->A) (apx_slab (inv eps - &11) (inv eps))`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(q:A) IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ (y2:real^3) IN rfs_neck_dom eps`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`--inv eps`; `&0`; `eps:real`] APX_SLAB_SUB_DOM);
        MP_TAC(ISPECL [`inv eps - &11`; `inv eps`; `eps:real`] APX_SLAB_SUB_DOM)] THEN
      (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^3) = y2` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `rfs_neck_dom eps`; `e:real^3->A`] MFD_PARAM_INJ) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(q:A) = (e:real^3->A) y1`; `(q:A) = (e:real^3->A) y2`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y1:real^3) IN apx_slab (--inv eps) (&0)` THEN
    UNDISCH_TAC `(y2:real^3) IN apx_slab (inv eps - &11) (inv eps)` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `eps:real`; `K:A->bool`; `U:A->bool`; `Cl:A->bool`; `CS:A->bool`; `d:real`]
                APXM_CAP_W0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN SET_TAC[]);;

(* Continuity of a curve at a time: a neighbourhood of times maps into an    *)
(* open set containing the image point.                                      *)

let APXM_CURVE_NEAR = prove
 (`!top (gamma:real->A) a b O c.
     continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
     open_in top O /\ a <= c /\ c <= b /\ gamma c IN O
     ==> ?del. &0 < del /\ !t. a <= t /\ t <= b /\ abs(t - c) < del ==> gamma t IN O`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O:A->bool` o CONJUNCT2 o REWRITE_RULE[continuous_map] o
    check (fun th -> can (find_term (fun u -> is_const u && fst(dest_const u) = "continuous_map"))
                         (concl th))) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; GSYM REAL_OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> ((gamma:real->A) t IN O <=> t IN V)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `{x | x IN real_interval[a,b] /\ (gamma:real->A) x IN O} =
                 V INTER real_interval[a,b]` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_REAL_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c IN (V:real->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `real_open (V:real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `del:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

(* Without a time on S in [u,w], a curve stays in or out of a closed set Yh *)
(* with Yh - S open.                                                         *)

let APXM_NO_CROSS = prove
 (`!top atlas (gamma:real->A) a b Yh S u w.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     mfd_c1_curve (top,atlas) gamma a b /\
     closed_in top Yh /\ open_in top (Yh DIFF S) /\
     a <= u /\ u <= w /\ w <= b /\ (!t. u <= t /\ t <= w ==> ~(gamma t IN S))
     ==> (gamma u IN Yh <=> gamma w IN Yh)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma a b` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real = w` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `u < w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) u w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                   `u:real`; `w:real`; `Yh:A->bool`] APXS_LAST_IN_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `a:real`; `b:real`; `Yh DIFF S:A->bool`;
                   `c:real`] APXM_CURVE_NEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC(ASSUME `!t. u <= t /\ t <= w ==> ~((gamma:real->A) t IN S)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `c + min (del / &2) (w - c)` (ASSUME
      `!t. c < t /\ t <= w ==> ~((gamma:real->A) t IN Yh)`)) THEN
    MP_TAC(SPEC `c + min (del / &2) (w - c)` (ASSUME
      `!t. a <= t /\ t <= b /\ abs(t - c) < del ==> (gamma:real->A) t IN Yh DIFF S`)) THEN
    PURE_REWRITE_TAC[IN_DIFF] THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p ==> r /\ s) ==> (q ==> ~r) ==> F`) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(\x. mat 1):A->real^3^3`; `gamma:real->A`; `u:real`; `w:real`]
                  MFD_LENGTH_REVERSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `\t. (gamma:real->A)(u + w - t)`; `u:real`; `w:real`; `Yh:A->bool`]
                  APXS_LAST_IN_CLOSED) THEN
    ASM_REWRITE_TAC[REAL_ARITH `u + w - u:real = w`; REAL_ARITH `u + w - w:real = u`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `a:real`; `b:real`; `Yh DIFF S:A->bool`;
                   `u + w - c:real`] APXM_CURVE_NEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC(ASSUME `!t. u <= t /\ t <= w ==> ~((gamma:real->A) t IN S)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `c + min (del / &2) (w - c)` (ASSUME
      `!t. c < t /\ t <= w ==> ~((gamma:real->A) (u + w - t) IN Yh)`)) THEN
    MP_TAC(SPEC `u + w - (c + min (del / &2) (w - c))` (ASSUME
      `!t. a <= t /\ t <= b /\ abs(t - (u + w - c)) < del
           ==> (gamma:real->A) t IN Yh DIFF S`)) THEN
    PURE_REWRITE_TAC[IN_DIFF] THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p ==> r /\ s) ==> (q ==> ~r) ==> F`) THEN
    ASM_REAL_ARITH_TAC]);;

(* The maximal piece in the neck through a time on the central sphere is    *)
(* long when the curve also passes outside the neck (at t0): its end on the *)
(* side of t0 lies outside the neck, so the exit bound from level 0 applies. *)

let APXM_PIECE_EXIT_LONG = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b c d p t0.
     &0 < eps /\ eps <= &1 / &2 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ apx_shortest (top,atlas) g gamma a b /\
     a <= c /\ c <= p /\ p <= d /\ d <= b /\
     (!t. c < t /\ t < d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
     (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
     (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps))) /\
     sphere(vec 0,&1) SUBSET rfs_neck_dom eps /\ gamma p IN IMAGE e (sphere(vec 0,&1)) /\
     a <= t0 /\ t0 <= b /\ ~(gamma t0 IN IMAGE e (rfs_neck_dom eps))
     ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x)) <= mfd_length atlas g gamma c d`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  UNDISCH_TAC `(gamma:real->A) p IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ apx_sval y = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) c d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `c:real`; `p:real`; `d:real`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^3^3) gamma c p /\
                &0 <= mfd_length atlas (g:A->real^3^3) gamma p d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <=
                sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) * inv eps`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t0 < p` THENL
   [SUBGOAL_THEN `t0 <= c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((gamma:real->A) t0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!t. c < t /\ t < d
                               ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((gamma:real->A) c IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
        is_disj(concl th) && can (find_term (fun u -> u = `c:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `t0:real = a` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `c:real`; `p:real`] MFD_LENGTH_REVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                   `\t. (gamma:real->A)(c + p - t)`; `c:real`; `p:real`] APX_NECK_EXIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `c + p - c:real = p`; REAL_ARITH `c + p - p:real = c`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p < t0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= t0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(ASSUME `!t. c < t /\ t < d
                             ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) d IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && can (find_term (fun u -> u = `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t0:real = b` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                 `gamma:real->A`; `p:real`; `d:real`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC);;

(* Membership in Y-hat = K + e(|y| <= 1) for points of the neck.             *)

let APXM_YH_NECK = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) K y.
     rfs_neck (top,atlas) g eps x e /\ DISJOINT K (IMAGE e (rfs_neck_dom eps)) /\
     y IN rfs_neck_dom eps
     ==> (e y IN K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
          apx_sval y <= &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps)
                          (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e:real^3->A) y IN K)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM; NORM_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(y:real^3) <= &1` THEN CONJ_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `rfs_neck_dom eps`; `e:real^3->A`] MFD_PARAM_INJ) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    MP_TAC(SPECL [`log(norm(y:real^3))`; `&0`; `sqrt(&2)`] REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`norm(y:real^3)`; `&1`] LOG_MONO_LE) THEN
    ASM_REWRITE_TAC[LOG_1; REAL_LT_01] THEN MESON_TAC[]]);;

let APXM_YH_SFUN = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) K p.
     rfs_neck (top,atlas) g eps x e /\ DISJOINT K (IMAGE e (rfs_neck_dom eps)) /\
     p IN IMAGE e (rfs_neck_dom eps)
     ==> (p IN K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
          apx_sfun (rfs_neck_dom eps) e p <= &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps)
                          (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`] APX_SFUN_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_PARAM_INJ]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC APXM_YH_NECK THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`] THEN
  ASM_REWRITE_TAC[]);;

(* A.8 KEY: a constant-speed minimizer that passes outside the neck crosses *)
(* the central sphere at most once (A7_ORDERED with r = 1; the pieces       *)
(* through the crossings are long by APXM_PIECE_EXIT_LONG).                  *)

let APXM_A8_KEY = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b t0 t1 t2.
     &0 < eps /\ eps <= &1 / &8000 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     a <= t0 /\ t0 <= b /\ ~(gamma t0 IN IMAGE e (rfs_neck_dom eps)) /\
     a <= t1 /\ t1 < t2 /\ t2 <= b /\
     gamma t1 IN IMAGE e (sphere(vec 0,&1)) /\ gamma t2 IN IMAGE e (sphere(vec 0,&1))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                       `a:real`; `b:real`; `&1`; `t1:real`; `t2:real`] APXM_A7_ORDERED) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun u -> u = `t1:real`)) (concl th))) THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                         `a:real`; `b:real`; `c:real`; `d:real`; `t1:real`; `t0:real`]
                        APXM_PIECE_EXIT_LONG);
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                         `a:real`; `b:real`; `c:real`; `d:real`; `t2:real`; `t0:real`]
                        APXM_PIECE_EXIT_LONG)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A.8 CROSS: at a crossing ts of the central sphere strictly inside (a,b), *)
(* the s-function is strictly monotone through 0 on a sub-piece, so Y-hat    *)
(* membership differs just before and just after ts.                         *)

let APXM_A8_CROSS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) gamma a b K t0 ts.
     &0 < eps /\ eps <= &1 / &8000 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ DISJOINT K (IMAGE e (rfs_neck_dom eps)) /\
     apx_shortest (top,atlas) g gamma a b /\ a < b /\
     (!t. t IN real_interval[a,b]
          ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
     a <= t0 /\ t0 <= b /\ ~(gamma t0 IN IMAGE e (rfs_neck_dom eps)) /\
     a < ts /\ ts < b /\ gamma ts IN IMAGE e (sphere(vec 0,&1))
     ==> ?tm tp. a <= tm /\ tm < ts /\ ts < tp /\ tp <= b /\
                 ~(gamma tm IN K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
                   gamma tp IN K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) ts IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!c d. a <= c /\ c <= ts /\ ts <= d /\ d <= b /\ c < d /\
           (!t. c < t /\ t < d ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
           (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
           (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
           ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))
               <= mfd_length atlas g gamma c d) /\
    (!t. ts <= t /\ t <= ts ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
    a <= ts /\ ts <= b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                           `a:real`; `b:real`; `c:real`; `d:real`; `ts:real`; `t0:real`]
                          APXM_PIECE_EXIT_LONG) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `t:real = ts` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `a:real`; `b:real`; `ts:real`; `ts:real`] APXM_A7_SUBPIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `f:real->real`
    (X_CHOOSE_THEN `f1:real->real` (X_CHOOSE_THEN `f2:real->real`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  SUBGOAL_THEN `c < ts /\ ts < d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term (fun u -> u = `ts:real`)) (concl th) &&
      not(can (find_term (fun u -> u = `IMAGE (e:real^3->A) (rfs_neck_dom eps)`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(mfd_scalar atlas (g:A->real^3^3) x) *
                     mfd_length atlas g gamma a b / (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
      SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
        UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
        SIMP_TAC[rfs_neck; apx_shortest] THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f1:real->real`; `f2:real->real`; `c:real`; `d:real`]
                APXM_STRICT_MONO) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `!t. c <= t /\ t <= d
                    ==> (f:real->real) t =
                        apx_sfun (rfs_neck_dom eps) (e:real^3->A) ((gamma:real->A) t)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) ts = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ts:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `log(&1) = &0` (fun th -> REWRITE_TAC[GSYM th; REAL_MUL_RZERO]) THENL
     [REWRITE_TAC[LOG_1]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `&1`;
                   `(gamma:real->A) ts`] APXM_SFUN_SPHERE) THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. c <= t /\ t <= d
        ==> ((gamma:real->A) t IN K UNION
                IMAGE (e:real^3->A) {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
             (f:real->real) t <= &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f:real->real`)) (concl th) &&
      not(can (find_term (fun u -> u = `f1:real->real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC APXM_YH_SFUN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `c:real`)) (concl th) &&
      can (find_term (fun u -> u = `IMAGE (e:real^3->A) (rfs_neck_dom eps)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d:real`] THEN
  SUBGOAL_THEN
   `((gamma:real->A) c IN K UNION
       IMAGE (e:real^3->A) {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
     (f:real->real) c <= &0) /\
    ((gamma:real->A) d IN K UNION
       IMAGE (e:real^3->A) {z | z IN rfs_neck_dom eps /\ norm z <= &1} <=>
     (f:real->real) d <= &0)` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `f:real->real`)) (concl th) &&
      can (find_term (fun u -> u = `K:A->bool`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun u -> u = `f1:real->real`)) (concl th))) THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`c:real`; `ts:real`] th) THEN
                            MP_TAC(SPECL [`ts:real`; `d:real`] th));
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`c:real`; `ts:real`] th) THEN
                            MP_TAC(SPECL [`ts:real`; `d:real`] th))] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;

(* Y-hat = K + e(|y| <= 1) is closed, Y-hat - S is open (S the central     *)
(* sphere), from the level-0 facts of APXM_A8_SETUP.                        *)

let APXM_A8_YH = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) K.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024 /\
     DISJOINT K (IMAGE e (rfs_neck_dom eps)) /\
     open_in top (K UNION IMAGE e (apx_slab (--inv eps) (&0))) /\
     top closure_of (K UNION IMAGE e (apx_slab (--inv eps) (&0))) SUBSET
     K UNION IMAGE e (apx_slab (--inv eps) (&0)) UNION IMAGE e (sphere(vec 0,&1))
     ==> closed_in top (K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1}) /\
         open_in top ((K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1}) DIFF
                      IMAGE e (sphere(vec 0,&1))) /\
         IMAGE e (sphere(vec 0,&1)) SUBSET
         K UNION IMAGE e {z | z IN rfs_neck_dom eps /\ norm z <= &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps)
                          (e:real^3->A) /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < &1 /\ &1 < exp(inv eps / sqrt(&2)) /\
                exp(&0 / sqrt(&2)) = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT; REAL_MUL_LNEG] THEN
      REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{z:real^3 | z IN rfs_neck_dom eps /\ norm z <= &1} =
                apx_slab (--inv eps) (&0) UNION sphere(vec 0,&1) /\
                DISJOINT (apx_slab (--inv eps) (&0)) (sphere(vec 0,&1):real^3->bool) /\
                apx_slab (--inv eps) (&0) SUBSET rfs_neck_dom eps /\
                sphere(vec 0,&1) SUBSET rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; annulus; EXTENSION; IN_ELIM_THM; IN_UNION;
                IN_SPHERE_0; DISJOINT; IN_INTER; NOT_IN_EMPTY; SUBSET] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)))
                         (IMAGE e (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z1:real^3) = z2` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `rfs_neck_dom eps`; `e:real^3->A`] MFD_PARAM_INJ) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`(q:A) = (e:real^3->A) z1`; `(q:A) = (e:real^3->A) z2`] THEN
      MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e (rfs_neck_dom eps)`
  ASSUME_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e:real^3->A) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `sphere(vec 0,&1) = {y:real^3 | &1 <= norm y /\ norm y <= &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC APX22_SHELL_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_UNION] THEN
  SUBGOAL_THEN
   `(K UNION IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)) UNION IMAGE e (sphere(vec 0,&1)))
    DIFF IMAGE e (sphere(vec 0,&1)) = K UNION IMAGE e (apx_slab (--inv eps) (&0))`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT K (IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
      `DISJOINT (IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))) (IMAGE e (sphere(vec 0,&1)))`;
      `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE e (rfs_neck_dom eps)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `K UNION IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))`]
                    OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `K UNION IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))`]
                    OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_ASSOC; CLOSURE_OF_UNION] THEN
  MP_TAC(ISPECL [`top:A topology`; `IMAGE (e:real^3->A) (sphere(vec 0,&1))`] CLOSURE_OF_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM CLOSURE_OF_UNION] THEN
  UNDISCH_TAC `top closure_of (K UNION IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))) SUBSET
               K UNION IMAGE e (apx_slab (--inv eps) (&0)) UNION IMAGE e (sphere(vec 0,&1))` THEN
  REWRITE_TAC[CLOSURE_OF_UNION] THEN SET_TAC[]);;

(* A.8-CS: a constant-speed minimizer meeting the core Y meets              *)
(* Y-hat = cl Y + e(|y| <= 1) in an interval containing an end point.       *)

let APXM_A8_CS = prove
 (`!u:A->bool. APX_A8_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A8_CS_STATEMENT] THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `ec:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `en:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))) THEN
  EXISTS_TAC `min ec (min en (&1 / &8000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`;
                       `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  SUBGOAL_THEN `eps <= ec /\ eps <= en /\ eps <= &1 / &8000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) eps /\ apx_ch_n4r top atlas g eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ctx" (fun th -> MP_TAC(SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`] th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "n4r" (fun th -> MP_TAC(SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`] th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`; `e:real^3->A`]
                APXM_A8_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `K = top closure_of (Y:A->bool)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `K:A->bool`] APXM_A8_YH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `Yh = K UNION IMAGE (e:real^3->A) {z | z IN rfs_neck_dom eps /\ norm z <= &1}` THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma a b` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t0 IN Yh /\
                ~((gamma:real->A) t0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
                (S:A->bool) SUBSET IMAGE e (rfs_neck_dom eps)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Yh" THEN ASM SET_TAC[];
      ASM SET_TAC[];
      EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* constancy of membership away from S *)
  SUBGOAL_THEN `!u w. a <= u /\ u <= w /\ w <= b /\
                      (!t. u <= t /\ t <= w ==> ~((gamma:real->A) t IN S))
                      ==> (gamma u IN Yh <=> gamma w IN Yh)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC APXM_NO_CROSS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `a:real`; `b:real`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?ts. a <= ts /\ ts <= b /\ (gamma:real->A) ts IN S` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!t. a <= t /\ t <= b ==> ~((gamma:real->A) t IN S)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM] o check (fun th ->
        is_neg(concl th) && is_exists(rand(concl th)))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(REAL_ARITH `t <= t0 \/ t0 <= t:real`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `t0:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun u -> u = `Yh:A->bool`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `t:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun u -> u = `Yh:A->bool`)) (concl th)))] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
       SIMP_TAC[]])] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ts:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b /\ (gamma:real->A) t IN S ==> t = ts` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t < ts \/ t = ts \/ ts < t:real`) THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                           `a:real`; `b:real`; `t0:real`; `t:real`; `ts:real`] APXM_A8_KEY) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                           `a:real`; `b:real`; `t0:real`; `ts:real`; `t:real`] APXM_A8_KEY) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u w. a <= u /\ u <= w /\ w < ts ==> ((gamma:real->A) u IN Yh <=> gamma w IN Yh)) /\
    (!u w. ts < u /\ u <= w /\ w <= b ==> ((gamma:real->A) u IN Yh <=> gamma w IN Yh))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
      can (find_term (fun v -> v = `S:A->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    (SUBGOAL_THEN `t:real = ts` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term (fun v -> v = `ts:real`)) (concl th) &&
         can (find_term (fun v -> v = `S:A->bool`)) (concl th))) THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t0:real = ts) /\ (gamma:real->A) ts IN Yh /\ (gamma:real->A) t0 IN Yh`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((gamma:real->A) t0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t0 < ts` THENL
   [MAP_EVERY EXISTS_TAC [`a:real`; `ts:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t < ts` THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      DISJ_CASES_TAC(REAL_ARITH `t <= t0 \/ t0 <= t:real`) THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `t0:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th)));
        FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `t:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th)))] THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real = ts` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `ts < t /\ a < ts /\ ts < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                   `a:real`; `b:real`; `K:A->bool`; `t0:real`; `ts:real`] APXM_A8_CROSS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tm:real` (X_CHOOSE_THEN `tp:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(gamma:real->A) tm IN Yh` ASSUME_TAC THENL
     [DISJ_CASES_TAC(REAL_ARITH `tm <= t0 \/ t0 <= tm:real`) THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`tm:real`; `t0:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th)));
        FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `tm:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th)))] THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((gamma:real->A) tp IN Yh)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((gamma:real->A) t IN Yh)` (fun th -> REWRITE_TAC[th]) THENL
     [DISJ_CASES_TAC(REAL_ARITH `t <= tp \/ tp <= t:real`) THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `tp:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
          not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))));
        FIRST_X_ASSUM(MP_TAC o SPECL [`tp:real`; `t:real`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
          can (find_term (fun v -> v = `ts:real`)) (concl th) &&
          can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
          not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))))] THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts < t0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ts:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ts < t` THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISJ_CASES_TAC(REAL_ARITH `t <= t0 \/ t0 <= t:real`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `t0:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `t:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))))] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real = ts` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `t < ts /\ a < ts /\ ts < b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`;
                 `a:real`; `b:real`; `K:A->bool`; `t0:real`; `ts:real`] APXM_A8_CROSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:real` (X_CHOOSE_THEN `tp:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(gamma:real->A) tp IN Yh` ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `tp <= t0 \/ t0 <= tp:real`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`tp:real`; `t0:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `tp:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `b:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))))] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) tm IN Yh)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) t IN Yh)` (fun th -> REWRITE_TAC[th]) THENL
   [DISJ_CASES_TAC(REAL_ARITH `t <= tm \/ tm <= t:real`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `tm:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPECL [`tm:real`; `t:real`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun v -> v = `a:real`)) (concl th) &&
        can (find_term (fun v -> v = `ts:real`)) (concl th) &&
        can (find_term (fun v -> v = `Yh:A->bool`)) (concl th) &&
        not(can (find_term (fun v -> v = `S:A->bool`)) (concl th))))] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;


