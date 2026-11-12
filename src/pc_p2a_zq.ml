(* ========================================================================= *)
(* Unit pc_p2a_zq: the Z/2-quotient cylinder model contains no line.         *)
(* Headline P2A985_ZQ_NO_LINE: for a Riemannian 3-manifold covered           *)
(* two-to-one by R^3 minus 0 through a map p with p y = p z <=> z = y or z = *)
(* rfs_twist y, local parametrizations on small balls and pullback metric c  *)
(* cylinder_flow(0) (the time-0 slice of the second alternative of           *)
(* p2b_cyl_model), no unit-speed line exists.  Proof: the height H(p y) =    *)
(* abs(apx_sval y) is well defined; it is 1/sqrt(c)-Lipschitz (local lifts,  *)
(* APX_SVAL_LENGTH_LOWER, continuous induction), and d(x1,x2) <= sqrt(c)     *)
(* (abs(H x1 - H x2) + sqrt 2 pi) since both points have lifts with norm >=  *)
(* 1 (APX_MODEL_PATH on norm > 1, where p is injective).  On a line,         *)
(* H(lam(-T)), H(lam T) <= H(lam 0) + T/sqrt c and both are >= 0, so 2T <=   *)
(* sqrt c (H(lam 0) + T/sqrt c + sqrt 2 pi): impossible for large T.  Used   *)
(* for MT Lemma 9.84 (pc_p2a_l984) and the A5L route (pc_p2b_a5l).           *)
(* ========================================================================= *)

needs "src/pc_apx_neck.ml";;
needs "src/pc_smt_product.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Helpers copied from units outside this closure (proofs unchanged up to    *)
(* renaming): speeds of e o c for a parametrization e (APXM_PARAM_SPEED of   *)
(* pc_apx_mincs), speeds depend only on the curve on [a,b] (P2A_SPEED_EQ of  *)
(* pc_p2a_minr), real induction (P3N_RIND of pc_p3_s16l15).                  *)
(* ========================================================================= *)

let p2azq_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* from pc_apx_mincs.ml *)
let P2AZQ_PARAM_SPEED = prove
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

(* from pc_p2a_minr.ml *)
let P2AZQ_SPEED_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
     gamma' a b t.
        (!s. s IN real_interval[a,b] ==> gamma s = gamma' s) /\
        t IN real_interval[a,b]
        ==> mfd_speed atlas g gamma a b t = mfd_speed atlas g gamma' a b t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `gamma':real->A`; `a:real`; `b:real`; `t:real`]
         GRGD_VELOCITY_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t = gamma' t` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; REFL_TAC]);;

(* from pc_p3_s16l15.ml *)
let P2AZQ_RIND = prove
 (`!P a b. a <= b /\ P a /\
     (!x. a <= x /\ x < b /\ (!y. a <= y /\ y <= x ==> P y)
          ==> ?d. &0 < d /\ !y. x < y /\ y < x + d /\ y <= b ==> P y) /\
     (!x. a < x /\ x <= b /\ (!y. a <= y /\ y < x ==> P y) ==> P x)
     ==> !x. a <= x /\ x <= b ==> P x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "right") (LABEL_TAC "left")))) THEN
  ABBREV_TAC `S = {x | a <= x /\ x <= b /\ !y. a <= y /\ y <= x ==> (P:real->bool) y}` THEN
  SUBGOAL_THEN `(a:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real = a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `a:real` THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `b:real` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `s = sup S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `a <= s /\ s <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "lub" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. a <= y /\ y < s ==> (P:real->bool) y` (LABEL_TAC "below") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x. x IN S /\ y < x` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `s <= y` MP_TAC THENL
       [USE_THEN "lub" MATCH_MP_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real->bool) s` ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real = a` THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. a <= y /\ y <= s ==> (P:real->bool) y` (LABEL_TAC "upto") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_CASES_TAC `y:real = s` THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = b` ASSUME_TAC THENL
   [ASM_CASES_TAC `s < b` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "right" (MP_TAC o C MP (end_itlist CONJ
      [ASSUME `a <= s`; ASSUME `s < b`; ASSUME `!y. a <= y /\ y <= s ==> (P:real->bool) y`]) o
      SPEC `s:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
    SUBGOAL_THEN `min (s + d / &2) b IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_CASES_TAC `y <= s` THENL
       [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "d" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN
      SUBGOAL_THEN `min (s + d / &2) b <= s` MP_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The twist and the height.  rfs_twist y = -y/|y|^2 has norm 1/|y| and      *)
(* apx_sval(rfs_twist y) = -apx_sval y; so abs(apx_sval y) depends only on p *)
(* y (the height p2azq_height), every point has a lift of norm >= 1, and p   *)
(* is injective on norm > 1, where it is a parametrization                   *)
(* (MFP_PARAM_LOCAL).                                                        *)
(* ========================================================================= *)

let P2AZQ_TWIST_FACTS = prove
 (`!y:real^3. ~(y = vec 0)
     ==> ~(rfs_twist y = vec 0) /\ norm(rfs_twist y) = inv(norm y) /\
         apx_sval(rfs_twist y) = --(apx_sval y)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(rfs_twist (y:real^3)) = inv(norm y)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    REWRITE_TAC[apx_sval] THEN ASM_SIMP_TAC[LOG_INV] THEN REAL_ARITH_TAC]);;

(* The structural hypotheses of the two-to-one model, as a predicate. *)

let p2azq_model = new_definition
 `p2azq_model (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
              (p:real^3->B) (c:real) <=>
    smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
    IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
    (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
    (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
    (!y. ~(y = vec 0) ==> rfs_pullback atlas p g y = c %% cylinder_flow (&0) y)`;;

let p2azq_height = new_definition
 `p2azq_height (p:real^3->B) (x:B) =
    @h. ?y. ~(y = vec 0) /\ p y = x /\ h = abs(apx_sval y)`;;

let P2AZQ_HEIGHT = prove
 (`!top atlas (g:B->real^3^3) p c y.
     p2azq_model (top,atlas) g p c /\ ~(y = vec 0)
     ==> p2azq_height p (p y) = abs(apx_sval y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2azq_model] THEN STRIP_TAC THEN
  REWRITE_TAC[p2azq_height] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `h:real` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `z:real^3`] o check (fun th ->
      p2azq_mentions "rfs_twist" th)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `y:real^3` P2AZQ_TWIST_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NEG];
    DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]);;

(* Every point has a lift of norm >= 1, with height apx_sval. *)

let P2AZQ_LIFT_GE1 = prove
 (`!top atlas (g:B->real^3^3) p c x.
     p2azq_model (top,atlas) g p c /\ x IN topspace top
     ==> ?y. &1 <= norm y /\ p y = x /\ p2azq_height p x = apx_sval y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  SUBGOAL_THEN `?y:real^3. ~(y = vec 0) /\ p y = (x:B)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN topspace top` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      p2azq_mentions "IMAGE" th && is_eq(concl th))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= norm(y:real^3)` THENL
   [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(p:real^3->B) y = x`)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:real^3->B`; `c:real`; `y:real^3`] P2AZQ_HEIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ABS_REFL; apx_sval] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real^3` P2AZQ_TWIST_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `rfs_twist (y:real^3)` THEN
  SUBGOAL_THEN `(p:real^3->B)(rfs_twist y) = x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(p:real^3->B) y = x`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `rfs_twist (y:real^3)`] o check (fun th ->
      p2azq_mentions "rfs_twist" th && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(p:real^3->B)(rfs_twist y) = x`)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `rfs_twist (y:real^3)`] P2AZQ_HEIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN REWRITE_TAC[apx_sval] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> &0 <= --x`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REAL_ARITH_TAC);;

(* p is a parametrization on norm > 1. *)

let P2AZQ_PARAM_OUT = prove
 (`!top atlas (g:B->real^3^3) p c.
     p2azq_model (top,atlas) g p c ==> mfd_param top atlas {y:real^3 | &1 < norm y} p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model]) THEN
  MATCH_MP_TAC MFP_PARAM_LOCAL THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &1 < norm y} = (:real^3) DIFF cball(vec 0,&1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE];
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_CBALL]];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `z:real^3`] o check (fun th ->
      p2azq_mentions "rfs_twist" th && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `y:real^3` P2AZQ_TWIST_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `&1 < norm(z:real^3)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      p2azq_mentions "mfd_param" th && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,min r (norm y - &1))` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_MIN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; REAL_LT_MIN] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`y:real^3`; `z:real^3`] NORM_TRIANGLE_SUB) THEN
      UNDISCH_TAC `dist(y:real^3,z) < norm y - &1` THEN REWRITE_TAC[dist] THEN
      CONV_TAC NORM_ARITH;
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Distances between points with lifts of norm > 1 are at most sqrt(c)       *)
(* (abs(difference of s-values) + sqrt 2 pi): the model path of              *)
(* APX_MODEL_PATH in norm > 1, pushed by the parametrization p               *)
(* (P2AZQ_PARAM_SPEED), whose length scales by sqrt c.                       *)
(* ========================================================================= *)

let P2AZQ_OPEN_OUT = prove
 (`open {y:real^3 | &1 < norm y} /\ (!y:real^3. y IN {y | &1 < norm y} ==> ~(y = vec 0))`,
  CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &1 < norm y} = (:real^3) DIFF cball(vec 0,&1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE];
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_CBALL]];
    REWRITE_TAC[IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC]);;

(* The length of p o c0 is sqrt(c) times the cylinder length of c0, for a   *)
(* model curve c0 in an open set s inside R^3 minus 0 on which p is a       *)
(* parametrization.                                                          *)

let P2AZQ_PUSH_LENGTH = prove
 (`!top atlas (g:B->real^3^3) p c s (c0:real->real^3) a b.
     p2azq_model (top,atlas) g p c /\ open s /\ (!y. y IN s ==> ~(y = vec 0)) /\
     mfd_param top atlas s p /\
     mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c0 a b /\ a < b
     ==> mfd_c1_curve (top,atlas) (p o c0) a b /\
         mfd_length atlas g (p o c0) a b =
         sqrt c * mfd_length (open_set_atlas s) (cylinder_flow (&0)) c0 a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `s:real^3->bool`; `p:real^3->B`; `\y:real^3. c %% cylinder_flow (&0) y`;
                 `c0:real->real^3`; `a:real`; `b:real`] P2AZQ_PARAM_SPEED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      p2azq_mentions "rfs_pullback" th)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfs_pullback] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REFL_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "spd")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (s:real^3->bool)) (cylinder_flow (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (s:real^3->bool))
                                      (open_set_atlas s)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^3->bool)`; `open_set_atlas (s:real^3->bool)`;
                 `cylinder_flow (&0)`; `c0:real->real^3`; `a:real`; `b:real`; `c:real`]
                MFD_LENGTH_SCALE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN USE_THEN "spd" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2AZQ_DIST_UP_STRICT = prove
 (`!top atlas (g:B->real^3^3) p c y1 y2.
     p2azq_model (top,atlas) g p c /\ &1 < norm y1 /\ &1 < norm y2
     ==> mfd_joinable (top,atlas) (p y1) (p y2) /\
         mfd_dist (top,atlas) g (p y1) (p y2) <=
         sqrt c * (abs(apx_sval y1 - apx_sval y2) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  MP_TAC(ISPECL [`{y:real^3 | &1 < norm y}`; `y1:real^3`; `y2:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2AZQ_OPEN_OUT; GSYM NORM_POS_LT; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `{y:real^3 | &1 < norm y}`; `c0:real->real^3`;
                 `&0`; `&1`] P2AZQ_PUSH_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2AZQ_OPEN_OUT; REAL_LT_01] THEN MATCH_MP_TAC P2AZQ_PARAM_OUT THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c:real`] THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) y1 = (p o c0) (&0) /\ p y2 = (p o c0) (&1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:B->real^3^3) ((p:real^3->B) o (c0:real->real^3)) (&0) (&1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Local Lipschitz bound for the height along C1 curves.  Near each time the *)
(* curve stays in p(ball(y0,r)) for a param ball around a lift y0; there it  *)
(* equals p o (e' o gamma) for the inverse e' of GRGD_PARAM_FACTS, and       *)
(* APX_SVAL_LENGTH_LOWER together with the length scaling of                 *)
(* P2AZQ_PUSH_LENGTH gives the bound.                                        *)
(* ========================================================================= *)

let P2AZQ_BALL_AVOID = prove
 (`!y0:real^3 r. r < norm y0
     ==> open(ball(y0,r)) /\ (!y. y IN ball(y0,r) ==> ~(y = vec 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[OPEN_BALL; IN_BALL] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `dist(y0:real^3,vec 0) < r` THEN REWRITE_TAC[DIST_0] THEN
  ASM_REAL_ARITH_TAC);;

let P2AZQ_LOCAL_LIP = prove
 (`!top atlas (g:B->real^3^3) p c (gamma:real->B) a b x.
     p2azq_model (top,atlas) g p c /\ mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
     x IN real_interval[a,b]
     ==> ?d. &0 < d /\
             !t1 t2. a <= t1 /\ t1 < t2 /\ t2 <= b /\ x - d < t1 /\ t2 < x + d
                     ==> sqrt c * abs(p2azq_height p (gamma t2) -
                                      p2azq_height p (gamma t1))
                         <= mfd_length atlas g gamma t1 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  SUBGOAL_THEN `(gamma:real->B) x IN IMAGE (p:real^3->B) {y:real^3 | ~(y = vec 0)}`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `gamma:real->B`; `a:real`; `b:real`; `x:real`]
                  MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y0:real^3` o
    check (fun th -> p2azq_mentions "mfd_param" th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`y0:real^3`; `r:real`] P2AZQ_BALL_AVOID) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(y0:real^3,r)`; `p:real^3->B`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `gamma:real->B`;
                 `a:real`; `b:real`; `IMAGE (p:real^3->B) (ball(y0,r))`; `x:real`]
                GRGD_CURVE_TIMES_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "win"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[t1,t2] ==> (gamma:real->B) t IN IMAGE p (ball(y0:real^3,r))`
  (LABEL_TAC "inW") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    USE_THEN "win" (MP_TAC o SPEC `lift t`) THEN
    REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; IN_REAL_INTERVAL; DIST_LIFT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((B->bool)#(B->real^3))->bool) (gamma:real->B) t1 t2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (subtopology euclidean (ball(y0:real^3,r)),open_set_atlas (ball(y0,r)))
                 ((e':B->real^3) o (gamma:real->B)) t1 t2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `subtopology euclidean (ball(y0:real^3,r))`;
                         `open_set_atlas (ball(y0:real^3,r))`;
                         `IMAGE (p:real^3->B) (ball(y0,r))`; `e':B->real^3`;
                         `gamma:real->B`; `t1:real`; `t2:real`] GRGD_C1_CURVE_PUSH) THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[t1,t2]
        ==> p2azq_height (p:real^3->B) ((gamma:real->B) t) =
            abs(apx_sval(((e':B->real^3) o gamma) t))` (LABEL_TAC "ht") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "inW" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[t1,t2]`))) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(e':B->real^3) ((p:real^3->B) y) = y` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2AZQ_HEIGHT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[t1,t2]
        ==> (gamma:real->B) t = ((p:real^3->B) o (e':B->real^3) o gamma) t`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:B->real^3^3) (gamma:real->B) t1 t2 =
    mfd_length atlas g ((p:real^3->B) o (e':B->real^3) o gamma) t1 t2`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN USE_THEN "eq" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `ball(y0:real^3,r)`;
                 `(e':B->real^3) o (gamma:real->B)`; `t1:real`; `t2:real`]
                P2AZQ_PUSH_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `t1 IN real_interval[t1,t2] /\ t2 IN real_interval[t1,t2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ht" (fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `t1 IN real_interval[t1,t2]`);
                MATCH_MP th (ASSUME `t2 IN real_interval[t1,t2]`)]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(apx_sval(((e':B->real^3) o (gamma:real->B)) t2) -
                  apx_sval((e' o gamma) t1))` THEN
  REWRITE_TAC[REAL_ABS_SUB_ABS] THEN
  MATCH_MP_TAC APX_SVAL_LENGTH_LOWER THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The height is 1/sqrt(c)-Lipschitz along every C1 curve (continuous        *)
(* induction P2AZQ_RIND over the local bound above, lengths added by         *)
(* MFD_LENGTH_COMBINE), hence for the distance (APX_DIST_GE_CURVES).         *)
(* ========================================================================= *)

let P2AZQ_COMBINE_ARITH = prove
 (`!s h0 h1 h2 l1 l2 l.
     &0 <= s /\ s * abs(h1 - h0) <= l1 /\ s * abs(h2 - h1) <= l2 /\ l = l1 + l2
     ==> s * abs(h2 - h0) <= l`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s * abs(h1 - h0) + s * abs(h2 - h1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]]);;

let P2AZQ_CURVE_LIP = prove
 (`!top atlas (g:B->real^3^3) p c (gamma:real->B) a b.
     p2azq_model (top,atlas) g p c /\ mfd_c1_curve (top,atlas) gamma a b
     ==> sqrt c * abs(p2azq_height p (gamma b) - p2azq_height p (gamma a)) <=
         mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; REAL_SUB_REFL; REAL_ABS_0;
                REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sqrt c * abs(p2azq_height (p:real^3->B) ((gamma:real->B) t) -
                                   p2azq_height p (gamma a)) <=
                      mfd_length atlas (g:B->real^3^3) gamma a t`; `a:real`; `b:real`]
                P2AZQ_RIND) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; REAL_SUB_REFL; REAL_ABS_0;
                  REAL_MUL_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `p:real^3->B`; `c:real`; `gamma:real->B`;
                     `a:real`; `b:real`; `x:real`] P2AZQ_LOCAL_LIP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2AZQ_COMBINE_ARITH THEN
      MAP_EVERY EXISTS_TAC [`p2azq_height (p:real^3->B) ((gamma:real->B) x)`;
                            `mfd_length atlas (g:B->real^3^3) (gamma:real->B) a x`;
                            `mfd_length atlas (g:B->real^3^3) (gamma:real->B) x y`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        USE_THEN "loc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `gamma:real->B`; `a:real`; `x:real`; `y:real`]
                      MFD_LENGTH_COMBINE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
          MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          SIMP_TAC[]]];
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `p:real^3->B`; `c:real`; `gamma:real->B`;
                     `a:real`; `b:real`; `x:real`] P2AZQ_LOCAL_LIP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
      ABBREV_TAC `y = max a (x - d / &2)` THEN
      SUBGOAL_THEN `a <= y /\ y < x /\ x - d < y` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "y" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2AZQ_COMBINE_ARITH THEN
      MAP_EVERY EXISTS_TAC [`p2azq_height (p:real^3->B) ((gamma:real->B) y)`;
                            `mfd_length atlas (g:B->real^3^3) (gamma:real->B) a y`;
                            `mfd_length atlas (g:B->real^3^3) (gamma:real->B) y x`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "loc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `gamma:real->B`; `a:real`; `y:real`; `x:real`]
                      MFD_LENGTH_COMBINE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
          MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          SIMP_TAC[]]]];
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P2AZQ_DIST_LOWER = prove
 (`!top atlas (g:B->real^3^3) p c x1 x2.
     p2azq_model (top,atlas) g p c /\ mfd_joinable (top,atlas) x1 x2
     ==> sqrt c * abs(p2azq_height p x2 - p2azq_height p x1) <=
         mfd_dist (top,atlas) g x1 x2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `gamma:real->B`; `&0`; `&1`] P2AZQ_CURVE_LIP) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Every point is close to an image p y with norm y > 1 (a radial step from  *)
(* a lift of norm >= 1 inside a param ball, GRGD_DIST_SMALL_NBHD), so the    *)
(* distance bound for lifts of norm > 1 extends to all pairs of points:      *)
(* d(x1,x2) <= sqrt(c) (abs(H x1 - H x2) + sqrt 2 pi), and all points are    *)
(* joinable.                                                                 *)
(* ========================================================================= *)

let P2AZQ_SVAL_POS = prove
 (`!y:real^3. &1 < norm y ==> &0 < apx_sval y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_SIMP_TAC[LOG_POS_LT; SQRT_POS_LT; REAL_ARITH `&0 < &2`]);;

let P2AZQ_RADIAL_STEP = prove
 (`!y:real^3 r. &1 <= norm y /\ &0 < r ==> ?y'. &1 < norm y' /\ dist(y,y') < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t * norm(y:real^3) < r` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `r / (&2 * norm(y:real^3))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `r / (&2 * norm(y:real^3)) * norm y = r / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 + t) % y:real^3` THEN
  REWRITE_TAC[NORM_MUL; dist; VECTOR_ARITH `y - (&1 + t) % y:real^3 = --(t % y)`;
              NORM_NEG] THEN
  SUBGOAL_THEN `abs(&1 + t) = &1 + t /\ abs t = t` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`t:real`; `norm(y:real^3)`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2AZQ_NEAR_OUT = prove
 (`!top atlas (g:B->real^3^3) p c x e.
     p2azq_model (top,atlas) g p c /\ x IN topspace top /\ &0 < e
     ==> ?y. &1 < norm y /\ mfd_joinable (top,atlas) x (p y) /\
             mfd_dist (top,atlas) g x (p y) < e /\
             sqrt c * abs(apx_sval y - p2azq_height p x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `e:real`] GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Wn:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Wn")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `x:B`] P2AZQ_LIFT_GE1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o
    check (fun th -> p2azq_mentions "mfd_param" th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(y:real^3,r)`; `p:real^3->B`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {z:real^3 | z IN ball(y,r) /\ (p:real^3->B) z IN Wn}` MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`p:real^3->B`; `subtopology euclidean (ball(y:real^3,r))`;
                   `top:B topology`; `Wn:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`y:real^3`; `r':real`] P2AZQ_RADIAL_STEP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^3->B) y' IN Wn` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(y:real^3,r') SUBSET {z:real^3 | z IN ball(y,r) /\ (p:real^3->B) z IN Wn}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y':real^3`) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) x ((p:real^3->B) y') /\
                mfd_dist (top,atlas) (g:B->real^3^3) x (p y') < e` STRIP_ASSUME_TAC THENL
   [USE_THEN "Wn" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2azq_height (p:real^3->B) (p y') = apx_sval y'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p:real^3->B`; `c:real`; `y':real^3`] P2AZQ_HEIGHT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs x = x`) THEN
    MATCH_MP_TAC P2AZQ_SVAL_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y':real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `x:B`; `(p:real^3->B) y'`] P2AZQ_DIST_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AZQ_UP_ARITH = prove
 (`!s K h1 h2 u1 u2 da db dm d e.
     &0 <= s /\ d <= da + dm + db /\ da < e /\ db < e /\
     dm <= s * (abs(u1 - u2) + K) /\ s * abs(u1 - h1) < e /\ s * abs(u2 - h2) < e
     ==> d < s * (abs(h1 - h2) + K) + &4 * e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s * abs(u1 - u2) <= s * abs(u1 - h1) + s * abs(h1 - h2) + s * abs(u2 - h2)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `dm <= s * (abs(u1 - u2) + K)` THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let P2AZQ_DIST_UP = prove
 (`!top atlas (g:B->real^3^3) p c x1 x2.
     p2azq_model (top,atlas) g p c /\ x1 IN topspace top /\ x2 IN topspace top
     ==> mfd_joinable (top,atlas) x1 x2 /\
         mfd_dist (top,atlas) g x1 x2 <=
         sqrt c * (abs(p2azq_height p x1 - p2azq_height p x2) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> mfd_joinable (top,atlas) x1 x2 /\
            mfd_dist (top,atlas) (g:B->real^3^3) x1 x2 <
            sqrt c * (abs(p2azq_height (p:real^3->B) x1 - p2azq_height p x2) +
                      sqrt(&2) * pi) + &4 * e`
  (LABEL_TAC "approx") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p:real^3->B`; `c:real`; `x1:B`; `e:real`]
                  P2AZQ_NEAR_OUT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p:real^3->B`; `c:real`; `x2:B`; `e:real`]
                  P2AZQ_NEAR_OUT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p:real^3->B`; `c:real`; `y1:real^3`; `y2:real^3`]
                  P2AZQ_DIST_UP_STRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y2) (x2:B)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y1) (x2:B)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(p:real^3->B) y2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (x1:B) x2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(p:real^3->B) y1` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AZQ_UP_ARITH THEN
    MAP_EVERY EXISTS_TAC [`apx_sval y1`; `apx_sval y2`;
                          `mfd_dist (top,atlas) (g:B->real^3^3) x1 ((p:real^3->B) y1)`;
                          `mfd_dist (top,atlas) (g:B->real^3^3) x2 ((p:real^3->B) y2)`;
                          `mfd_dist (top,atlas) (g:B->real^3^3) ((p:real^3->B) y1) (p y2)`] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x1 ((p:real^3->B) y1) +
                mfd_dist (top,atlas) g (p y1) x2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((p:real^3->B) y1) (p y2) +
                mfd_dist (top,atlas) g (p y2) x2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `x2:B`; `(p:real^3->B) y2`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "approx" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "approx" (MP_TAC o SPEC
    `(mfd_dist (top,atlas) (g:B->real^3^3) x1 x2 -
      sqrt c * (abs(p2azq_height (p:real^3->B) x1 - p2azq_height p x2) +
                sqrt(&2) * pi)) / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* No line.  For a line l, with H the height, tt = sqrt(c) (H(l 0) + sqrt 2  *)
(* pi) + 1: d(l tt,l(-tt)) = 2 tt is at most sqrt(c) (abs(H(l tt) -          *)
(* H(l(-tt))) + sqrt 2 pi) (previous section), while H >= 0 and sqrt(c)      *)
(* abs(H(l(+-tt)) - H(l 0)) <= tt (Lipschitz bound); so tt <= sqrt(c) (H(l   *)
(* 0) + sqrt 2 pi), which is absurd.  The headline P2A985_ZQ_NO_LINE states  *)
(* the hypotheses as the conjuncts of the two-to-one alternative of          *)
(* p2b_cyl_model (pc_p2b_defs) for a flow g at time 0, so that this unit     *)
(* does not load pc_p2b_defs; its users (pc_p2a_l984, pc_p2b_a5l) apply it   *)
(* to that definition.                                                       *)
(* ========================================================================= *)

let P2AZQ_HEIGHT_POS = prove
 (`!top atlas (g:B->real^3^3) p c x.
     p2azq_model (top,atlas) g p c /\ x IN topspace top ==> &0 <= p2azq_height p x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `x:B`] P2AZQ_LIFT_GE1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[apx_sval] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; LOG_POS]);;

let P2AZQ_LINE_ARITH = prove
 (`!s K h0 h1 h2 tt d12.
     &0 < s /\ &0 <= h1 /\ &0 <= h2 /\
     s * abs(h1 - h0) <= tt /\ s * abs(h2 - h0) <= tt /\
     d12 = &2 * tt /\ d12 <= s * (abs(h1 - h2) + K)
     ==> tt <= s * (h0 + K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(h1 - h2) <= h0 + abs(h1 - h0) \/ abs(h1 - h2) <= h0 + abs(h2 - h0)`
  STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `s * (abs(h1 - h2) + K) <= s * ((h0 + abs(h1 - h0)) + K)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `s * (abs(h1 - h2) + K) <= s * ((h0 + abs(h2 - h0)) + K)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC]);;

let P2AZQ_NO_LINE = prove
 (`!top atlas (g:B->real^3^3) p c.
     p2azq_model (top,atlas) g p c
     ==> ~(?l. !s t. l s IN topspace top /\
                     mfd_dist (top,atlas) g (l s) (l t) = abs(t - s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real->B` (LABEL_TAC "line")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2azq_model] o
    check (fun th -> p2azq_mentions "p2azq_model" th)) THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. (l:real->B) s IN topspace top` ASSUME_TAC THENL
   [USE_THEN "line" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `tt = sqrt c * (p2azq_height (p:real^3->B) ((l:real->B) (&0)) +
                             sqrt(&2) * pi) + &1` THEN
  SUBGOAL_THEN `&0 < tt` ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AZQ_HEIGHT_POS THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) ((l:real->B) tt) (l(--tt)) = &2 * tt`
  ASSUME_TAC THENL
   [USE_THEN "line" (MP_TAC o CONJUNCT2 o SPECL [`tt:real`; `--tt:real`]) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) ((l:real->B) (&0)) (l tt) = tt /\
                mfd_dist (top,atlas) g (l(&0)) (l(--tt)) = tt` STRIP_ASSUME_TAC THENL
   [USE_THEN "line" (fun th -> REWRITE_TAC[CONJUNCT2(SPECL [`&0`; `tt:real`] th);
                                          CONJUNCT2(SPECL [`&0`; `--tt:real`] th)]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `(l:real->B) tt`; `(l:real->B) (--tt)`]
                P2AZQ_DIST_UP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `(l:real->B) (&0)`; `(l:real->B) tt`]
                P2AZQ_DIST_UP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `(l:real->B) (&0)`; `(l:real->B) (--tt)`]
                P2AZQ_DIST_UP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `(l:real->B) (&0)`; `(l:real->B) tt`]
                P2AZQ_DIST_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:real^3->B`; `c:real`; `(l:real->B) (&0)`; `(l:real->B) (--tt)`]
                P2AZQ_DIST_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= p2azq_height (p:real^3->B) ((l:real->B) tt) /\
                &0 <= p2azq_height p (l(--tt))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AZQ_HEIGHT_POS THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt c`; `sqrt(&2) * pi`;
                 `p2azq_height (p:real^3->B) ((l:real->B) (&0))`;
                 `p2azq_height (p:real^3->B) ((l:real->B) tt)`;
                 `p2azq_height (p:real^3->B) ((l:real->B) (--tt))`; `tt:real`;
                 `mfd_dist (top,atlas) (g:B->real^3^3) ((l:real->B) tt) (l(--tt))`]
                P2AZQ_LINE_ARITH) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Headline: the two-to-one (Z/2-quotient) alternative of p2b_cyl_model,    *)
(* with its conjuncts copied verbatim, contains no line at time 0.           *)

let P2A985_ZQ_NO_LINE = prove
 (`!top atlas (g:real->B->real^3^3) (p:real^3->B) lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g(&0)) /\ &0 < lam /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0)
          ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0)
            ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y)
     ==> ~(?l. !s t. l s IN topspace top /\
                     mfd_dist (top,atlas) (g(&0)) (l s) (l t) = abs(t - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AZQ_NO_LINE THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->B`; `lam:real`] THEN
  REWRITE_TAC[p2azq_model] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o
    check (fun th -> p2azq_mentions "rfs_pullback" th)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO]);;

