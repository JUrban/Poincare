(* ========================================================================= *)
(* Unit pc_rfa_slmfd: transfer of the local Shi estimate to manifolds.  The  *)
(* exp pullback of a Ricci flow g(t) by the exp map of g(sg) at p (in the    *)
(* coordinates of a frame E), rfa_expflow: its chart form, its smoothness    *)
(* and the local Ricci flow equation on the tangent ball, and the invariance *)
(* of |nabla^m Rm|^2.                                                        *)
(* ========================================================================= *)

needs "src/pc_rfa_slloc.ml";;
needs "src/pc_cmp_hess.ml";;

prioritize_real();;
type_invention_error := true;;

(* G(t)(w) = (d exp)^T g(t)(exp(E w)) (d exp), exp and its differential      *)
(* those of g(sg) at p; at t = sg this is cmp_expmetric.                     *)

let rfa_expflow = new_definition
 `rfa_expflow (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
              (g:real->A->real^N^N) (sg:real) (p:A) (E:real^N^N) (t:real) (w:real^N) =
    transp(cmp_dexp (top,atlas) (g sg) p E w) **
    g t (mfd_exp (top,atlas) (g sg) p (E ** w)) **
    cmp_dexp (top,atlas) (g sg) p E w`;;

(* ========================================================================= *)
(* The exp pullback flow as a bilinear form and in charts.                   *)
(* ========================================================================= *)

let RFA_EXPFLOW_SG = prove
 (`!top atlas (g:real->A->real^N^N) sg (p:A) (E:real^N^N).
     rfa_expflow (top,atlas) g sg p E sg = cmp_expmetric (top,atlas) (g sg) p E`,
  REWRITE_TAC[FUN_EQ_THM; rfa_expflow; cmp_expmetric]);;

let RFA_EXPFLOW_DOT = prove
 (`!top atlas (g:real->A->real^N^N) sg (p:A) (E:real^N^N) t w a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas (g sg) /\ p IN topspace top /\
     E ** w IN mfd_exp_dom (top,atlas) (g sg) p
     ==> a dot (rfa_expflow (top,atlas) g sg p E t w ** b) =
         mfd_differential (open_set_atlas (:real^N)) atlas
           (mfd_exp (top,atlas) (g sg) p) (E ** w) (E ** a) dot
         (g t (mfd_exp (top,atlas) (g sg) p (E ** w)) **
          mfd_differential (open_set_atlas (:real^N)) atlas
            (mfd_exp (top,atlas) (g sg) p) (E ** w) (E ** b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_expflow] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; CMPP_DOT_TRANSP] THEN
  ASM_SIMP_TAC[CMPP_DEXP_APPLY]);;

let RFA_EXPFLOW_LOCAL = prove
 (`!top atlas (g:real->A->real^N^N) sg (p:A) (E:real^N^N) t
    (c:(A->bool)#(A->real^N)) w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas (g sg) /\ p IN topspace top /\ c IN atlas /\
     E ** w IN mfd_exp_dom (top,atlas) (g sg) p /\
     mfd_exp (top,atlas) (g sg) p (E ** w) IN FST c
     ==> rfa_expflow (top,atlas) g sg p E t w =
         mpullback (\w. SND c (mfd_exp (top,atlas) (g sg) p (E ** w)))
                   (metric_local atlas c (g t)) w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_SIMP_TAC[RFA_EXPFLOW_DOT] THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p)
                    ((E:real^N^N) ** w)` THEN
  ABBREV_TAC `q = mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w)` THEN
  SUBGOAL_THEN
   `((\w. SND (c:(A->bool)#(A->real^N))
            (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w)))
     has_derivative
     (\h. chart_jac (chart_at atlas (q:A)) c q ((D:real^N->real^N) (E ** h)))) (at w)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. SND (c:(A->bool)#(A->real^N))
              (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w))) =
      (\y. SND c (mfd_exp (top,atlas) (g sg) p y)) o (\w. E ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. chart_jac (chart_at atlas (q:A)) (c:(A->bool)#(A->real^N)) q
             ((D:real^N->real^N) ((E:real^N^N) ** h))) =
      (\h. chart_jac (chart_at atlas q) c q (D h)) o (\h. E ** h)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      MAP_EVERY EXPAND_TAC ["q"; "D"] THEN MATCH_MP_TAC CMPP_EXP_CHART_DERIV THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `c:(A->bool)#(A->real^N)`; `q:A`;
                 `(D:real^N->real^N) ((E:real^N^N) ** a)`;
                 `(D:real^N->real^N) ((E:real^N^N) ** b)`] GEOC_BILIN_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* lricci_flow is local: it transfers to equal families, to                  *)
(* open subsets, and glues over open covers.                                 *)
(* ========================================================================= *)

let RFA_LRICCI_FLOW_EQ = prove
 (`!U a b (G:real->real^N->real^N^N) G'.
     lricci_flow U a b G /\ (!t y. a < t /\ t < b /\ y IN U ==> G' t y = G t y)
     ==> lricci_flow U a b G'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `(G:real->real^N->real^N^N) t` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `lricci ((G':real->real^N->real^N^N) t) y (basis i) (basis j) =
      lricci (G t) y (basis i) (basis j)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s. (G:real->real^N->real^N^N) s y$i$j`;
                          `min (t - a) (b - t)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(G':real->real^N->real^N^N) s y = G s y`
      (fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let RFA_LRICCI_FLOW_SUBSET = prove
 (`!U V a b (G:real->real^N->real^N^N).
     lricci_flow U a b G /\ open V /\ V SUBSET U ==> lricci_flow V a b G`,
  REWRITE_TAC[lricci_flow] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[METRIC_FIELD_SUBSET];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ASM_MESON_TAC[SUBSET]]);;

let RFA_LRICCI_FLOW_UNION = prove
 (`!U a b (G:real->real^N->real^N^N).
     open U /\ a < b /\
     (!y. y IN U ==> ?V. open V /\ y IN V /\ V SUBSET U /\ lricci_flow V a b G)
     ==> lricci_flow U a b G`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "loc"))) THEN
  REWRITE_TAC[lricci_flow] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN U`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN U`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (V:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN
    UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN U`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The frame is invertible, linear diffeomorphisms, and d exp                *)
(* is injective on the tangent ball where the exp pullback is a metric       *)
(* field (so that CMPH_EXP_FRAME_DIFFEO of pc_cmp_hess applies).             *)
(* ========================================================================= *)

let RFA_FRAME_INVERTIBLE = prove
 (`!(g:A->real^N^N) x (E:real^N^N). mfd_orthonormal_frame g x E ==> invertible E`,
  REWRITE_TAC[mfd_orthonormal_frame] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) x` THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

let RFA_LINEAR_DIFFEO = prove
 (`!(E:real^N^N) S.
     invertible E /\ open S
     ==> diffeomorphism_on {w | E ** w IN S} S (\w. E ** w)
                           (\v. matrix_inv E ** v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN `open {w | (E:real^N^N) ** w IN S}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
    EQ_TAC THENL [MESON_TAC[]; DISCH_TAC] THEN
    EXISTS_TAC `matrix_inv(E:real^N^N) ** v` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
      DISCH_TAC THEN EXISTS_TAC `(E:real^N^N) ** w` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]];
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    MP_TAC(ISPECL [`{w | (E:real^N^N) ** w IN S}`; `\x:real^N. x`;
                   `\w. (E:real^N^N) ** w`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR];
    MP_TAC(ISPECL [`S:real^N->bool`; `\x:real^N. x`;
                   `\v. matrix_inv(E:real^N^N) ** v`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR]]);;

let RFA_EXPFLOW_DEXP_INJ = prove
 (`!top atlas (gs:A->real^N^N) (p:A) (E:real^N^N) rho w0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas gs /\ p IN topspace top /\ invertible E /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) gs p E) /\
     norm w0 < rho /\ E ** w0 IN mfd_exp_dom (top,atlas) gs p
     ==> !h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) gs p) (E ** w0) h = vec 0 ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  ABBREV_TAC `k = matrix_inv(E:real^N^N) ** h` THEN
  SUBGOAL_THEN `h = (E:real^N^N) ** k` SUBST_ALL_TAC THENL
   [EXPAND_TAC "k" THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `k:real^N = vec 0` (fun th -> REWRITE_TAC[th; MATRIX_VECTOR_MUL_RZERO]) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 < k dot (cmp_expmetric (top,atlas) (gs:A->real^N^N) p E w0 ** k)`
  MP_TAC THENL
   [UNDISCH_TAC `metric_field (ball(vec 0,rho))
                   (cmp_expmetric (top,atlas) (gs:A->real^N^N) p E)` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `w0:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMPP_EXPMETRIC_DOT] THEN
  REWRITE_TAC[DOT_LZERO; REAL_LT_REFL]);;

(* ========================================================================= *)
(* The exp pullback of a Ricci flow is a local Ricci flow on                 *)
(* the tangent ball, and |nabla^m Rm|^2 is preserved.                        *)
(* ========================================================================= *)

let RFA_EXPFLOW_LRICCI = prove
 (`!top atlas (g:real->A->real^N^N) a b sg (p:A) (E:real^N^N) rho.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < sg /\ sg < b /\
     p IN topspace top /\ mfd_orthonormal_frame (g sg) p E /\
     mfd_tball (g sg) p rho SUBSET mfd_exp_dom (top,atlas) (g sg) p /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g sg) p E)
     ==> lricci_flow (ball(vec 0,rho)) a b (rfa_expflow (top,atlas) g sg p E)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) sg)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_FRAME_INVERTIBLE]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_UNION THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  X_GEN_TAC `w0:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** w0 IN mfd_exp_dom (top,atlas) ((g:real->A->real^N^N) sg) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball ((g:real->A->real^N^N) sg) p rho SUBSET
                 mfd_exp_dom (top,atlas) (g sg) p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `p:A`; `E:real^N^N`; `w0:real^N`]
         CMPH_EXP_FRAME_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_DEXP_INJ THEN
    EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w0) IN
    topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w0)`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                             ((E:real^N^N) ** w0))` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `Tr:real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `Tr SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `W INTER ball(vec 0:real^N,rho)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; IN_BALL_0; INTER_SUBSET] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC
   `\t. mpullback (\w. SND(c:(A->bool)#(A->real^N))
                         (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                  ((E:real^N^N) ** w)))
                  (metric_local atlas c (g t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`Tr:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_LOCAL THEN
    ASM_SIMP_TAC[]]);;

let RFA_EXPFLOW_RMD = prove
 (`!top atlas (g:real->A->real^N^N) a b sg (p:A) (E:real^N^N) rho j t w.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < sg /\ sg < b /\
     a < t /\ t < b /\ p IN topspace top /\ mfd_orthonormal_frame (g sg) p E /\
     mfd_tball (g sg) p rho SUBSET mfd_exp_dom (top,atlas) (g sg) p /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g sg) p E) /\
     norm w < rho
     ==> lrm_deriv_norm2 j (rfa_expflow (top,atlas) g sg p E t) w =
         rfa_rmd2 j atlas (g t) (mfd_exp (top,atlas) (g sg) p (E ** w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) sg) /\
                riemannian_metric atlas (g t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_FRAME_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) ((g:real->A->real^N^N) sg) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball ((g:real->A->real^N^N) sg) p rho SUBSET
                 mfd_exp_dom (top,atlas) (g sg) p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `p:A`; `E:real^N^N`; `w:real^N`]
         CMPH_EXP_FRAME_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_DEXP_INJ THEN
    EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w) IN
    topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w)`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                             ((E:real^N^N) ** w))` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `Tr:real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `Tr SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lrm_deriv_norm2 j
      (mpullback (\w. SND(c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                 ((E:real^N^N) ** w)))
                 (metric_local atlas c (g t))) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_EXPFLOW_LOCAL THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `Tr:real^N->bool`; `W:real^N->bool`;
                 `\w. SND(c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                 ((E:real^N^N) ** w))`;
                 `h':real^N->real^N`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `w:real^N`] LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^N^N) t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_RMD2_CHART THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* First exit.  If g2 <= lam^2 g1 on an open set R containing                *)
(* the g2-ball of radius d about y, a curve from y of g1-length < d / lam    *)
(* stays in R; hence the g1-ball of radius d / lam lies in R and the         *)
(* distances compare.                                                        *)
(* ========================================================================= *)

let RFA_CURVE_STAYS = prove
 (`!top atlas (g1:A->real^N^N) g2 R y d lam (gamma:real->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\
     open_in top R /\ &0 < lam /\
     (!z. mfd_joinable (top,atlas) y z /\ mfd_dist (top,atlas) g2 y z < d ==> z IN R) /\
     (!z v. z IN R ==> v dot (g2 z ** v) <= lam pow 2 * (v dot (g1 z ** v))) /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y /\ y IN R /\
     lam * mfd_length atlas g1 gamma (&0) (&1) < d
     ==> (!s. &0 <= s /\ s <= &1 ==> gamma s IN R) /\
         mfd_length atlas g2 gamma (&0) (&1) <=
         lam * mfd_length atlas g1 gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ball") (CONJUNCTS_THEN2 (LABEL_TAC "cmp")
    STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `sqrt(lam pow 2) = lam` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> mfd_c1_curve (top,atlas) (gamma:real->A) (&0) s /\
            mfd_length atlas (g1:A->real^N^N) gamma (&0) s <=
            mfd_length atlas g1 gamma (&0) (&1)`
  (LABEL_TAC "sub") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `gamma:real->A`; `&0`; `s:real`; `&1`]
           MFD_LENGTH_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `gamma:real->A`; `s:real`; `&1`]
           MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= &1 ==> (gamma:real->A) s IN R` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `R:A->bool`] GRGD_FIRST_TIME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[mfd_c1_curve];
        EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                   `mfd_cball (top,atlas) (g2:A->real^N^N) y
                      (lam * mfd_length atlas g1 (gamma:real->A) (&0) (&1))`;
                   `t1:real`] GRGD_CLOSED_LEFT_CURVE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "sub" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_C1_CURVE_JOINABLE) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_length atlas (g2:A->real^N^N) (gamma:real->A) (&0) s` THEN
      CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `(gamma:real->A)(&0) = y`)) THEN
        MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * mfd_length atlas (g1:A->real^N^N) (gamma:real->A) (&0) s` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g1:A->real^N^N`; `g2:A->real^N^N`; `lam pow 2`;
                       `gamma:real->A`; `&0`; `s:real`] MFD_LENGTH_METRIC_COMPARE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MAP_EVERY X_GEN_TAC [`u:real`; `v:real^N`] THEN STRIP_TAC THEN
        USE_THEN "cmp" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN R)` THEN REWRITE_TAC[] THEN
    USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g1:A->real^N^N`; `g2:A->real^N^N`; `lam pow 2`;
                 `gamma:real->A`; `&0`; `&1`] MFD_LENGTH_METRIC_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real^N`] THEN STRIP_TAC THEN
  USE_THEN "cmp" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let RFA_DIST_APPROX = prove
 (`!top atlas (g:A->real^N^N) y z e.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) y z /\ &0 < e
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = y /\ gamma(&1) = z /\
                 mfd_length atlas g gamma (&0) (&1) < mfd_dist (top,atlas) g y z + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (y:A) /\ gamma(&1) = z}`;
                 `mfd_dist (top,atlas) (g:A->real^N^N) y z + e`] INF_APPROACH) THEN
  REWRITE_TAC[GSYM mfd_dist] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_ADDR] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (y:A) z` THEN
      REWRITE_TAC[mfd_joinable] THEN MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[]]);;

let RFA_LE_EPS = prove
 (`!x y c. &0 < c /\ (!u. &0 < u /\ u < c ==> x <= y + u) ==> x <= y`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (c / &2) ((x - y) / &2)`) THEN
  ASM_REAL_ARITH_TAC);;

let RFA_BALL_INCLUSION = prove
 (`!top atlas (g1:A->real^N^N) g2 R y d lam.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\
     open_in top R /\ y IN R /\ &0 < lam /\
     (!z. mfd_joinable (top,atlas) y z /\ mfd_dist (top,atlas) g2 y z < d ==> z IN R) /\
     (!z v. z IN R ==> v dot (g2 z ** v) <= lam pow 2 * (v dot (g1 z ** v)))
     ==> !z. mfd_joinable (top,atlas) y z /\ mfd_dist (top,atlas) g1 y z < d / lam
             ==> z IN R /\
                 mfd_dist (top,atlas) g2 y z <= lam * mfd_dist (top,atlas) g1 y z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g1:A->real^N^N) y z < d / lam` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u. &0 < u /\ u < d - mfd_dist (top,atlas) (g1:A->real^N^N) y z * lam
        ==> (z:A) IN R /\
            mfd_dist (top,atlas) g2 y z <= lam * mfd_dist (top,atlas) g1 y z + u`
  (LABEL_TAC "approx") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `y:A`; `z:A`; `u / lam`] RFA_DIST_APPROX) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `lam * mfd_length atlas (g1:A->real^N^N) (gam:real->A) (&0) (&1) <
      lam * mfd_dist (top,atlas) g1 y z + u`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `lam * (mfd_dist (top,atlas) (g1:A->real^N^N) y z + u / lam)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
        ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `g2:A->real^N^N`; `R:A->bool`; `y:A`; `d:real`;
                   `lam:real`; `gam:real->A`] RFA_CURVE_STAYS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(gam:real->A)(&1) = z`)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g2:A->real^N^N) (gam:real->A) (&0) (&1)` THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(gam:real->A)(&1) = z`)) THEN
      SUBST1_TAC(SYM(ASSUME `(gam:real->A)(&0) = y`)) THEN
      MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d - mfd_dist (top,atlas) (g1:A->real^N^N) y z * lam` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "approx" (MP_TAC o SPEC
      `(d - mfd_dist (top,atlas) (g1:A->real^N^N) y z * lam) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MATCH_MP_TAC RFA_LE_EPS THEN
    EXISTS_TAC `d - mfd_dist (top,atlas) (g1:A->real^N^N) y z * lam` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "approx" (MP_TAC o SPEC `u:real`) THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Orthonormal frames exist; for a Ricci flow on (a,b] smooth                *)
(* up to b (chart extensions past b), the metrics at sg and at b compare    *)
(* pointwise under a Ricci bound on [sg,b).                                 *)
(* ========================================================================= *)

let RFA_FRAME_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) g x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top
     ==> ?E:real^N^N. mfd_orthonormal_frame g x E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                               (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`] LRG_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:A->real^N^N) x = transp M ** (M:real^N^N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(M:real^N^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  ASM_REWRITE_TAC[mfd_orthonormal_frame] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID; GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID]);;

let RFA_UPTO_QFORM_EQUIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) z sg Kr v.
     ricci_flow_on (top,atlas) a b g /\
     (!c. c IN atlas
          ==> ?e Fx. &0 < e /\
                     smooth_map_on
                       (interval(lift a,lift(b + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
                     !t y. a < t /\ t <= b /\ y IN IMAGE (SND c) (FST c)
                           ==> Fx(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y)) /\
     z IN topspace top /\ a < sg /\ sg <= b /\ &0 <= Kr /\
     (!s. sg < s /\ s < b
          ==> abs(mfd_ricci atlas (g s) z v v) <= Kr * (v dot (g s z ** v)))
     ==> exp(--(&2 * Kr * (b - sg))) * (v dot (g sg z ** v)) <= v dot (g b z ** v) /\
         v dot (g b z ** v) <= exp(&2 * Kr * (b - sg)) * (v dot (g sg z ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric"))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  ASM_CASES_TAC `sg:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                    REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ext" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A) IN atlas`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `y0 = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z` THEN
  SUBGOAL_THEN `y0 IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                             (FST(chart_at atlas z))` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. v dot ((g:real->A->real^N^N) s z ** v)`;
                 `\s. --(&2) * mfd_ricci atlas ((g:real->A->real^N^N) s) (z:A) v v`;
                 `&2 * Kr`; `sg:real`; `b:real`] RFA_GRONWALL_2SIDED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC
       `\r. drop((\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v)))
                 ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (pastecart (lift r) y0)))` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        REWRITE_TAC[LIFT_DROP] THEN
        SUBGOAL_THEN
         `(FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift r) y0) =
          vectorize(metric_local atlas (chart_at atlas (z:A))
                                 ((g:real->A->real^N^N) r) y0)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[MATRIFY_VECTORIZE] THEN EXPAND_TAC "y0" THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(g:real->A->real^N^N) r`; `z:A`] METRIC_LOCAL_AT) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MP_TAC(ISPECL
         [`interval(lift a,lift(b + e)) PCROSS
           IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                 (FST(chart_at atlas z))`;
          `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
          `\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v))`;
          `y0:real^N`; `r:real`] RFA_TSLICE_CONTINUOUS) THEN
        REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS;
                       IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[]]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "ric" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* exp is defined on the tangent ball of radius rho when the                 *)
(* metric ball of radius rho lies in a compact set (maximal geodesics leave  *)
(* compact sets, MFD_GEO_ESCAPE).                                            *)
(* ========================================================================= *)

let RFA_EXP_DOM_COMPACT = prove
 (`!top atlas (g:A->real^N^N) y Kc rho.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ y IN topspace top /\ compact_in top Kc /\
     (!z. mfd_joinable (top,atlas) y z /\ mfd_dist (top,atlas) g y z < rho
          ==> z IN Kc)
     ==> mfd_tball g y rho SUBSET mfd_exp_dom (top,atlas) g y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inK")))))) THEN
  REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[is_realinterval] THEN STRIP_TAC THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) y v` THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s IN M
        ==> s % v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) y /\
            mfd_exp (top,atlas) g y (s % v) = mfd_geo (top,atlas) g y v s`
  (LABEL_TAC "resc") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `v:real^N`; `s:real`] MFD_GEO_RESCALE) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[mfd_exp_dom; mfd_exp; IN_ELIM_THM; REAL_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t IN M ==> t < &1` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 IN M` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 3)) THEN
      MAP_EVERY EXISTS_TAC [`&0`; `t:real`] THEN ASM_REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `v:real^N`; `Kc:A->bool`; `&1`]
         MFD_GEO_ESCAPE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "esc"))) THEN
  ABBREV_TAC `ts = max t1 (&0)` THEN
  SUBGOAL_THEN `ts IN M /\ &0 <= ts /\ t1 <= ts` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "esc" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(ts:real) IN M`) (ASSUME `t1 <= ts`)))) THEN
  USE_THEN "resc" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `&0 <= ts`) (ASSUME `(ts:real) IN M`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[] THEN
  USE_THEN "inK" MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `ts % v:real^N`] CMPH_EXP_DIST_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_tnorm (g:A->real^N^N) y (ts % v)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs ts * mfd_tnorm (g:A->real^N^N) y v <= mfd_tnorm g y v`
  MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ts < &1` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The normal-coordinate setup at (y, g1) inside a region R                  *)
(* where g2 <= lam^2 g1 and |sec(g1)| <= K, R inside a compact set: exp of   *)
(* g1 is defined on the tangent ball of radius rho <= d / lam, maps it into  *)
(* R, and the pullback satisfies rfa_expc (from CMP_EXP_PULLBACK).          *)
(* ========================================================================= *)

let RFA_MFD_EXPSETUP = prove
 (`!top atlas (g1:A->real^N^N) g2 R Kc y d lam K rho E.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\
     open_in top R /\ R SUBSET Kc /\ compact_in top Kc /\ y IN R /\ &0 < lam /\
     (!z. mfd_joinable (top,atlas) y z /\ mfd_dist (top,atlas) g2 y z < d ==> z IN R) /\
     (!z v. z IN R ==> v dot (g2 z ** v) <= lam pow 2 * (v dot (g1 z ** v))) /\
     (!z. z IN R ==> mfd_rm_norm atlas g1 z <= K) /\
     &0 <= K /\ &0 < rho /\ rho <= d / lam /\ K * rho pow 2 <= &1 /\
     mfd_orthonormal_frame g1 y E
     ==> mfd_tball g1 y rho SUBSET mfd_exp_dom (top,atlas) g1 y /\
         (!w. norm w < rho ==> mfd_exp (top,atlas) g1 y (E ** w) IN R) /\
         metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) g1 y E) /\
         rfa_expc (cmp_expmetric (top,atlas) g1 y E) rho K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. mfd_joinable (top,atlas) (y:A) z /\
        mfd_dist (top,atlas) (g1:A->real^N^N) y z < rho ==> z IN R`
  (LABEL_TAC "ball") THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `g2:A->real^N^N`; `R:A->bool`; `y:A`; `d:real`;
                   `lam:real`] RFA_BALL_INCLUSION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g1:A->real^N^N) y rho SUBSET mfd_exp_dom (top,atlas) g1 y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_EXP_DOM_COMPACT THEN EXISTS_TAC `Kc:A->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `(R:A->bool) SUBSET Kc` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w. norm w < rho ==> mfd_exp (top,atlas) (g1:A->real^N^N) y ((E:real^N^N) ** w) IN R`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g1:A->real^N^N) y`
    ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_tball (g1:A->real^N^N) y rho SUBSET
                   mfd_exp_dom (top,atlas) g1 y` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `y:A`; `(E:real^N^N) ** w`] CMPH_EXP_DIST_LE) THEN
    ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN STRIP_TAC THEN
    USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:A)`; `(:N)`] CMP_EXP_PULLBACK) THEN
  REWRITE_TAC[CMP_EXP_PULLBACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g1:A->real^N^N`; `y:A`; `E:real^N^N`; `K:real`;
                             `rho:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[rfa_expc]);;

