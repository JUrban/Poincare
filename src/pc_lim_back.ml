(* ========================================================================= *)
(* L6 of the limit-geometry layer (the statement                             *)
(* LIM_FLOW_COMPLETE_BACK_STATEMENT of pc_lim_stmts), a fact about a single  *)
(* flow.                                                                     *)
(*   LIM_FLOW_COMPLETE_BACK |- !w. LIM_FLOW_COMPLETE_BACK_STATEMENT w: a    *)
(*     Ricci flow up to b with sec >= 0 and complete g(b) has complete      *)
(*     slices g(s), a < s <= b.                                              *)
(* Route: sec >= 0 gives Ric >= 0 (CMPZ_MFD_RICCI_SEC_LOWER), so g(s) >=    *)
(* g(b) (P4_RF_PREFERRED_DERIV, the mean value theorem, and continuity at  *)
(* b from the smooth extension of rfs_flow_upto); then cball_s SUBSET       *)
(* cball_b (RFAH_DIST_COMPARE), closed in a compact set.                    *)
(* ========================================================================= *)

needs "src/pc_lim_stmts.ml";;
needs "src/pc_p4_width.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p3_s14ftr.ml";;
needs "src/pc_rfa_hbar.ml";;
needs "src/pc_lrg_evol.ml";;

prioritize_real();;
type_invention_error := true;;
(* Along a flow up to b, the quadratic form of g t x is continuous on      *)
(* [s,b] (the smooth extension past b of rfs_flow_upto).                     *)

let LIM_UPTO_QF_CONT = prove
 (`!top atlas (g:real->A->real^3^3) a b x (v:real^3) s.
     rfs_flow_upto (top,atlas) a b g /\ x IN topspace top /\ a < s /\ s <= b
     ==> (\t. v dot (g t x ** v)) real_continuous_on real_interval[s,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `p = SND(c:(A->bool)#(A->real^3)) x` THEN
  SUBGOAL_THEN `(p:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) continuous_on
                 (interval(lift a,lift(b + e)) PCROSS
                                  IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_map_on (interval(lift a,lift(b + e)) PCROSS
                                IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                  (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)` THEN
    REWRITE_TAC[smooth_map_on] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[continuously_differentiable];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `(\m:real^(3,3)finite_prod. lift(v dot ((matrify m:real^3^3) ** v))) o Fx o
              (\w:real^1. pastecart w (p:real^3))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop w`; `p:real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIFY_VECTORIZE] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) (drop w)`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                      LIFT_DROP] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT]]);;
(* Backward monotonicity of the metric under Ricci flow with sec >= 0.     *)

let LIM_METRIC_BACK = prove
 (`!top atlas (g:real->A->real^3^3) a b s x (v:real^3).
     rfs_flow_upto (top,atlas) a b g /\
     (!t y u w. a < t /\ t <= b /\ y IN topspace top /\ ~collinear {vec 0,u,w}
                ==> &0 <= mfd_sectional atlas (g t) y u w) /\
     a < s /\ s <= b /\ x IN topspace top
     ==> v dot (g b x ** v) <= v dot (g s x ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = b:real` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                !t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (v:real^3) dot ((g:real->A->real^3^3) t x ** v)`;
                 `\t. (v:real^3) dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x)
                                       ** v)`;
                 `s:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_UPTO_QF_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC P4_RF_PREFERRED_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `t IN real_interval(s,b)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_ricci atlas ((g:real->A->real^3^3) t) x v v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `&0`; `v:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((--(&2) %% mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x) ** v) =
                --(&2) * mfd_ricci atlas (g t) x v v` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `v:real^3`; `v:real^3`] P3S_MFD_RICCI_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_ricci atlas ((g:real->A->real^3^3) t) x v v * (b - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `b - s`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ricci_matrix")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* L6: completeness of all slices of a flow with sec >= 0 before a complete *)
(* final slice.                                                              *)

let LIM_FLOW_COMPLETE_BACK = prove
 (`!w:B->bool. LIM_FLOW_COMPLETE_BACK_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[LIM_FLOW_COMPLETE_BACK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
    ASM_CASES_TAC `s = b:real` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`x0:B`; `r:real`] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) b) x0 r` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) b)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) s) x0 z` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `(g:real->B->real^3^3) b`; `&1`; `x0:B`; `z:B`]
                  RFAH_DIST_COMPARE) THEN
    ASM_REWRITE_TAC[REAL_LT_01; SQRT_1; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_METRIC_BACK THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]]);;

