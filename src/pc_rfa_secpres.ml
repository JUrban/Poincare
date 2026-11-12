(* ========================================================================= *)
(* Unit pc_rfa_secpres: the statements P2C_REQ_SEC_PRESERVED (A13 of         *)
(* pc_p2c_iface) and P2_THM_4_23 (pc_p3_iface): on a closed 3-manifold,      *)
(* sec >= 0 and, on a connected component, sec > 0 are preserved by the      *)
(* Ricci flow.                                                               *)
(* ========================================================================= *)

needs "src/pc_rfa_tmaxp.ml";;
needs "src/pc_mfd_diff.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* lambda versus the sectional curvatures at a point, and the                *)
(* headline theorems RFA_P2C_REQ_SEC_PRESERVED and RFA_P2_THM_4_23.          *)
(* ========================================================================= *)

(* lambda = mfd_sec_min versus the sectional curvatures at a point (3D).   *)

let RFA_SEC_GE_SECMIN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> mfd_sec_min atlas g x <= mfd_sectional atlas g x u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `x:A`] RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let RFA_SECMIN_NONNEG = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x.
     2 <= dimindex(:N) /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  MATCH_MP_TAC REAL_LE_INF THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g x (basis 1) (basis 2)`;
    `basis 1:real^N`; `basis 2:real^N`] THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:real` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. v$2`) THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= 2 /\ 2 <= dimindex(:N) /\ 1 <= dimindex(:N)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC]);;

let RFA_SECMIN_POS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g x u v)
     ==> &0 < mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c (g:A->real^3^3)) /\
    SND c x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:(A->bool)#(A->real^3)`; `x:A`]
         RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `transp(S:real^3^3) ** basis 1`]
         RFA_PCURV_AS_SEC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP (SPECL [`u:real^3`; `v:real^3`] (ASSUME
    `!u v. ~collinear {vec 0,u,v}
           ==> &0 < mfd_sectional (atlas:((A->bool)#(A->real^3))->bool)
                                  (g:A->real^3^3) x u v`))
    (ASSUME `~collinear {vec 0:real^3,u,v}`)) THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[]);;

(* The statement P2C_REQ_SEC_PRESERVED (A13): on a closed 3-manifold,       *)
(* sec >= 0 is preserved by the Ricci flow.                                 *)

let RFA_FLOW_FROM_METRICS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
     ricci_flow_from (top,atlas) a b g
     ==> ricci_flow_on (top,atlas) a b g /\ smooth_manifold_atlas top atlas /\ a < b /\
         (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^N^N)` THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = a` THENL
   [ASM_MESON_TAC[ricci_flow_from];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_P2C_REQ_SEC_PRESERVED = prove
 (`!u:A->bool. P2C_REQ_SEC_PRESERVED_STATEMENT u`,
  REWRITE_TAC[P2C_REQ_SEC_PRESERVED_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`; `&0`]
         RFA_SECMIN_LOWER_PRESERVED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; GSYM compact_space; REAL_LE_REFL] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[]]);;

(* P2_THM_4_23 (MT Thm 4.23 as stated in Part 3): positive sectional       *)
(* curvature on a component of a closed 3-manifold is preserved.             *)

let RFA_P2_THM_4_23 = prove
 (`!u:A->bool. P2_THM_4_23_STATEMENT u`,
  REWRITE_TAC[P2_THM_4_23_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ compact_in top U /\ ~(U = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
      ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top (U:A->bool),euclideanreal)
      (\x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) a) x)`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`subtopology euclideanreal {t | a <= t /\ t < b}`;
       `subtopology (top:A topology) U`;
       `\t x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                ((g:real->A->real^3^3) t) (x:A)`;
       `a:real`] RFA_SLICE_CONTINUOUS)) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_CMAP_RESTRICT_TU THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[ricci_flow_from]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (top:A topology) U`;
                 `\x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                        ((g:real->A->real^3^3) a) (x:A)`;
                 `U:A->bool`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `xm:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) a) xm`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_SECMIN_POS THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `U:A->bool`;
                 `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                    ((g:real->A->real^3^3) a) xm`]
         RFA_SECMIN_LOWER_PRESERVED) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                ((g:real->A->real^3^3) t) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                  ((g:real->A->real^3^3) a) xm` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

