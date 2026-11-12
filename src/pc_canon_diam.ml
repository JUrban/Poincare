(* ========================================================================= *)
(* Unit pc_canon_diam: (C,eps)-canonical neighbourhoods lie in balls of      *)
(* radius D R(x)^(-1/2) about their centre (or, for caps and components,     *)
(* about any point of the core resp. component):                             *)
(* - necks: sqrt(1 + eps) (1/eps + sqrt 2 pi) (APX_NECK_DIST_UPPER);         *)
(* - caps: C (the intrinsic diameter bound of rfs_cap);                       *)
(* - C-components: C sqrt C (sec > sup R / C gives inf R >= R(x) / C);        *)
(* - eps-round components: 12 (Myers for the constant-curvature metric g1 on *)
(*   the compact component, CMP_MYERS_DIAMETER_RIC, the C^0 comparison of    *)
(*   q g with g1, and R(x) <= 7 q from scalar stability).                     *)
(* CANON_NBHD_IN_BALL combines the four cases; CANON_NBHD_OPEN: canonical    *)
(* neighbourhoods are open.  Used for MT Claim 11.6 (pc_p2c_blowup) and      *)
(* Claim 11.35.                                                              *)
(* ========================================================================= *)

needs "src/pc_p2b_slice.ml";;
needs "src/pc_cmp_myers.ml";;
needs "src/pc_p2c_lrestrict.ml";;
needs "src/pc_rfa_hbar.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_rfa_sec.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2b_ltr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Openness, the four cases and the combined bound.                          *)
(* ========================================================================= *)

(* Canonical neighbourhoods are open.                                       *)

let CANON_NBHD_OPEN = prove
 (`!top atlas (g:A->real^3^3) C eps x U.
     rfs_canonical_nbhd (top,atlas) g C eps x U
     ==> smooth_manifold_atlas top atlas /\ open_in top U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_canonical_nbhd] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ASM_MESON_TAC[rfs_cap];
    SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                  U IN connected_components_of top` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_c_component]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                   APX_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                  U IN connected_components_of top` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_round_component]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                   APX_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[]]);;

(* Canonical neighbourhoods lie in balls of radius D R(x)^(-1/2) about      *)
(* their centre: the neck and cap cases.                                     *)

let CANON_NECK_IN_BALL = prove
 (`!top atlas (g:A->real^3^3) eps x e z.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
     z IN IMAGE e (rfs_neck_dom eps)
     ==> mfd_joinable (top,atlas) x z /\
         mfd_dist (top,atlas) g x z <=
         sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(e:real^3->A) y0`; `e:real^3->A`; `y0:real^3`; `y:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `apx_sval y0 = &0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&0 - apx_sval y) <= inv eps` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + eps) /\
                &0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y0)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c = a * c * b`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CANON_CAP_IN_BALL = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x z.
     riemannian_metric atlas g /\ rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\ z IN U
     ==> mfd_joinable (top,atlas) x z /\
         mfd_dist (top,atlas) g x z <= C * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap]) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U (x:A) z`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable_in" with _ -> false))
          (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_IMP]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_dist_in" with _ -> false))
        (concl th) && not (is_forall (concl th)))) THEN
  REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let has c = can (find_term (fun t -> try fst(dest_const t) = c with _ -> false))
                    (concl th) in
    has "rfs_sup_lt" && has "real_div" && not (has "rfs_scalar_grad2") &&
    not (has "rfs_scalar_lap") && not (has "mfd_dist_in"))) THEN
  REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dq"))) THEN
  SUBGOAL_THEN `!y. y IN U ==> &0 < mfd_scalar atlas (g:A->real^3^3) y` (LABEL_TAC "Rpos")
  THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x <= sup(IMAGE (mfd_scalar atlas g) U)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `dq * mfd_scalar atlas (g:A->real^3^3) x` THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "dq" (MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) y / mfd_scalar atlas g x`) THEN
      ANTS_TAC THENL [MAP_EVERY EXISTS_TAC [`y:A`; `x:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "Rpos" (MP_TAC o C MP (ASSUME `(x:A) IN U`) o SPEC `x:A`) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U x z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd:real` THEN CONJ_TAC THENL
   [USE_THEN "dd" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `z:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [USE_THEN "dq" (MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x`) THEN
    ANTS_TAC THENL [MAP_EVERY EXISTS_TAC [`x:A`; `x:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]]);;

(* The C-component case: sec >= d > sup R / C gives inf R >= 6 d >= R(x)/C *)
(* (P2BS_MFD_SCALAR_SECT), and the diameter is < C (inf R)^(-1/2).          *)

let CANON_CCOMP_IN_BALL = prove
 (`!top atlas (g:A->real^3^3) C U x z.
     riemannian_metric atlas g /\ rfs_c_component (top,atlas) g C U /\ &1 <= C /\
     x IN U /\ z IN U
     ==> mfd_joinable (top,atlas) x z /\
         mfd_dist (top,atlas) g x z <= C * sqrt C * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `U:A->bool`; `x:A`] P2B_C_COMPONENT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rpos") (CONJUNCTS_THEN2 (LABEL_TAC "Rbd")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_c_component]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "infgt")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "diam") (K ALL_TAC))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `x:A`; `z:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  (* distances on U x U are bounded *)
  SUBGOAL_THEN `?B. !p q. p IN U /\ q IN U ==> mfd_dist (top,atlas) (g:A->real^3^3) p q <= B`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `real_bounded (IMAGE (\(p,q). mfd_dist (top,atlas) (g:A->real^3^3) p q)
                                     ((U:A->bool) CROSS U))` MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `prod_topology (top:A topology) top` THEN
      ASM_SIMP_TAC[MFD_DIST_CONTINUOUS; COMPACT_IN_CROSS];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
      MESON_TAC[REAL_ARITH `abs z <= b ==> z <= b`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) x z <=
                sup {mfd_dist (top,atlas) g x y | x IN U /\ y IN U}` ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `z:A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* inf R >= R(x) / C *)
  USE_THEN "infgt" (MP_TAC o REWRITE_RULE[rfs_inf_gt; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dlow"))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x <= sup(IMAGE (mfd_scalar atlas g) U)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> &6 * d <= mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `d:real`] P2BS_MFD_SCALAR_SECT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "dlow" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv C * mfd_scalar atlas (g:A->real^3^3) x <=
                inf(IMAGE (mfd_scalar atlas g) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INF THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&6 * d` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv C * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv C * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C * mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(inf(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) <=
                sqrt C * inv(sqrt(mfd_scalar atlas g x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(sqrt(inv C * mfd_scalar atlas (g:A->real^3^3) x))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; SQRT_INV; REAL_INV_MUL;
                   REAL_INV_INV; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sup {mfd_dist (top,atlas) (g:A->real^3^3) x y | x IN U /\ y IN U}` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * inv(sqrt(inf(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)))` THEN
  CONJ_TAC THENL [USE_THEN "diam" (ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE); ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Quadratic-form comparisons pass to restricted metrics (the restricted    *)
(* preferred chart changes both by the same Jacobian).                       *)

let CDM_RESTRICT_QF_LE = prove
 (`!top atlas (W:A->bool) (G:A->real^N^N) G' c x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
     (!v. v dot (G x ** v) <= c * (v dot (G' x ** v)))
     ==> !v. v dot (restrict_metric atlas W G x ** v) <=
             c * (v dot (restrict_metric atlas W G' x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT1 th]) THEN
  X_GEN_TAC `v:real^N` THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[]);;

(* The C^0 part of the closeness of a round component: q g <= (1 + eps) g1. *)

let CDM_ROUND_QF = prove
 (`!top atlas (g:A->real^N^N) g1 q k eps U y v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g1 /\ &0 < q /\ &0 < eps /\
     rfs_mclose k eps atlas U g1 (\y. q %% g y) /\ y IN U /\ y IN topspace top
     ==> v dot (g y ** v) <= (&1 + eps) / q * (v dot (g1 y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_mclose k eps atlas U (g1:A->real^N^N) (\y. q %% (g:A->real^N^N) y)` THEN
  REWRITE_TAC[rfs_mclose] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `y:A`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)` THEN
  SUBGOAL_THEN `riemannian_metric atlas (\y. q %% (g:A->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (\y. q %% (g:A->real^N^N) y)`;
                 `SND (c:(A->bool)#(A->real^N)) y`; `v:real^N`] LCK_DIST_C0) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `riemannian_metric atlas (\y. q %% (g:A->real^N^N) y)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N) (SND c y) = g1 y /\
                metric_local atlas (c:(A->bool)#(A->real^N)) (\y. q %% (g:A->real^N^N) y)
                  (SND c y) = q %% g y`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "c" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                  METRIC_LOCAL_AT) THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                  (g1:A->real^N^N)) (metric_local atlas c (\y. q %% (g:A->real^N^N) y))
                  (SND c y)) <= eps` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot ((g1:A->real^N^N) y ** v)` ASSUME_TAC THENL
   [ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g1:A->real^N^N`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                  (g1:A->real^N^N)) (metric_local atlas c (\y. q %% (g:A->real^N^N) y))
                  (SND c y))` THEN
  ABBREV_TAC `a = v dot ((g:A->real^N^N) y ** v)` THEN
  ABBREV_TAC `b = v dot ((g1:A->real^N^N) y ** v)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `q * a <= (&1 + eps) * b` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b + s * b` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `b + s * b = (&1 + s) * b`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[real_div; REAL_ARITH `(x * inv q) * b = inv q * (x * b)`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

(* A component of a smooth manifold is the joinable class of each of its   *)
(* points.                                                                    *)

let CDM_COMPONENT_CLASS = prove
 (`!top atlas (U:A->bool) x.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     U IN connected_components_of top /\ x IN U
     ==> {y | mfd_joinable (top,atlas) x y} = U`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected_component_of top (x:A) SUBSET U` MP_TAC THENL
     [MATCH_MP_TAC(ISPEC `top:A topology` CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
      ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
      REWRITE_TAC[SET_RULE `!s t:A->bool. ~DISJOINT s t <=> ?z. z IN s /\ z IN t`] THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
      ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                   `x:A`; `y:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
    ASM_SIMP_TAC[]]);;

(* Scalar curvature at a point of a round component: R(x) is about 6 q.    *)

let CDM_ROUND_SCALAR = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) g1 q eps U x.
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       riemannian_metric atlas g1 /\ &0 < q /\ &0 < eps /\ eps <= eps0 /\
       (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 x u v = &1) /\
       rfs_mclose (rfs_kreg eps) eps atlas U g1 (\y. q %% g y) /\ x IN U /\
       x IN topspace top
       ==> &0 < mfd_scalar atlas g x /\ mfd_scalar atlas g x <= &7 * q`,
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cr"))) THEN
  SUBGOAL_THEN `&0 <= sqrt Cr` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  EXISTS_TAC `inv(&100 * (&1 + sqrt Cr))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &10 /\ &72 * (&1 + sqrt Cr) * eps <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(&100 * (&1 + sqrt Cr)) * eps <= &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&100 * (&1 + sqrt Cr)) * inv(&100 * (&1 + sqrt Cr))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt Cr * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (\y. q %% (g:A->real^3^3) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `q:real`; `x:A`] P2BCS_SCALAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `x:A`; `&1`] P2BS_MFD_SCALAR_SECT) THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg eps) eps atlas U (g1:A->real^3^3)
                 (\y. q %% (g:A->real^3^3) y)` THEN
  REWRITE_TAC[rfs_mclose] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_scalar; mfd_sectional]) THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))) (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g1:A->real^3^3)) /\
                metric_field (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))) (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (\y. q %% (g:A->real^3^3) y)) /\
                SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x IN IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `riemannian_metric atlas (\y. q %% (g:A->real^3^3) y)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g1:A->real^3^3))
                  (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (\y. q %% (g:A->real^3^3) y))
                  (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x)) <= eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg eps) (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g1:A->real^3^3))
                    (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (\y. q %% (g:A->real^3^3) y))
                    (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt Cr`; `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))`; `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g1:A->real^3^3)`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (\y. q %% (g:A->real^3^3) y)`;
                 `SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `c = c * &1 pow 2`] THEN
      USE_THEN "Cr" MATCH_MP_TAC THEN EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))` THEN
      ASM_SIMP_TAC[REAL_ABS_1; REAL_LE_REFL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&8 * &9 * (&1 + sqrt Cr)) *
                sqrt(lck_dist2 2 (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g1:A->real^3^3))
                       (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (\y. q %% (g:A->real^3^3) y))
                       (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x)) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&8 * &9 * (&1 + sqrt Cr)) * eps` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 <= mfd_scalar atlas (g:A->real^3^3) x / q /\
                mfd_scalar atlas g x / q <= &7` MP_TAC THENL
   [ASM_REWRITE_TAC[mfd_scalar] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* The round case: the constant-curvature metric g1 of a round component    *)
(* has diameter <= 4 on the component (Myers, CMP_MYERS_DIAMETER_RIC, on the *)
(* compact restricted manifold, Ric >= 2 g1).                                *)

let CANON_ROUND_G1_DIAM = prove
 (`!top atlas (g1:A->real^3^3) U x z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     U IN connected_components_of top /\ compact_in top U /\
     (!y u v. y IN U /\ ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 y u v = &1) /\
     x IN U /\ z IN U
     ==> mfd_joinable (subtopology top U,restrict_atlas atlas U) x z /\
         mfd_dist (subtopology top U,restrict_atlas atlas U) (restrict_metric atlas U g1) x z
         <= &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ (U:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                    APX_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `x:A`] CDM_COMPONENT_CLASS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `x:A`; `x:A`; `z:A`] P2CO_CLASS_DIST) THEN
  ASM_SIMP_TAC[MFD_JOINABLE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `x:A`; `z:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (subtopology top U,
                  restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U) (x:A) z`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top U)
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U) /\
                riemannian_metric (restrict_atlas atlas U) (restrict_metric atlas U g1) /\
                hausdorff_space (subtopology top (U:A->bool)) /\
                topspace (subtopology top U) = U`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; HAUSDORFF_SPACE_SUBTOPOLOGY;
                 TOPSPACE_SUBTOPOLOGY; SET_RULE `!s t:A->bool. s SUBSET t ==> t INTER s = s`] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                 `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) U g1`;
                 `&2`; `&1`; `x:A`; `z:A`] CMP_MYERS_DIAMETER_RIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < &2`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BL_COMPACT_COMPLETE THEN ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                   `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) U g1`;
                   `y:A`; `&1`; `w:real^3`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `g1:A->real^3^3`; `y:A`] MFDR_SECTIONAL_SET_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `mfd_sectional (restrict_atlas atlas U)
                                (restrict_metric atlas U (g1:A->real^3^3)) (y:A) u v`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `u':real^3`; `v':real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional" with _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* Round components lie in balls of radius 12 R(x)^(-1/2): diam_g1 <= 4,    *)
(* g <= ((1+eps)/q) g1 on U and R(x) <= 7 q.                                 *)

let CANON_ROUND_IN_BALL = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps U x z.
       hausdorff_space top /\ riemannian_metric atlas g /\
       rfs_round_component (top,atlas) g eps U /\ &0 < eps /\ eps <= eps0 /\
       x IN U /\ z IN U
       ==> mfd_joinable (top,atlas) x z /\
           mfd_dist (top,atlas) g x z <= &12 * inv(sqrt(mfd_scalar atlas g x))`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs")) CDM_ROUND_SCALAR THEN
  EXISTS_TAC `min e0 (&1 / &10)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`; `z:A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_round_component]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "sec1") (LABEL_TAC "close"))))))))) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ (U:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                    APX_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `x:A`; `z:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the scalar curvature at x *)
  USE_THEN "rs" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `g1:A->real^3^3`; `q:real`; `eps:real`; `U:A->bool`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  (* the g1 diameter *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `U:A->bool`; `x:A`; `z:A`] CANON_ROUND_G1_DIAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* comparison of g and g1 on the restricted manifold *)
  ABBREV_TAC `c = (&1 + eps) / q` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                 `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) U g1`;
                 `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) U g`;
                 `c:real`; `x:A`; `z:A`] RFAH_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                     `g:A->real^3^3`; `g1:A->real^3^3`; `c:real`; `y:A`]
                    CDM_RESTRICT_QF_LE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `w:real^3` THEN EXPAND_TAC "c" THEN MATCH_MP_TAC CDM_ROUND_QF THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `rfs_kreg eps`; `U:A->bool`] THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `x:A`] CDM_COMPONENT_CLASS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `x:A`; `z:A`] P2CO_CLASS_DIST) THEN
  ASM_SIMP_TAC[MFD_JOINABLE_REFL] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `sqrt c <= &3 * inv(sqrt R)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 * inv(sqrt R) = sqrt(&9 / R)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `sqrt(&9) = &3` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[real_div];
      ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN EXPAND_TAC "c" THEN
    SUBGOAL_THEN `inv q <= &7 * inv R` ASSUME_TAC THENL
     [SUBGOAL_THEN `&7 * inv R = inv(R / &7)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv q /\ &0 <= inv R` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&11 / &10) * (&7 * inv R)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt c * mfd_dist (subtopology top U,
                restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                (restrict_metric atlas U (g1:A->real^3^3)) (x:A) z` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt c * &4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Canonical neighbourhoods lie in balls of radius Dc(C,eps) R(x)^(-1/2).  *)

let CANON_NBHD_IN_BALL = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) C eps x U.
       hausdorff_space top /\ riemannian_metric atlas g /\ &1 <= C /\ &0 < eps /\
       eps <= eps0 /\ rfs_canonical_nbhd (top,atlas) g C eps x U
       ==> x IN U /\ &0 < mfd_scalar atlas g x /\
           !z. z IN U
               ==> mfd_joinable (top,atlas) x z /\
                   mfd_dist (top,atlas) g x z <=
                   max (sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)) (max (C * sqrt C) (&12)) *
                   inv(sqrt(mfd_scalar atlas g x))`,
  X_CHOOSE_THEN `er:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "round"))
    (INST_TYPE [`:A`,`:A`] CANON_ROUND_IN_BALL) THEN
  X_CHOOSE_THEN `es:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))
    (INST_TYPE [`:A`,`:A`] CDM_ROUND_SCALAR) THEN
  EXISTS_TAC `min (min er es) (&1 / &2)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `C:real`; `eps:real`; `x:A`; `U:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  ABBREV_TAC `Dc = max (sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)) (max (C * sqrt C) (&12))` THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) <= Dc /\ C <= Dc /\
                C * sqrt C <= Dc /\ &12 <= Dc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dc" THEN
    SUBGOAL_THEN `C <= C * sqrt C` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. &0 <= d /\ d <= Dc /\ &0 < mfd_scalar atlas (g:A->real^3^3) x
                    ==> d * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <=
                        Dc * inv(sqrt(mfd_scalar atlas g x))`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_canonical_nbhd (top,atlas) (g:A->real^3^3) C eps x U` THEN
  REWRITE_TAC[rfs_canonical_nbhd] THEN STRIP_TAC THENL
   [(* neck *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `z:A`]
                    CANON_NECK_IN_BALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)) *
                  inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
      USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]];
    (* cap *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
    SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`; `z:A`]
                  CANON_CAP_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* C-component *)
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `U:A->bool`; `x:A`] P2B_C_COMPONENT_SCALAR) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `U:A->bool`; `x:A`; `z:A`] CANON_CCOMP_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C * sqrt C) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
    USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    (* round component *)
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_round_component]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3`
         STRIP_ASSUME_TAC))))) THEN
      USE_THEN "rs" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `g1:A->real^3^3`; `q:real`; `eps:real`; `U:A->bool`; `x:A`]) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "round" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`; `z:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&12 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

