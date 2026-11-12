(* ========================================================================= *)
(* Unit pc_p2c_e994a (Part 2C): infrastructure for compact kappa-solutions,  *)
(* used for MT Thm 9.89 (2) (COR_9_94_L).  canon_L under parabolic rescaling *)
(* and monotone in C, round slices give round components (MT Thm 9.89 (1)),  *)
(* compact kappa-solutions with ksep have positive curvature (the cylinder   *)
(* model being noncompact) and R > 0 at time 0, and with the topology clause *)
(* their time-0 slice is a C-component for some C.                           *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_rfa_c971.ml";;
needs "src/pc_cmp_soul.ml";;
needs "src/pc_p2b_shrinkcl.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2b_tube2.ml";;
needs "src/pc_p2b_slice.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The kview of a parabolic rescaling, canon_L under rescaling               *)
(* and monotone in C.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2KC_KVIEW_RESCALE = prove
 (`!top atlas (g:real->B->real^3^3) q.
     &0 < q
     ==> p2b_kview (top,atlas) (\t x. q %% g (t / q) x) =
         p2b_rescale_view (p2b_kview (top,atlas) g) (&0) q`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; p2b_rescale_view; rfs_vtop; rfs_vatlas; rfs_vmetric;
              PAIR_EQ; FUN_EQ_THM; IN_ELIM_THM; REAL_ADD_LID] THEN
  X_GEN_TAC `s:real` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]);;

(* canon_L at time 0 is invariant under the parabolic rescaling q g(t / q). *)

let P2KC_CANON_L_RESCALE_IMP = prove
 (`!kappa top atlas (g:real->B->real^3^3) q C eps L x.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < q /\
     p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)
     ==> p2b_canon_L (p2b_kview (top,atlas) (\t x. q %% g (t / q) x)) C eps L x (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  ASM_SIMP_TAC[P2KC_KVIEW_RESCALE] THEN
  ABBREV_TAC `V = p2b_kview (top,atlas) (g:real->B->real^3^3)` THEN
  SUBGOAL_THEN `rfs_vtop (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                           (real->B->real^3^3)) (&0) = top /\
                rfs_vatlas V (&0) = atlas /\ rfs_vmetric V (&0) = g (&0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop (p2b_rescale_view (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                           (real->B->real^3^3)) (&0) q) (&0) = top /\
                rfs_vatlas (p2b_rescale_view V (&0) q) (&0) = atlas /\
                rfs_vmetric (p2b_rescale_view V (&0) q) (&0) = (\y. q %% g (&0) y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2b_rescale_view; rfs_vtop; rfs_vatlas; rfs_vmetric; real_div;
                REAL_MUL_LZERO; REAL_ADD_RID] THEN
    UNDISCH_TAC `rfs_vtop (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                           (real->B->real^3^3)) (&0) = top` THEN
    UNDISCH_TAC `rfs_vatlas (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                           (real->B->real^3^3)) (&0) = atlas` THEN
    UNDISCH_TAC `rfs_vmetric (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                           (real->B->real^3^3)) (&0) = g (&0)` THEN
    SPEC_TAC(`V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`,
             `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `p2b_canon_L (V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                              (real->B->real^3^3)) C eps L x (&0)` THEN
  REWRITE_TAC[p2b_canon_L] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[P2BCS_CAP_CMUL; P2BCS_CCOMP_CMUL; P2BCS_ROUND_CMUL;
               ISPEC `(g:real->B->real^3^3) (&0)` ETA_AX] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') ==> (a \/ b ==> a' \/ b)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`) THEN EXISTS_TAC `e:real^3->B` THEN
  MATCH_MP_TAC P2BT_EVOLVING_NECK_RESCALE THEN ASM_REWRITE_TAC[]);;

let P2KC_RESCALE_INVOLUTION = prove
 (`!(g:real->B->real^3^3) q.
     &0 < q
     ==> (\t x. inv q %% (\t x. q %% g (t / q) x) (t / inv q) x) = g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t / inv q) / q = t` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID]);;

let P2KC_CANON_L_RESCALE = prove
 (`!kappa top atlas (g:real->B->real^3^3) q C eps L x.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < q
     ==> (p2b_canon_L (p2b_kview (top,atlas) (\t x. q %% g (t / q) x)) C eps L x (&0) <=>
          p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\t x. q %% (g:real->B->real^3^3) (t / q) x`; `inv q`;
                   `C:real`; `eps:real`; `L:real`; `x:B`] P2KC_CANON_L_RESCALE_IMP) THEN
    ASM_SIMP_TAC[RFA_C971_KSOL_SCALE; REAL_LT_INV; P2KC_RESCALE_INVOLUTION];
    DISCH_TAC THEN MATCH_MP_TAC P2KC_CANON_L_RESCALE_IMP THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]]);;

(* canon_L is monotone in C (the cap and C-component clauses). *)

let P2KC_CANON_L_MONO_C = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C C' eps L x t.
     &1 < C /\ C <= C' /\ riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
     p2b_canon_L V C eps L x t
     ==> p2b_canon_L V C' eps L x t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_canon_L] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`U:A->bool`; `Y:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B_RFS_CAP_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B_RFS_C_COMPONENT_MONO_C THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `x:A`] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MT Thm 9.89 (1): a round slice at time 0 of a compact kappa-solution is   *)
(* an eps-round component (g1 = k g(0) has sec 1); and compact               *)
(* kappa-solutions with ksep have positive curvature at time 0 (the cylinder *)
(* model is noncompact).                                                     *)
(* ------------------------------------------------------------------------- *)

let P2KC_ROUND_CANON = prove
 (`!kappa top atlas (g:real->B->real^3^3) C eps L x.
     p2b_kappa_solution kappa (top,atlas) g /\ compact_space top /\ &0 < eps /\
     p2b_round (top,atlas) (g (&0)) /\ x IN topspace top
     ==> p2b_canon_L (p2b_kview (top,atlas) g) C eps L x (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KAPPA_SOLUTION_P2C) THEN
  REWRITE_TAC[p2c_kappa_sol] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[p2b_canon_L; P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `topspace top:B->bool` THEN
  ASM_REWRITE_TAC[rfs_round_component] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  UNDISCH_TAC `p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
  REWRITE_TAC[p2b_round] THEN DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real`; `\y. k %% (g:real->B->real^3^3) (&0) y`] THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`; `k:real`]
                RIEMANNIAN_METRIC_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `k:real`; `z:B`; `u:real^3`; `v:real^3`]
                  P2BCS_SECT_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `mfd_sectional atlas ((g:real->B->real^3^3) (&0)) z u v = k` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose; P2BL_LCK_DIST2_REFL] THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]);;

(* Positive curvature at time 0 for compact kappa-solutions with ksep. *)

let P2KC_COMPACT_POS_SEC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3).
     P2B_PROP_9_83K_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top
     ==> !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 < mfd_sectional atlas (g(&0)) x u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_83K_STATEMENT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[P2BSK_CYL_NOT_COMPACT]);;

(* ------------------------------------------------------------------------- *)
(* The time-0 slice of a compact kappa-solution with ksep and positive       *)
(* curvature is a C-component of its manifold for SOME C, once the topology  *)
(* clause holds: all the quantities are finite by compactness (sec >= k0 > 0 *)
(* by CMPSO_UNIFORM_CURV, R >= 6 k0, bounded R and diameter, the derivative  *)
(* bounds of COR_9_71).                                                      *)
(* ------------------------------------------------------------------------- *)

(* A manifold point has another point. *)

let P2KC_OTHER_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> ?y. y IN topspace top /\ ~(y = x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball((phi:A->real^N) x,r) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (phi:A->real^N) U)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = (phi:A->real^N) x + (r / &2) % basis 1` THEN
  SUBGOAL_THEN `(w:real^N) IN IMAGE (phi:A->real^N) U /\ ~(w = phi x)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm((r / &2) % basis 1:real^N) = r / &2` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th = `ball((phi:A->real^N) x,r) SUBSET IMAGE phi U`)) THEN
      EXPAND_TAC "w" THEN REWRITE_TAC[IN_BALL; NORM_ARITH `dist(a:real^N,a + b) = norm b`] THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH `a + b:real^N = a <=> b = vec 0`; GSYM NORM_EQ_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^N) w` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = phi(x:A))` THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* A reciprocal below a bound. *)

let P2KC_INV_LT = prove
 (`!z c. &0 < z ==> (inv z < c <=> &1 < c * z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `c:real`; `z:real`] REAL_LT_LDIV_EQ) THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LID]);;

(* The C-component property at one slice: a compact connected Riemannian     *)
(* 3-manifold with sec > 0, the COR_9_71 derivative bounds and the topology  *)
(* clause is a C-component of itself for some C.                             *)

let P2KC_CCOMP_SLICE = prove
 (`!top atlas (g0:B->real^3^3) C71.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
     ~(topspace top = {}) /\ compact_space top /\
     riemannian_metric atlas g0 /\ mfd_complete (top,atlas) g0 /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g0 x u v) /\
     (!x. x IN topspace top
          ==> sqrt(rfs_scalar_grad2 atlas g0 x) <=
              C71 * mfd_scalar atlas g0 x * sqrt(mfd_scalar atlas g0 x) /\
              abs(rfs_scalar_lap atlas g0 x + &2 * rfs_ric_norm2 atlas g0 x) <=
              C71 * mfd_scalar atlas g0 x pow 2) /\
     (mfd_diffeomorphic (subtopology top (topspace top)) (restrict_atlas atlas (topspace top))
                        (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
      rfs_has_twisted (subtopology top (topspace top)) (restrict_atlas atlas (topspace top)))
     ==> ?C. &1 < C /\ rfs_c_component (top,atlas) g0 C (topspace top)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(LABEL_TAC "der" o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_grad2" with Failure _ -> false))
        (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "pos" o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional" with Failure _ -> false))
        (concl th))) THEN
  SUBGOAL_THEN `?x0:B. x0 IN topspace top` (X_CHOOSE_TAC `x0:B`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x0:B`]
                P2KC_OTHER_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!p q:B. p IN topspace top /\ q IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) p q`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dpos = mfd_dist (top,atlas) (g0:B->real^3^3) x0 y0` THEN
  SUBGOAL_THEN `&0 < dpos` ASSUME_TAC THENL
   [EXPAND_TAC "dpos" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `x0:B`; `y0:B`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `x0:B`; `y0:B`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `&0 <= d /\ ~(d = &0) ==> &0 < d`];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Bd. !p. p IN topspace top
                         ==> mfd_dist (top,atlas) (g0:B->real^3^3) x0 p <= Bd`
  (X_CHOOSE_THEN `Bd:real` (LABEL_TAC "Bd")) THENL
   [SUBGOAL_THEN `real_bounded (IMAGE (\p. mfd_dist (top,atlas) (g0:B->real^3^3) x0 p)
                                      (topspace top))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[GSYM compact_space] THEN
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_dist (top,atlas) (g0:B->real^3^3) x0 x0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[]; USE_THEN "Bd" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q. p IN topspace top /\ q IN topspace top
                      ==> mfd_dist (top,atlas) (g0:B->real^3^3) p q <= &2 * Bd`
  (LABEL_TAC "diam") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `p:B`; `x0:B`; `q:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `p:B`; `x0:B`] MFD_DIST_SYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "Bd" (MP_TAC o C MP (ASSUME `(p:B) IN topspace top`) o SPEC `p:B`) THEN
    USE_THEN "Bd" (MP_TAC o C MP (ASSUME `(q:B) IN topspace top`) o SPEC `q:B`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a uniform positive lower bound of the sectional curvature *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`]
                CMPSO_UNIFORM_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x0:B`; `Bd:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> k0 <= mfd_sectional atlas (g0:B->real^3^3) y u v`
  (LABEL_TAC "k0") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> &6 * k0 <= mfd_scalar atlas (g0:B->real^3^3) y`
  (LABEL_TAC "R6") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `y:B`; `k0:real`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `SR = IMAGE (mfd_scalar atlas (g0:B->real^3^3)) (topspace top)` THEN
  SUBGOAL_THEN `~(SR:real->bool = {}) /\ (?b. !r. r IN SR ==> r <= b) /\
                (!r. r IN SR ==> &6 * k0 <= r)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "SR" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_bounded (IMAGE (mfd_scalar atlas (g0:B->real^3^3)) (topspace top))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[GSYM compact_space] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  ABBREV_TAC `Rmax = sup (SR:real->bool)` THEN ABBREV_TAC `Rmin = inf (SR:real->bool)` THEN
  SUBGOAL_THEN `(!y. y IN topspace top ==> mfd_scalar atlas (g0:B->real^3^3) y <= Rmax) /\
                &6 * k0 <= Rmin /\ Rmin <= Rmax /\ &0 < Rmin` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `SR:real->bool` SUP) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPEC `SR:real->bool` INF) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g0:B->real^3^3) x0 IN SR` ASSUME_TAC THENL
     [EXPAND_TAC "SR" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "SR" THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_scalar atlas (g0:B->real^3^3) x0` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&6 * k0` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `DS = {mfd_dist (top,atlas) (g0:B->real^3^3) x y | x,y |
                    x IN topspace top /\ y IN topspace top}` THEN
  SUBGOAL_THEN `dpos <= sup (DS:real->bool) /\ sup DS <= &2 * Bd` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(DS:real->bool = {}) /\ (!r. r IN DS ==> r <= &2 * Bd) /\ dpos IN DS`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "DS" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`dpos:real`; `x0:B`; `y0:B`] THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "diam" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`x0:B`; `y0:B`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `DS:real->bool` SUP) THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt Rmin /\ &0 < sqrt Rmax` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `C = &2 * Rmax / k0 + &2 * inv(sqrt Rmax * dpos) + &4 * Bd * sqrt Rmin +
                  abs C71 + &2` THEN
  SUBGOAL_THEN `&0 <= Rmax / k0 /\ &0 <= inv(sqrt Rmax * dpos) /\ &0 <= Bd * sqrt Rmin`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < C /\ &0 < C /\ C71 < C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[rfs_c_component] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING];
    ASM_REWRITE_TAC[GSYM compact_space];
    (* inf sec > inv C * sup R *)
    REWRITE_TAC[rfs_inf_gt] THEN EXISTS_TAC `k0:real` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `Rmax < k0 * C` MP_TAC THENL
       [SUBGOAL_THEN `Rmax = k0 * (Rmax / k0)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < k0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`Rmax:real`; `k0:real`; `C:real`] REAL_LT_LDIV_EQ) THEN
      ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* the diameter lower bound *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dpos:real` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(sqrt Rmax * dpos) < C` MP_TAC THENL
     [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt Rmax * dpos /\ &0 < C * sqrt Rmax` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2KC_INV_LT; GSYM REAL_INV_MUL] THEN REAL_ARITH_TAC;
    (* the diameter upper bound *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * Bd` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * Bd * sqrt Rmin < C` MP_TAC THENL
     [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    (* the gradient bound *)
    REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN EXISTS_TAC `C71:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "der" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top`) o SPEC `y:B`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g0:B->real^3^3) y` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&6 * k0` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; USE_THEN "R6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g0:B->real^3^3) y * sqrt(mfd_scalar atlas g0 y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    (* the Laplacian bound *)
    REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN EXISTS_TAC `C71:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "der" (MP_TAC o C MP (ASSUME `(y:B) IN topspace top`) o SPEC `y:B`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g0:B->real^3^3) y pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&6 * k0` THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; USE_THEN "R6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* The C-component property for compact kappa-solutions with ksep. *)

let P2KC_CCOMP_SOME = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3).
     P2B_PROP_9_83K_STATEMENT w /\ P2B_COR_9_71_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ compact_space top /\
     (mfd_diffeomorphic (subtopology top (topspace top)) (restrict_atlas atlas (topspace top))
                        (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
      rfs_has_twisted (subtopology top (topspace top)) (restrict_atlas atlas (topspace top)))
     ==> ?C. &1 < C /\ rfs_c_component (top,atlas) (g (&0)) C (topspace top)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KAPPA_SOLUTION_P2C) THEN
  REWRITE_TAC[p2c_kappa_sol] THEN STRIP_TAC THEN
  UNDISCH_TAC `P2B_COR_9_71_STATEMENT (w:B->bool)` THEN REWRITE_TAC[P2B_COR_9_71_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `C71:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2KC_CCOMP_SLICE THEN EXISTS_TAC `C71:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2KC_COMPACT_POS_SEC THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `x:B`; `&0`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* R > 0 at time 0 on a compact kappa-solution with ksep, from positive      *)
(* curvature (P2KC_COMPACT_POS_SEC) and a positive lower bound of the       *)
(* sectional curvature at the point (CMPSO_UNIFORM_CURV).  Used to          *)
(* normalise R(x,0) = 1 at a given point (Claim 9.90, the main theorem).    *)
(* ------------------------------------------------------------------------- *)

let P2KC_COMPACT_R_POS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) x.
     P2B_PROP_9_83K_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p2b_ksep top atlas /\ compact_space top /\ x IN topspace top
     ==> &0 < mfd_scalar atlas (g (&0)) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KAPPA_SOLUTION_P2C) THEN
  REWRITE_TAC[p2c_kappa_sol] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]
                P2KC_COMPACT_POS_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`] CMPSO_UNIFORM_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:B`; `&0`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `x:B`; `k0:real`] P2BS_MFD_SCALAR_SECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIST_REFL; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

