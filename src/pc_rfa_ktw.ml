(* ========================================================================= *)
(* Unit pc_rfa_ktw: case M2 of piece (d) of COR_9_94_L, the twisted model,   *)
(* the statement P2B_KNCL_TWISTED_CANON_STATEMENT of pc_p2b_kncltwreq,       *)
(* proved as RFA_P2B_KNCL_TWISTED_CANON.  The Z/2 quotient of the cylinder   *)
(* model is canonical at time 0.  Far points p y0 (|y0| > e^a,               *)
(* a = 1/(sqrt 2 eps)) are centres of exact evolving necks p o (|y0| .)      *)
(* (dilation invariance, Z2X_MODEL_NECK of pc_z2x_neck for the slice); the   *)
(* other points lie in the core of an explicit twisted cap: the chart        *)
(* p o phi with phi a radial map commuting with rfs_twist, equal to the      *)
(* identity near the unit sphere and to rho . on annulus(2,4), rho = e^a;    *)
(* the necks are p o (2 rho .) and p o (2 e^(2a) .).  R = 1/lam is constant, *)
(* so the cap constants come from the model: diameter by model paths, volume *)
(* by boxes (pc_p2a_cylm), ball volumes from P2ACM_STD_UNIT_BALL after       *)
(* scaling.                                                                  *)
(* ========================================================================= *)

needs "src/pc_p2b_kncltwreq.ml";;
needs "src/pc_z2x_neck.ml";;
needs "src/pc_p2b_cylnecks.ml";;
needs "src/pc_p2a_zq.ml";;
needs "src/pc_p2a_cylm.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_sch_isoext.ml";;
needs "src/pc_grg_dist_in.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The hypotheses of the statement as one predicate, the slice               *)
(* at time 0 as the two-to-one models of pc_p2a_zq and pc_p2a_cylm, the view *)
(* p2b_kview, and the curvature of the slice at time 0: R = 1/lam,           *)
(* grad R = 0, Lap R = 0, abs(Ric)^2 = 1/(2 lam^2) at every point.           *)
(* ------------------------------------------------------------------------- *)

let rfa_ktw_model = new_definition
 `rfa_ktw_model (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                (g:real->B->real^3^3) (p:real^3->B) (lam:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < lam /\
    (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
    IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
    (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
    (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
    (!t y. t <= &0 /\ ~(y = vec 0)
           ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y)`;;

let RFA_KTW_G0 = prove
 (`!top atlas (g:real->B->real^3^3) p lam.
     rfa_ktw_model (top,atlas) g p lam
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < lam /\
         riemannian_metric atlas (g(&0)) /\
         p2azq_model (top,atlas) (g(&0)) p lam /\ p2acm_std (top,atlas) (g(&0)) p lam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_ktw_model] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric"))
          (concl th))) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~(y = vec 0)
                    ==> rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) (&0)) y =
                        lam %% cylinder_flow (&0) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_pullback")) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2azq_model; p2acm_std]);;

let RFA_KTW_KVIEW = prove
 (`!top atlas (g:real->B->real^3^3) t.
     rfs_vtop (p2b_kview (top,atlas) g) t =
       (if t <= &0 then top else discrete_topology {}) /\
     rfs_vatlas (p2b_kview (top,atlas) g) t = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) g) t = g t /\
     rfs_vscalar (p2b_kview (top,atlas) g) t = mfd_scalar atlas (g t)`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar;
              IN_ELIM_THM; FUN_EQ_THM]);;

(* Every point has a lift; p is a parametrization on B(w, |w|/2).           *)

let RFA_KTW_LIFT = prove
 (`!top atlas (g:real->B->real^3^3) p lam x.
     rfa_ktw_model (top,atlas) g p lam /\ x IN topspace top
     ==> ?w. &1 <= norm w /\ p w = x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `x:B`]
                P2AZQ_LIFT_GE1) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let RFA_KTW_PARAM_NEAR = prove
 (`!top atlas (g:real->B->real^3^3) p lam w.
     rfa_ktw_model (top,atlas) g p lam /\ ~(w = vec 0)
     ==> mfd_param top atlas (ball(w,norm w / &2)) p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MATCH_MP_TAC P2ACM_STD_PARAM_NEAR THEN
  MAP_EVERY EXISTS_TAC [`(g:real->B->real^3^3) (&0)`; `lam:real`] THEN ASM_REWRITE_TAC[]);;

let RFA_KTW_BALL_NZ = prove
 (`!w z:real^3. ~(w = vec 0) /\ z IN ball(w,norm w / &2) ==> ~(z = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `dist(w:real^3,vec 0) < norm w / &2` THEN REWRITE_TAC[DIST_0] THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The local scalar curvature of the pullback of g(0) by p is 1/lam. *)

let RFA_KTW_LSCALAR_PB = prove
 (`!top atlas (g:real->B->real^3^3) p lam z.
     rfa_ktw_model (top,atlas) g p lam /\ ~(z = vec 0)
     ==> lscalar (rfs_pullback atlas p (g(&0))) z = inv lam`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2azq_model] o
    check (fun th -> is_comb(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2azq_model")) (concl th))) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lscalar (\y:real^3. lam %% cylinder_flow (&0) y) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`; `lam:real`; `z:real^3`]
                LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01; IN_DELETE; IN_UNIV]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`&0`; `z:real^3`] RFB_CYL_SCALAR) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LID; REAL_INV_1]);;

let RFA_KTW_SCALAR = prove
 (`!top atlas (g:real->B->real^3^3) p lam x.
     rfa_ktw_model (top,atlas) g p lam /\ x IN topspace top
     ==> mfd_scalar atlas (g(&0)) x = inv lam`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `x:B`] RFA_KTW_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 <= norm(vec 0:real^3)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `ball(w:real^3,norm w / &2)`; `p:real^3->B`;
                 `w:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_KTW_PARAM_NEAR THEN
      MAP_EVERY EXISTS_TAC [`g:real->B->real^3^3`; `lam:real`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&1 <= norm(w:real^3)` THEN REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RFA_KTW_LSCALAR_PB THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Far points.  For rho > e^a (a = 1/(sqrt 2 eps)) and a unit                *)
(* vector u, e = p o (rho .) is an evolving eps-neck of every length L at    *)
(* p(rho u) and time 0: the slice is the neck of Z2X_MODEL_NECK, and for    *)
(* s <= 0 the pullback of g(s lam) by e is lam cylinder_flow(s), since the   *)
(* shrinking cylinder is dilation invariant (RFA_KTW_CYL_DIL), so the        *)
(* normalized family is exactly cylinder_flow s.                             *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_CYL_DIL = prove
 (`!s rho (z:real^3).
     &0 < rho /\ ~(z = vec 0)
     ==> cylinder_flow s (rho % z) = inv(rho pow 2) %% cylinder_flow s z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; cylinder_flow; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT; VECTOR_MUL_COMPONENT; NORM_MUL] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN COND_CASES_TAC THEN
  UNDISCH_TAC `&0 < norm(z:real^3)` THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD);;

let RFA_KTW_FAR_NECK = prove
 (`!top atlas (g:real->B->real^3^3) p lam eps rho u L.
     rfa_ktw_model (top,atlas) g p lam /\ &0 < eps /\ exp(inv(sqrt(&2) * eps)) < rho /\
     norm u = &1 /\ &0 < L
     ==> rfs_evolving_neck (p2b_kview (top,atlas) g) eps (p (rho % u)) (&0) L
                           (p o (\w. rho % w)) /\
         rfs_neck (top,atlas) (g(&0)) eps (p (rho % u)) (p o (\w. rho % w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `eps:real`;
                 `rho:real`; `u:real^3`] Z2X_MODEL_NECK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "out") (K ALL_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `exp(inv(sqrt(&2) * eps))` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((p:real^3->B) o (\w. rho % w))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) eps (p (rho % u))
                   ((p:real^3->B) o (\w. rho % w))` THEN
    REWRITE_TAC[rfs_neck] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the pullback of every slice by the neck map *)
  SUBGOAL_THEN
   `!tau v. tau <= &0 /\ v IN rfs_neck_dom eps
            ==> rfs_pullback atlas ((p:real^3->B) o (\w. rho % w)) ((g:real->B->real^3^3) tau) v =
                lam %% cylinder_flow (tau / lam) v`
  (LABEL_TAC "pf") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) tau`; `{y:real^3 | &1 < norm y}`;
                   `rfs_neck_dom eps`; `p:real^3->B`; `rho:real`] APX_RFS_PULLBACK_DILATE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "out" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:real^3) IN rfs_neck_dom eps`)]) THEN
    SUBGOAL_THEN `~(v:real^3 = vec 0) /\ ~(rho % v:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [USE_THEN "out" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(v:real^3) IN rfs_neck_dom eps`))) THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
      ASM_CASES_TAC `v:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; NORM_0] THEN UNDISCH_TAC `&0 < rho` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `rfa_ktw_model (top,atlas) (g:real->B->real^3^3) p lam` THEN
    REWRITE_TAC[rfa_ktw_model] THEN
    DISCH_THEN(MP_TAC o SPECL [`tau:real`; `rho % v:real^3`] o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[RFA_KTW_CYL_DIL; MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps ==> ~(y = vec 0)` ASSUME_TAC THENL
   [MESON_TAC[P2BCY_NECK_DOM_NZ; SUBSET; IN_DELETE]; ALL_TAC] THEN
  (* each closeness distance of the normalized family vanishes *)
  SUBGOAL_THEN
   `!s k y. s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 k (cylinder_flow s)
                  (\z. inv lam %%
                       rfs_pullback atlas ((p:real^3->B) o (\w. rho % w))
                                    ((g:real->B->real^3^3) (&0 + s / inv lam)) z) y = &0`
  (LABEL_TAC "zero") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `cylinder_flow s`; `cylinder_flow s`; `cylinder_flow s`;
                   `\z. inv lam %%
                        rfs_pullback atlas ((p:real^3->B) o (\w. rho % w))
                                     ((g:real->B->real^3^3) (&0 + s / inv lam)) z`;
                   `rfs_neck_dom eps`; `y:real^3`] LCK_DIST2_LOCAL) THEN
    REWRITE_TAC[APX_NECK_DOM_OPEN] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `&0 + s / inv lam = s * lam` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ADD_LID; real_div; REAL_INV_INV]; ALL_TAC] THEN
      SUBGOAL_THEN `s * lam <= &0` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= --s * l ==> s * l <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "pf" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `s * lam <= &0`) (ASSUME `(z:real^3) IN rfs_neck_dom eps`))]) THEN
      REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
      SUBGOAL_THEN `(s * lam) / lam = s /\ inv lam * lam = &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REWRITE_TAC[MATRIX_CMUL_LID];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[P2BCY_LCK_DIST2_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; RFA_KTW_KVIEW; REAL_LE_REFL] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) (p (rho % (u:real^3))) = inv lam`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; SUBSET_REFL];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "zero" (MP_TAC o SPECL [`s:real`; `rfs_kreg eps`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL])]);;


(* ------------------------------------------------------------------------- *)
(* The radial map of the core chart.  rfa_ktw_step is a smooth               *)
(* step in r = |y|^2, 0 for r <= 9/4 and 1 for r >= 4; the map               *)
(* rfa_ktw_out rho y = (1 + (rho - 1) step(|y|^2)) y is the identity on      *)
(* |y| <= 3/2 and rho y on |y| >= 2; it is smooth with injective derivative  *)
(* everywhere, and injective, with |out y| = h(|y|) for the increasing       *)
(* profile h(r) = (1 + (rho - 1) step(r^2)) r.                               *)
(* ------------------------------------------------------------------------- *)

let rfa_ktw_step = new_definition
 `rfa_ktw_step (r:real) = smooth_step((r - &9 / &4) * &4 / &7)`;;

let rfa_ktw_out = new_definition
 `rfa_ktw_out (rho:real) (y:real^3) =
    (&1 + (rho - &1) * rfa_ktw_step (norm y pow 2)) % y`;;

let rfa_ktw_h = new_definition
 `rfa_ktw_h (rho:real) (r:real) = (&1 + (rho - &1) * rfa_ktw_step (r pow 2)) * r`;;

let RFA_KTW_STEP_0 = prove
 (`!r. r <= &9 / &4 ==> rfa_ktw_step r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_step] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  ASM_REAL_ARITH_TAC);;

let RFA_KTW_STEP_1 = prove
 (`!r. &4 <= r ==> rfa_ktw_step r = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_step] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
  ASM_REAL_ARITH_TAC);;

let RFA_KTW_STEP_BOUNDS = prove
 (`!r. &0 <= rfa_ktw_step r /\ rfa_ktw_step r <= &1`,
  REWRITE_TAC[rfa_ktw_step; SMOOTH_STEP_BOUNDS]);;

let RFA_KTW_STEP_MONO = prove
 (`!r s. r <= s ==> rfa_ktw_step r <= rfa_ktw_step s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_step] THEN MATCH_MP_TAC SMOOTH_STEP_MONO THEN
  ASM_REAL_ARITH_TAC);;

let RFA_KTW_Q_GE1 = prove
 (`!rho r. &1 <= rho ==> &1 <= &1 + (rho - &1) * rfa_ktw_step r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (rho - &1) * rfa_ktw_step r` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[RFA_KTW_STEP_BOUNDS] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* smooth_step has a nonnegative derivative everywhere (the argument of     *)
(* STDCAP_SS_DERIV, pc_p2c_stdcap, outside this closure).                    *)

let RFA_KTW_SS_DERIV = prove
 (`!u. (smooth_step has_real_derivative real_derivative smooth_step u) (atreal u) /\
       &0 <= real_derivative smooth_step u`,
  SUBGOAL_THEN `!u. (smooth_step has_real_derivative real_derivative smooth_step u) (atreal u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `smooth_step real_differentiable (atreal u)` MP_TAC THENL
     [REWRITE_TAC[REAL_DIFFERENTIABLE_AT] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_STEP_SMOOTH];
      REWRITE_TAC[real_differentiable; real_derivative] THEN
      DISCH_TAC THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`smooth_step`; `real_derivative smooth_step`; `(:real)`]
                HAS_REAL_DERIVATIVE_INCREASING) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; EXTENSION; IN_UNIV; IN_SING] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `a + &1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[SMOOTH_STEP_MONO]);;

let RFA_KTW_STEP_DERIV = prove
 (`!r. ?d. (rfa_ktw_step has_real_derivative d) (atreal r) /\ &0 <= d`,
  GEN_TAC THEN
  EXISTS_TAC `&4 / &7 * real_derivative smooth_step ((r - &9 / &4) * &4 / &7)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `rfa_ktw_step = (\x. smooth_step ((\r. (r - &9 / &4) * &4 / &7) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_ktw_step]; ALL_TAC] THEN
    MP_TAC(INST [`real_derivative smooth_step`,`g':real->real`; `&4 / &7`,`f':real`]
            (ISPECL [`\r. (r - &9 / &4) * &4 / &7`; `smooth_step`]
                    HAS_REAL_DERIVATIVE_CHAIN_UNIV)) THEN
    REWRITE_TAC[RFA_KTW_SS_DERIV] THEN DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MP_TAC(REAL_DIFF_CONV `((\r. (r - &9 / &4) * &4 / &7) has_real_derivative f)
                               (atreal r)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      BETA_TAC THEN SIMP_TAC[]];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[RFA_KTW_SS_DERIV] THEN REAL_ARITH_TAC]);;

let RFA_KTW_STEP_CONT = prove
 (`!s. rfa_ktw_step real_continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MP_TAC(SPEC `r:real` RFA_KTW_STEP_DERIV) THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

(* The map out: identity near the unit sphere, rho . far out.               *)

let RFA_KTW_OUT_ID = prove
 (`!rho y:real^3. norm y <= &3 / &2 ==> rfa_ktw_out rho y = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_out] THEN
  SUBGOAL_THEN `rfa_ktw_step (norm(y:real^3) pow 2) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_KTW_STEP_0 THEN
    SUBGOAL_THEN `norm(y:real^3) pow 2 <= (&3 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; VECTOR_MUL_LID]]);;

let RFA_KTW_OUT_DIL = prove
 (`!rho y:real^3. &2 <= norm y ==> rfa_ktw_out rho y = rho % y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_out] THEN
  SUBGOAL_THEN `rfa_ktw_step (norm(y:real^3) pow 2) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_KTW_STEP_1 THEN
    SUBGOAL_THEN `(&2) pow 2 <= norm(y:real^3) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let RFA_KTW_OUT_NORM = prove
 (`!rho y:real^3. &1 <= rho ==> norm(rfa_ktw_out rho y) = rfa_ktw_h rho (norm y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_out; rfa_ktw_h; NORM_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> abs x = x`) THEN
  ASM_SIMP_TAC[RFA_KTW_Q_GE1]);;

let RFA_KTW_H_MONO = prove
 (`!rho r s. &1 <= rho /\ &0 <= r /\ r < s ==> rfa_ktw_h rho r < rfa_ktw_h rho s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_h] THEN
  SUBGOAL_THEN `rfa_ktw_step (r pow 2) <= rfa_ktw_step (s pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_KTW_STEP_MONO THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho:real`; `s pow 2`] RFA_KTW_Q_GE1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + (rho - &1) * rfa_ktw_step (s pow 2)) * r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC]);;

let RFA_KTW_H_VALUES = prove
 (`!rho r. &1 <= rho
           ==> rfa_ktw_h rho (&1) = &1 /\ rfa_ktw_h rho (&2) = &2 * rho /\
               (&0 <= r ==> r <= rfa_ktw_h rho r) /\
               (&0 <= r /\ r <= &3 / &2 ==> rfa_ktw_h rho r = r) /\
               (&2 <= r ==> rfa_ktw_h rho r = rho * r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[rfa_ktw_h] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `rfa_ktw_step (&1 pow 2) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_KTW_STEP_0 THEN CONV_TAC REAL_RAT_REDUCE_CONV; REAL_ARITH_TAC];
    SUBGOAL_THEN `rfa_ktw_step (&2 pow 2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_KTW_STEP_1 THEN CONV_TAC REAL_RAT_REDUCE_CONV; REAL_ARITH_TAC];
    DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RFA_KTW_Q_GE1];
    STRIP_TAC THEN
    SUBGOAL_THEN `rfa_ktw_step (r pow 2) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_KTW_STEP_0 THEN
      SUBGOAL_THEN `r pow 2 <= (&3 / &2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `rfa_ktw_step (r pow 2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_KTW_STEP_1 THEN
      SUBGOAL_THEN `(&2) pow 2 <= r pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let RFA_KTW_H_CONT = prove
 (`!rho s. (rfa_ktw_h rho) real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `rfa_ktw_h rho = (\r. (&1 + (rho - &1) * rfa_ktw_step (r pow 2)) * r)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_ktw_h]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
  SUBGOAL_THEN `(\r. rfa_ktw_step (r pow 2)) = rfa_ktw_step o (\r. r pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[RFA_KTW_STEP_CONT] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID]);;

(* out is injective, nonzero away from 0, and onto the shell [1,2 rho]      *)
(* from the shell [1,2] (intermediate values).                              *)

let RFA_KTW_OUT_INJ = prove
 (`!rho y z:real^3. &1 <= rho /\ rfa_ktw_out rho y = rfa_ktw_out rho z ==> y = z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(y:real^3) = norm(z:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`rho:real`; `y:real^3`] RFA_KTW_OUT_NORM) THEN
    MP_TAC(SPECL [`rho:real`; `z:real^3`] RFA_KTW_OUT_NORM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `rfa_ktw_h rho (norm(y:real^3)) = rfa_ktw_h rho (norm(z:real^3))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(SPECL [`rho:real`; `norm(z:real^3)`; `norm(y:real^3)`] RFA_KTW_H_MONO);
      MP_TAC(SPECL [`rho:real`; `norm(y:real^3)`; `norm(z:real^3)`] RFA_KTW_H_MONO)] THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfa_ktw_out rho y = rfa_ktw_out rho (z:real^3)` THEN
  ASM_REWRITE_TAC[rfa_ktw_out; VECTOR_MUL_LCANCEL] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN
  MP_TAC(SPECL [`rho:real`; `norm(z:real^3) pow 2`] RFA_KTW_Q_GE1) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFA_KTW_OUT_NZ = prove
 (`!rho y:real^3. &1 <= rho /\ ~(y = vec 0) ==> ~(rfa_ktw_out rho y = vec 0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `rfa_ktw_out rho y = vec 0:real^3` THEN
  ASM_REWRITE_TAC[rfa_ktw_out; VECTOR_MUL_EQ_0] THEN
  MP_TAC(SPECL [`rho:real`; `norm(y:real^3) pow 2`] RFA_KTW_Q_GE1) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFA_KTW_OUT_ONTO = prove
 (`!rho w:real^3. &1 <= rho /\ &1 <= norm w /\ norm w <= &2 * rho
                  ==> ?y. &1 <= norm y /\ norm y <= &2 /\ rfa_ktw_out rho y = w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rfa_ktw_h rho`; `&1`; `&2`; `norm(w:real^3)`] REAL_IVT_INCREASING) THEN
  ASM_SIMP_TAC[RFA_KTW_H_CONT; RFA_KTW_H_VALUES] THEN ANTS_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `r IN real_interval[&1,&2]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(r / norm(w:real^3)) % w` THEN
  SUBGOAL_THEN `norm((r / norm(w:real^3)) % w) = r` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= r ==> abs r = r`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfa_ktw_out] THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  UNDISCH_TAC `rfa_ktw_h rho r = norm(w:real^3)` THEN REWRITE_TAC[rfa_ktw_h] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN UNDISCH_TAC `(&1 + (rho - &1) * rfa_ktw_step (r pow 2)) * r = norm(w:real^3)` THEN
  UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD);;


(* ------------------------------------------------------------------------- *)
(* out and rfs_twist are diffeomorphisms of real^3 minus 0.                  *)
(* out is smooth with derivative h |-> Q h + c (z.h) z, Q >= 1, c >= 0,     *)
(* which is injective, and out is a bijection (intermediate values on       *)
(* [0,2] and the dilation beyond), so SCHI_INJ_DIFFEO applies; rfs_twist is *)
(* a smooth involution.                                                      *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_OUT_SMOOTH = prove
 (`!rho. smooth_map_on (:real^3) (rfa_ktw_out rho)`,
  GEN_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z:real^3. lift(rfa_ktw_step(norm z pow 2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfa_ktw_step] THEN
    MP_TAC(ISPECL [`(:real^3)`;
                   `\z:real^3. (&4 / &7) % (lift(norm z pow 2) - lift(&9 / &4))`]
                  SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`(:real^3)`; `\z:real^3. z`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_ktw_out rho =
    (\z:real^3. drop((\z. lift(&1) + (rho - &1) % lift(rfa_ktw_step(norm z pow 2))) z) %
                (\z. z) z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_ktw_out; DROP_ADD; DROP_CMUL; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let RFA_KTW_LIN_INJ = prove
 (`!Q c (z:real^3) h. &1 <= Q /\ &0 <= c /\ Q % h + (c * (z dot h)) % z = vec 0
                      ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) dot h = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (z:real^3) dot v`) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO] THEN
    SUBGOAL_THEN `&0 <= c * ((z:real^3) dot z)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
    ABBREV_TAC `x = (z:real^3) dot h` THEN ABBREV_TAC `w = (z:real^3) dot z` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `x * (Q + c * w) = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `Q % h + (c * ((z:real^3) dot h)) % z = vec 0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN ASM_REAL_ARITH_TAC);;

let RFA_KTW_OUT_DERIV = prove
 (`!rho (z:real^3).
     &1 <= rho
     ==> ?L. (rfa_ktw_out rho has_derivative L) (at z) /\ linear L /\
             (!h. L h = vec 0 ==> h = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `norm(z:real^3) pow 2` RFA_KTW_STEP_DERIV) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `((\r. &1 + (rho - &1) * rfa_ktw_step r) has_real_derivative ((rho - &1) * d))
                (atreal (norm(z:real^3) pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\r:real. &1`; `&0`; `\r. (rho - &1) * rfa_ktw_step r`; `(rho - &1) * d`;
                   `atreal (norm(z:real^3) pow 2)`] HAS_REAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o (\y:real^3. &1 + (rho - &1) * rfa_ktw_step (norm y pow 2))) has_derivative
     (lift o (\h. ((rho - &1) * d * &2) * (z dot h)))) (at z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\r. &1 + (rho - &1) * rfa_ktw_step r`; `(rho - &1) * d`;
                   `\y:real^3. lift(norm y pow 2)`; `\h:real^3. &2 % lift(z dot h)`;
                   `z:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^3. &1 + (rho - &1) * rfa_ktw_step (norm y pow 2)`;
                 `\h:real^3. ((rho - &1) * d * &2) * (z dot h)`;
                 `\y:real^3. y`; `\h:real^3. h`; `z:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfa_ktw_out rho =
                (\x:real^3. (&1 + (rho - &1) * rfa_ktw_step (norm x pow 2)) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_ktw_out]; ALL_TAC] THEN
  EXISTS_TAC `\h:real^3. (&1 + (rho - &1) * rfa_ktw_step (norm(z:real^3) pow 2)) % h +
                         (((rho - &1) * d * &2) * (z dot h)) % z` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR th));
    ALL_TAC] THEN
  X_GEN_TAC `h:real^3` THEN BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (rho - &1) * d * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_KTW_LIN_INJ THEN
  MAP_EVERY EXISTS_TAC [`&1 + (rho - &1) * rfa_ktw_step (norm(z:real^3) pow 2)`;
                        `(rho - &1) * d * &2`; `z:real^3`] THEN
  ASM_SIMP_TAC[RFA_KTW_Q_GE1]);;

let RFA_KTW_OUT_DET = prove
 (`!rho (z:real^3).
     &1 <= rho ==> ~(det(matrix(frechet_derivative (rfa_ktw_out rho) (at z))) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rho:real`; `z:real^3`] RFA_KTW_OUT_DERIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^3->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  UNDISCH_TAC `det(matrix(L:real^3->real^3)) = &0` THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[]);;

(* out is a bijection of real^3 minus 0. *)

let RFA_KTW_OUT_ONTO0 = prove
 (`!rho w:real^3. &1 <= rho /\ ~(w = vec 0)
                  ==> ?y. ~(y = vec 0) /\ rfa_ktw_out rho y = w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ rfa_ktw_h rho r = norm(w:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `norm(w:real^3) <= &2 * rho` THENL
     [MP_TAC(SPECL [`rfa_ktw_h rho`; `&0`; `&2`; `norm(w:real^3)`] REAL_IVT_INCREASING) THEN
      ASM_SIMP_TAC[RFA_KTW_H_CONT; RFA_KTW_H_VALUES] THEN ANTS_TAC THENL
       [REWRITE_TAC[rfa_ktw_h; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `r = &0` THENL
       [UNDISCH_TAC `rfa_ktw_h rho r = norm(w:real^3)` THEN
        ASM_REWRITE_TAC[rfa_ktw_h; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `r IN real_interval[&0,&2]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC];
      EXISTS_TAC `norm(w:real^3) / rho` THEN
      SUBGOAL_THEN `&2 <= norm(w:real^3) / rho /\ &0 < rho` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
                        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RFA_KTW_H_VALUES] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  EXISTS_TAC `(r / norm(w:real^3)) % w` THEN
  SUBGOAL_THEN `norm((r / norm(w:real^3)) % w) = r` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfa_ktw_out] THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  UNDISCH_TAC `rfa_ktw_h rho r = norm(w:real^3)` THEN REWRITE_TAC[rfa_ktw_h] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN
  UNDISCH_TAC `(&1 + (rho - &1) * rfa_ktw_step (r pow 2)) * r = norm(w:real^3)` THEN
  UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD);;

let RFA_KTW_OUT_DIFFEO = prove
 (`!rho. &1 <= rho
         ==> ?g. diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                   g (rfa_ktw_out rho)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rfa_ktw_out rho`; `(:real^3) DELETE vec 0`] SCHI_INJ_DIFFEO) THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[RFA_KTW_OUT_SMOOTH; SUBSET_UNIV];
      ASM_MESON_TAC[RFA_KTW_OUT_INJ];
      ASM_SIMP_TAC[RFA_KTW_OUT_DET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (rfa_ktw_out rho) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_KTW_OUT_NZ THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MP_TAC(SPECL [`rho:real`; `w:real^3`] RFA_KTW_OUT_ONTO0) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MESON_TAC[DIFFEOMORPHISM_ON_SYM]);;

(* rfs_twist is a smooth involution of real^3 minus 0. *)

let RFA_KTW_TWIST_INV = prove
 (`!y:real^3. ~(y = vec 0) ==> rfs_twist(rfs_twist y) = y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [rfs_twist] THEN
  ASM_SIMP_TAC[P2ACM_TWIST_NORM2; REAL_INV_INV] THEN
  REWRITE_TAC[rfs_twist; VECTOR_MUL_RNEG; VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 * inv(norm y pow 2) = &1`
  (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH]);;

let RFA_KTW_TWIST_DIFFEO = prove
 (`diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) rfs_twist rfs_twist`,
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0) rfs_twist` ASSUME_TAC THENL
   [SUBGOAL_THEN `(:real^3) DELETE vec 0 = {x:real^3 | ~(x = vec 0)}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rfs_twist = (\x:real^3. --((\x. inv(norm x pow 2) % x) x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; rfs_twist]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_INVERSION];
    ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV; P2ACM_TWIST_NZ; RFA_KTW_TWIST_INV]);;


(* ------------------------------------------------------------------------- *)
(* The core chart.  phi = out on |y| >= 1 and                                *)
(* twist o out o twist inside; phi commutes with rfs_twist, is injective,    *)
(* is rho . on |y| >= 2, and p o phi equals p o out on |y| > 2/3 and         *)
(* p o out o twist on |y| < 1 (p is twist invariant), so p o phi is a        *)
(* parametrization near every point (P2ACM_PARAM_PRECOMP) and a twisted      *)
(* chart (RFA_KTW_TWISTED).                                                  *)
(* ------------------------------------------------------------------------- *)

let rfa_ktw_phi = new_definition
 `rfa_ktw_phi (rho:real) (y:real^3) =
    if &1 <= norm y then rfa_ktw_out rho y else rfs_twist(rfa_ktw_out rho (rfs_twist y))`;;

let RFA_KTW_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  SIMP_TAC[P2AZQ_TWIST_FACTS]);;

let RFA_KTW_PHI_NZ = prove
 (`!rho y:real^3. &1 <= rho /\ ~(y = vec 0) ==> ~(rfa_ktw_phi rho y = vec 0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `rfa_ktw_phi rho y = vec 0:real^3` THEN
  REWRITE_TAC[rfa_ktw_phi] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[RFA_KTW_OUT_NZ];
    MATCH_MP_TAC P2ACM_TWIST_NZ THEN MATCH_MP_TAC RFA_KTW_OUT_NZ THEN
    ASM_SIMP_TAC[P2ACM_TWIST_NZ]]);;

let RFA_KTW_PHI_NORM1 = prove
 (`!rho y:real^3. &1 <= rho /\ ~(y = vec 0)
                  ==> (&1 <= norm(rfa_ktw_phi rho y) <=> &1 <= norm y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_phi] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[RFA_KTW_OUT_NORM] THEN
    MP_TAC(SPECL [`rho:real`; `norm(y:real^3)`] RFA_KTW_H_VALUES) THEN
    ASM_SIMP_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(rfs_twist y = vec 0:real^3) /\ ~(rfa_ktw_out rho (rfs_twist y) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2ACM_TWIST_NZ; RFA_KTW_OUT_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_KTW_TWIST_NORM; RFA_KTW_OUT_NORM] THEN
  MP_TAC(SPECL [`rho:real`; `norm(rfs_twist (y:real^3))`] RFA_KTW_H_VALUES) THEN
  ASM_SIMP_TAC[NORM_POS_LE; RFA_KTW_TWIST_NORM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ norm y < &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < inv(norm(y:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < rfa_ktw_h rho (inv(norm(y:real^3)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(norm(y:real^3))` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]);;

let RFA_KTW_PHI_TWIST = prove
 (`!rho y:real^3. &1 <= rho /\ ~(y = vec 0)
                  ==> rfa_ktw_phi rho (rfs_twist y) = rfs_twist(rfa_ktw_phi rho y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(rfs_twist y = vec 0:real^3) /\ norm(rfs_twist y) = inv(norm y) /\
                &0 < norm(y:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2ACM_TWIST_NZ; RFA_KTW_TWIST_NORM; NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[rfa_ktw_phi] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `norm(y:real^3) = &1` THENL
   [ASM_REWRITE_TAC[REAL_INV_1; REAL_LE_REFL] THEN
    SUBGOAL_THEN `norm(rfs_twist y:real^3) <= &3 / &2 /\ norm(y:real^3) <= &3 / &2`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RFA_KTW_OUT_ID];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= norm(y:real^3)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(&1 <= inv(norm(y:real^3)))` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[RFA_KTW_TWIST_INV]];
    SUBGOAL_THEN `&1 <= inv(norm(y:real^3))` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_KTW_TWIST_INV THEN
      ASM_SIMP_TAC[RFA_KTW_OUT_NZ]]]);;

let RFA_KTW_PHI_INJ = prove
 (`!rho y z:real^3.
     &1 <= rho /\ ~(y = vec 0) /\ ~(z = vec 0) /\ rfa_ktw_phi rho y = rfa_ktw_phi rho z
     ==> y = z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 <= norm(y:real^3) <=> &1 <= norm(z:real^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_KTW_PHI_NORM1]; ALL_TAC] THEN
  UNDISCH_TAC `rfa_ktw_phi rho y = rfa_ktw_phi rho (z:real^3)` THEN
  REWRITE_TAC[rfa_ktw_phi] THEN ASM_CASES_TAC `&1 <= norm(z:real^3)` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[RFA_KTW_OUT_INJ]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `rfs_twist:real^3->real^3`) THEN
  ASM_SIMP_TAC[RFA_KTW_TWIST_INV; RFA_KTW_OUT_NZ; P2ACM_TWIST_NZ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_KTW_OUT_INJ o CONJ (ASSUME `&1 <= rho`)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `rfs_twist:real^3->real^3`) THEN
  ASM_SIMP_TAC[RFA_KTW_TWIST_INV]);;

let RFA_KTW_PHI_DIL = prove
 (`!rho y:real^3. &2 <= norm y ==> rfa_ktw_phi rho y = rho % y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_phi] THEN
  SUBGOAL_THEN `&1 <= norm(y:real^3)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[RFA_KTW_OUT_DIL]]);;

(* p is twist invariant; p o phi through out. *)

let RFA_KTW_P_TWIST = prove
 (`!top atlas (g:real->B->real^3^3) p lam w.
     rfa_ktw_model (top,atlas) g p lam /\ ~(w = vec 0) ==> p (rfs_twist w) = p w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_ktw_model] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_twist")) (concl th)
    then MP_TAC(SPECL [`w:real^3`; `rfs_twist w:real^3`] th) else NO_TAC) THEN
  ASM_SIMP_TAC[P2ACM_TWIST_NZ]);;

let RFA_KTW_PP_OUT = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ &2 / &3 < norm y
     ==> p(rfa_ktw_phi rho y) = p(rfa_ktw_out rho y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_phi] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ norm(y:real^3) < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&2 / &3 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(rfs_twist y:real^3) <= &3 / &2 /\ norm(y:real^3) <= &3 / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_KTW_TWIST_NORM] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INV_LE_1; REAL_LE_INV2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 / &3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_KTW_OUT_ID; RFA_KTW_TWIST_INV]);;

let RFA_KTW_PP_IN = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ ~(y = vec 0) /\ norm y < &1
     ==> p(rfa_ktw_phi rho y) = p(rfa_ktw_out rho (rfs_twist y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_ktw_phi] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &1 ==> ~(&1 <= x)`] THEN
  MATCH_MP_TAC RFA_KTW_P_TWIST THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:real->B->real^3^3`; `lam:real`] THEN
  ASM_SIMP_TAC[RFA_KTW_OUT_NZ; P2ACM_TWIST_NZ]);;

(* Parametrization balls for p o out and p o phi. *)

let RFA_KTW_POUT_PARAM = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ ~(y = vec 0)
     ==> ?r. &0 < r /\ r < norm y /\
             mfd_param top atlas (ball(y,r)) (p o rfa_ktw_out rho)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(SPEC `rho:real` RFA_KTW_OUT_DIFFEO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `og:real^3->real^3`) THEN
  MATCH_MP_TAC P2ACM_PARAM_PRECOMP THEN
  MAP_EVERY EXISTS_TAC [`og:real^3->real^3`;
                        `norm(rfa_ktw_out rho (y:real^3)) / &2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(rfa_ktw_out rho (y:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; RFA_KTW_OUT_NZ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_KTW_PARAM_NEAR THEN
    MAP_EVERY EXISTS_TAC [`g:real->B->real^3^3`; `lam:real`] THEN
    ASM_SIMP_TAC[RFA_KTW_OUT_NZ]]);;

let RFA_KTW_PP_PARAM = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ ~(y = vec 0)
     ==> ?r. &0 < r /\ mfd_param top atlas (ball(y,r)) (p o rfa_ktw_phi rho)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&2 / &3 < norm(y:real^3)` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:real^3`]
                  RFA_KTW_POUT_PARAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r (norm(y:real^3) - &2 / &3)` THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_EQ THEN
    EXISTS_TAC `(p:real^3->B) o rfa_ktw_out rho` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN; o_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_KTW_PP_OUT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `g:real->B->real^3^3`; `lam:real`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`y:real^3`; `x:real^3`] NORM_TRIANGLE_SUB) THEN
      UNDISCH_TAC `dist(y:real^3,x) < norm(y:real^3) - &2 / &3` THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* inside: p o phi = (p o out) o twist near y *)
  SUBGOAL_THEN `~(rfs_twist y = vec 0:real^3) /\ norm(rfs_twist y) = inv(norm(y:real^3))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[P2ACM_TWIST_NZ; RFA_KTW_TWIST_NORM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`;
                 `rfs_twist y:real^3`] RFA_KTW_POUT_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(p:real^3->B) o rfa_ktw_out rho`; `rfs_twist:real^3->real^3`;
                 `rfs_twist:real^3->real^3`; `y:real^3`; `r:real`] P2ACM_PARAM_PRECOMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFA_KTW_TWIST_DIFFEO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r' (&1 - norm(y:real^3))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `((p:real^3->B) o rfa_ktw_out rho) o rfs_twist` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r')` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) < &1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`x:real^3`; `y:real^3`; `vec 0:real^3`] DIST_TRIANGLE) THEN
      REWRITE_TAC[DIST_0] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `dist(y:real^3,vec 0) < r'` THEN
      REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_KTW_PP_IN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `lam:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* p o phi is a twisted chart. *)

let RFA_KTW_TWISTED = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho
     ==> rfs_twisted_chart top atlas (p o rfa_ktw_phi rho)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_twisted_chart] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(p:real^3->B) (rfa_ktw_phi rho y) = p (rfa_ktw_phi rho z) <=>
      rfa_ktw_phi rho z = rfa_ktw_phi rho y \/
      rfa_ktw_phi rho z = rfs_twist(rfa_ktw_phi rho y)` SUBST1_TAC THENL
     [UNDISCH_TAC `rfa_ktw_model (top,atlas) (g:real->B->real^3^3) p lam` THEN
      REWRITE_TAC[rfa_ktw_model] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_twist")) (concl th))) THEN
      ASM_SIMP_TAC[RFA_KTW_PHI_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RFA_KTW_PHI_TWIST] THEN
    SUBGOAL_THEN `!w:real^3. ~(w = vec 0) ==> (rfa_ktw_phi rho z = rfa_ktw_phi rho w <=> z = w)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC RFA_KTW_PHI_INJ THEN EXISTS_TAC `rho:real` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN REFL_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2ACM_TWIST_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:real^3`]
                RFA_KTW_PP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r (min (norm(y:real^3) - &1 / &4) (&4 - norm y))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `x:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x:real^3`; `y:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x:real^3`; `y:real^3`] NORM_SUB) THEN
    UNDISCH_TAC `dist(y:real^3,x) < norm(y:real^3) - &1 / &4` THEN
    UNDISCH_TAC `dist(y:real^3,x) < &4 - norm(y:real^3)` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The sets of the twisted cap, with rho = e^a >= 2:                         *)
(* U = p(annulus(1/(2 rho^3), 2 rho^3)), core Y = p'(annulus(1/2,2)) with   *)
(* p' = p o phi, closed core p'(1/2 <= |y| <= 2) = p(1 <= |w| <= 2 rho),     *)
(* outer neck p o (2 rho^2 .) with image p(annulus(2 rho, 2 rho^3)) =         *)
(* U minus the closed core, inner neck p o (2 rho .) with central sphere     *)
(* p'(sphere 2) and p' y = e'(y/2) on annulus(2,4).                          *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_DIL_ANN = prove
 (`!c r1 r2. &0 < c
             ==> IMAGE (\w:real^3. c % w) (annulus r1 r2) = annulus (c * r1) (c * r2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    STRIP_TAC THEN EXISTS_TAC `inv c % x:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let RFA_KTW_DIL_SPHERE = prove
 (`!c r. &0 < c
         ==> IMAGE (\w:real^3. c % w) (sphere(vec 0,r)) = sphere(vec 0,c * r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`];
    STRIP_TAC THEN EXISTS_TAC `inv c % x:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]);;

(* A lift of norm >= 1 of p w, w nonzero. *)

let RFA_KTW_LIFT1 = prove
 (`!top atlas (g:real->B->real^3^3) p lam w.
     rfa_ktw_model (top,atlas) g p lam /\ ~(w = vec 0)
     ==> ?v. &1 <= norm v /\ p v = p w /\ (norm v = norm w \/ norm v = inv(norm w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= norm(w:real^3)` THENL
   [EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `rfs_twist w:real^3` THEN ASM_SIMP_TAC[RFA_KTW_TWIST_NORM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_KTW_P_TWIST THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `lam:real`] THEN ASM_REWRITE_TAC[]]);;

(* Points of symmetric shells have lifts of norm >= 1. *)

let RFA_KTW_SYM_SHELL = prove
 (`!top atlas (g:real->B->real^3^3) p lam R x.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= R
     ==> (x IN IMAGE p (annulus (inv R) R) <=>
          ?w. &1 <= norm w /\ norm w < R /\ p w = x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv R` THEN
      ASM_SIMP_TAC[REAL_LT_INV; REAL_ARITH `&1 <= R ==> &0 < R`];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `w:real^3`]
                  RFA_KTW_LIFT1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC))) THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_ARITH `&1 <= R ==> &0 < R`];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]);;

let RFA_KTW_H_MONO_LE = prove
 (`!rho r s. &1 <= rho /\ &0 <= r /\ r <= s ==> rfa_ktw_h rho r <= rfa_ktw_h rho s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:real = s` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC RFA_KTW_H_MONO THEN ASM_REAL_ARITH_TAC);;

(* p o phi through out: the two cases with norm bounds. *)

let RFA_KTW_PP_CASES = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ ~(y = vec 0)
     ==> ?v. (p o rfa_ktw_phi rho) y = p(rfa_ktw_out rho v) /\
             &1 <= norm v /\ (norm v = norm y \/ norm v = inv(norm y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= norm(y:real^3)` THENL
   [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[o_THM; rfa_ktw_phi]; ALL_TAC] THEN
  EXISTS_TAC `rfs_twist y:real^3` THEN ASM_SIMP_TAC[RFA_KTW_TWIST_NORM; o_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_KTW_PP_IN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `lam:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC]);;

let RFA_KTW_CORE_IMG = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho
     ==> IMAGE (p o rfa_ktw_phi rho) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
         IMAGE p {w:real^3 | &1 <= norm w /\ norm w <= &2 * rho}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:real^3`]
                  RFA_KTW_PP_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    EXISTS_TAC `rfa_ktw_out rho v:real^3` THEN ASM_SIMP_TAC[RFA_KTW_OUT_NORM] THEN
    SUBGOAL_THEN `norm(v:real^3) <= &2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`] RFA_KTW_H_VALUES) THEN
    MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`; `&2`] RFA_KTW_H_MONO_LE) THEN
    MP_TAC(SPECL [`rho:real`; `&2`] RFA_KTW_H_VALUES) THEN
    ASM_SIMP_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`rho:real`; `w:real^3`] RFA_KTW_OUT_ONTO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[o_THM; rfa_ktw_phi] THEN
    ASM_REAL_ARITH_TAC]);;

let RFA_KTW_U_DIFF = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho.
     rfa_ktw_model (top,atlas) g p lam /\ &2 <= rho
     ==> IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) DIFF
         IMAGE p {w:real^3 | &1 <= norm w /\ norm w <= &2 * rho} =
         IMAGE p (annulus (&2 * rho) (&2 * rho pow 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &2 * rho pow 3 /\ &0 < &2 * rho` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF] THEN X_GEN_TAC `x:B` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `&2 * rho pow 3`; `x:B`]
                RFA_KTW_SYM_SHELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; annulus] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `w:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0) /\ ~(v:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->B) w = p v` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `rfa_ktw_model (top,atlas) (g:real->B->real^3^3) p lam` THEN
    REWRITE_TAC[rfa_ktw_model] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_twist")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `v:real^3 = w` THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `v = rfs_twist (w:real^3)` THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&1 <= norm(rfs_twist (w:real^3))` THEN ASM_SIMP_TAC[RFA_KTW_TWIST_NORM] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]]);;

let RFA_KTW_DIL_IMG = prove
 (`!(p:real^3->B) c r1 r2.
     &0 < c ==> IMAGE (p o (\w. c % w)) (annulus r1 r2) = IMAGE p (annulus (c * r1) (c * r2))`,
  SIMP_TAC[IMAGE_o; RFA_KTW_DIL_ANN]);;

let RFA_KTW_SPHERES = prove
 (`!(p:real^3->B) rho.
     &0 < rho
     ==> IMAGE (p o (\w. (&2 * rho) % w)) (sphere(vec 0,&1)) =
         IMAGE (p o rfa_ktw_phi rho) (sphere(vec 0,&2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `IMAGE (rfa_ktw_phi rho) (sphere(vec 0,&2)) =
                IMAGE (\w:real^3. rho % w) (sphere(vec 0,&2))` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    SIMP_TAC[IN_SPHERE_0; RFA_KTW_PHI_DIL; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_KTW_DIL_SPHERE; REAL_ARITH `&0 < rho ==> &0 < &2 * rho`] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RFA_KTW_MATCH = prove
 (`!(p:real^3->B) rho y.
     y IN annulus (&2) (&4)
     ==> (p o rfa_ktw_phi rho) y =
         (p o (\w. (&2 * rho) % w)) (radial_ext (\x. x) (inv(&2) % y))`,
  REWRITE_TAC[annulus; IN_ELIM_THM; SMT_RADIAL_EXT_ID; o_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_KTW_PHI_DIL; REAL_LT_IMP_LE; VECTOR_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RFA_KTW_CHART_SUB = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho.
     rfa_ktw_model (top,atlas) g p lam /\ &2 <= rho
     ==> IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &4) (&4)) SUBSET
         IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &2 * rho pow 3 /\ &4 * rho <= &2 * rho pow 3` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 <= rho pow 2` MP_TAC THENL
     [SUBGOAL_THEN `(&2) pow 2 <= rho pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&8 <= rho * rho pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &4` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * rho <= rho pow 2 * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:real^3`]
                RFA_KTW_PP_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[GSYM annulus] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `&2 * rho pow 3`;
                 `(p:real^3->B)(rfa_ktw_out rho v)`] RFA_KTW_SYM_SHELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `rfa_ktw_out rho v:real^3` THEN
  SUBGOAL_THEN `norm(v:real^3) < &4` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_KTW_OUT_NORM; REAL_ARITH `&2 <= rho ==> &1 <= rho`] THEN
  MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`] RFA_KTW_H_VALUES) THEN
  MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`; `&4`] RFA_KTW_H_MONO) THEN
  MP_TAC(SPECL [`rho:real`; `&4`] RFA_KTW_H_VALUES) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&2 <= rho ==> &1 <= rho`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

(* The core Y: lifts below 2 rho, and every point with a lift in [1,rho]. *)

let RFA_KTW_CORE_LIFT = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho x.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\
     x IN IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &2) (&2))
     ==> ?w. &1 <= norm w /\ norm w < &2 * rho /\ p w = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:real^3`]
                RFA_KTW_PP_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `rfa_ktw_out rho v:real^3` THEN ASM_SIMP_TAC[RFA_KTW_OUT_NORM] THEN
  SUBGOAL_THEN `norm(v:real^3) < &2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`] RFA_KTW_H_VALUES) THEN
  MP_TAC(SPECL [`rho:real`; `norm(v:real^3)`; `&2`] RFA_KTW_H_MONO) THEN
  MP_TAC(SPECL [`rho:real`; `&2`] RFA_KTW_H_VALUES) THEN
  ASM_SIMP_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let RFA_KTW_CORE_MEM = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho w.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho /\ &1 <= norm w /\ norm w <= rho
     ==> p w IN IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &2) (&2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rho:real`; `w:real^3`] RFA_KTW_OUT_ONTO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM; o_THM] THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[rfa_ktw_phi] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`rho:real`; `y:real^3`] RFA_KTW_OUT_NORM) THEN
  MP_TAC(SPECL [`rho:real`; `&2`] RFA_KTW_H_VALUES) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The curvature clauses of the cap.  At time 0 the pullback                 *)
(* of g by p is lam cylinder_flow(0) on real^3 minus 0, so in each chart    *)
(* R = 1/lam is constant: grad R = 0, Lap R = 0 and abs(Ric)^2 = 1/(2 lam^2) *)
(* (P2C_PARAM_REP, P2C_CYL_MODEL); sups of constant functions.               *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_DERIVS = prove
 (`!top atlas (g:real->B->real^3^3) p lam x.
     rfa_ktw_model (top,atlas) g p lam /\ x IN topspace top
     ==> rfs_scalar_grad2 atlas (g(&0)) x = &0 /\ rfs_scalar_lap atlas (g(&0)) x = &0 /\
         rfs_ric_norm2 atlas (g(&0)) x = inv(&2 * lam pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2azq_model] o
    check (fun th -> is_comb(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2azq_model")) (concl th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `x:B`] RFA_KTW_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 <= norm(vec 0:real^3)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `ball(w:real^3,norm w / &2)`; `p:real^3->B`;
                 `w:real^3`] P2C_PARAM_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_KTW_PARAM_NEAR THEN
      MAP_EVERY EXISTS_TAC [`g:real->B->real^3^3`; `lam:real`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&1 <= norm(w:real^3)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN (:real^3) DELETE vec 0
               ==> rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) (&0)) z =
                   lam %% cylinder_flow (&0) z /\
                   lscalar (rfs_pullback atlas p (g(&0))) z = inv lam`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_KTW_LSCALAR_PB THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN (:real^3) DELETE vec 0 /\ open((:real^3) DELETE vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[IN_DELETE; IN_UNIV; OPEN_DELETE; OPEN_UNIV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lgrad2 (\z:real^3. lam %% cylinder_flow (&0) z) (\z. inv lam) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[lgrad2; FRECHET_DERIVATIVE_CONST_AT; VEC_COMPONENT; DROP_VEC;
                  REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `llap (\z:real^3. lam %% cylinder_flow (&0) z) (\z. inv lam) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[llap; FRECHET_DERIVATIVE_CONST_AT; VEC_COMPONENT; DROP_VEC;
                  REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; REAL_SUB_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 2 (\z:real^3. lam %% cylinder_flow (&0) z) (lric2 (cylinder_flow (&0))) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN X_GEN_TAC `u:num->real^3` THEN
    REWRITE_TAC[lric2] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lricci (\z:real^3. lam %% cylinder_flow (&0) z) w (u 1) (u 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LRICCI_SCALE THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01]];
    REWRITE_TAC[P2C_LTNORM2_METRIC_SCALE; ETA_AX] THEN ASM_SIMP_TAC[P2C_CYL_MODEL] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD]);;

(* Sups of constant functions; strict bounds of constant sets. *)

let RFA_KTW_SUP_CONST = prove
 (`!(f:B->real) S c. ~(S = {}) /\ (!x. x IN S ==> f x = c) ==> sup(IMAGE f S) = c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:B->real) S = {c}` (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
  ASM SET_TAC[]);;

let RFA_KTW_SUP_LT = prove
 (`!(S:real->bool) d c. (!x. x IN S ==> x <= d) /\ d < c ==> rfs_sup_lt S c`,
  REWRITE_TAC[rfs_sup_lt] THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The diameter of U = p(annulus(1/R,R)).  A segment inside a                *)
(* parametrization domain D of p has pushed length at most sqrt C times its  *)
(* length when lam 2/|y|^2 <= C on it (the argument of P2ACM_STD_SEG_BALL).  *)
(* Each point of U is joined in U to a point of the sphere |w| = 2 radially, *)
(* inside a coordinate half-space where p is a parametrization               *)
(* (P2ACM_STD_HALF_PARAM), and points of that sphere by model paths         *)
(* (APX_MODEL_PATH, P2AZQ_PUSH_LENGTH).                                      *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_SEG_DIST = prove
 (`!top atlas (g:real->B->real^3^3) p lam D K U z0 z Cq.
     rfa_ktw_model (top,atlas) g p lam /\ open D /\ (!y. y IN D ==> ~(y = vec 0)) /\
     mfd_param top atlas D p /\ segment[z0,z] SUBSET K /\ K SUBSET D /\
     IMAGE p K SUBSET U /\ (!y. y IN K ==> lam * &2 / norm y pow 2 <= Cq)
     ==> mfd_joinable_in (top,atlas) U (p z0) (p z) /\
         mfd_dist_in (top,atlas) (g(&0)) U (p z0) (p z) <= sqrt Cq * dist(z0,z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2azq_model] o
    check (fun th -> is_comb(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2azq_model")) (concl th))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `D:real^3->bool`; `\x:real^3. x`; `z0:real^3`; `z:real^3`]
                GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pt") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (K ALL_TAC))) THEN
  (let seg = `\t. chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + t % (z - z0))` in
   let cyl = `\y:real^3. lam %% cylinder_flow (&0) y` in
   MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `(g:real->B->real^3^3) (&0)`; `D:real^3->bool`; `p:real^3->B`; cyl; seg;
                  `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
     CONV_TAC SYM_CONV THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
       is_forall(concl th) && can (find_term (fun t -> is_const t &&
         fst(dest_const t) = "rfs_pullback")) (concl th) &&
       not (can (find_term (fun t -> is_var t && fst(dest_var t) = "t")) (concl th)))) THEN
     ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[rfs_pullback];
     ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1M") (LABEL_TAC "len")) THEN
   MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                  cyl; `D:real^3->bool`; `\x:real^3. x`; `z0:real^3`; `z:real^3`; `&0`;
                  `Cq:real`; `K:real^3->bool`] GRGD_SEGMENT_LENGTH_UPPER) THEN
   ANTS_TAC THENL
    [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
         ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01];
         ASM_SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV]];
       ALL_TAC] THEN
     MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN
     SUBGOAL_THEN `(y:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; P2ACM_CYL0_QF; DOT_SQUARE_NORM] THEN
     SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
      [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[REAL_MUL_LZERO] THEN
       REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
       ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; NORM_POS_LE; REAL_LT_IMP_LE; REAL_POS];
       SUBGOAL_THEN `lam * &2 / norm(y:real^3) pow 2 * norm(v:real^3) pow 2 =
                     (lam * &2 / norm y pow 2) * norm v pow 2` SUBST1_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `Cq:real`)) (concl th))) THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + &0 % (z - z0)) = z0 /\
                 chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + &1 % (z - z0)) = z`
   STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [USE_THEN "pt" (MP_TAC o SPEC `&0`);
       USE_THEN "pt" (MP_TAC o SPEC `&1`)] THEN
     REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN VECTOR_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                     ==> chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + t % (z - z0)) =
                         z0 + t % (z - z0) /\
                         (p:real^3->B) (z0 + t % (z - z0)) IN U` (LABEL_TAC "inU") THENL
    [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
     USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(z0:real^3) + t % (z - z0) IN segment[z0,z]` MP_TAC THENL
      [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
       UNDISCH_TAC `t IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
       SIMP_TAC[] THEN DISCH_TAC THEN VECTOR_ARITH_TAC;
       ASM SET_TAC[]];
     ALL_TAC] THEN
   SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                     ==> ((p:real^3->B) o
                          (\t. chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + t % (z - z0)))) t
                         IN U` ASSUME_TAC THENL
    [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
     USE_THEN "inU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[mfd_joinable_in] THEN
     EXISTS_TAC (mk_comb(mk_comb(`(o):(real^3->B)->(real->real^3)->real->B`, `p:real^3->B`), seg)) THEN
     ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
     SUBGOAL_THEN `t IN real_interval[&0,&1]` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
     USE_THEN "inU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `(g:real->B->real^3^3) (&0)`; `U:B->bool`;
                  mk_comb(mk_comb(`(o):(real^3->B)->(real->real^3)->real->B`, `p:real^3->B`), seg);
                  `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
   USE_THEN "len" SUBST1_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS]));;

let RFA_KTW_COORD = prove
 (`!w:real^3. ~(w = vec 0)
              ==> ?k s. 1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1)) /\ &0 < s * w$k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= 3 /\ ~((w:real^3)$k = &0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(w:real^3 = vec 0)` THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT; DIMINDEX_3] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `if &0 < (w:real^3)$k then &1 else --(&1)`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_KTW_HALF_OPEN = prove
 (`!b s k. (s = &1 \/ s = --(&1)) ==> open {z:real^3 | b < s * z$k}`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THENL
   [MP_TAC(ISPECL [`b:real`; `k:num`] (INST_TYPE [`:3`,`:N`] OPEN_HALFSPACE_COMPONENT_GT)) THEN
    REWRITE_TAC[real_gt];
    MP_TAC(ISPECL [`--b:real`; `k:num`] (INST_TYPE [`:3`,`:N`] OPEN_HALFSPACE_COMPONENT_LT)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

let RFA_KTW_SEG_RAY = prove
 (`!(w:real^3) c x. &0 < c /\ x IN segment[w,c % w]
                    ==> ?l. x = l % w /\ min (&1) c <= l /\ l <= max (&1) c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  EXISTS_TAC `(&1 - u) + u * c` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u * (c - &1) /\ u * (c - &1) <= c - &1 \/
                c - &1 <= u * (c - &1) /\ u * (c - &1) <= &0` MP_TAC THENL
   [ASM_CASES_TAC `&1 <= c` THENL
     [DISJ1_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC];
      DISJ2_TAC THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_ARITH `c - &1 <= u * (c - &1) <=> &0 <= (&1 - u) * (&1 - c)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_ARITH `u * (c - &1) <= &0 <=> &0 <= u * (&1 - c)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

let RFA_KTW_W_BOUND = prove
 (`!lam y:real^3. &0 < lam /\ &1 <= norm y ==> lam * &2 / norm y pow 2 <= &2 * lam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= norm(y:real^3) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 pow 2 <= norm(y:real^3) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_ONE]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `inv(norm(y:real^3) pow 2) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lam * &2 * inv(norm(y:real^3) pow 2) = (&2 * lam) * inv(norm y pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REAL_ARITH_TAC);;

let RFA_KTW_RAD_DIST = prove
 (`!top atlas (g:real->B->real^3^3) p lam R w.
     rfa_ktw_model (top,atlas) g p lam /\ &2 < R /\ &1 <= norm w /\ norm w < R
     ==> mfd_joinable_in (top,atlas) (IMAGE p (annulus (inv R) R))
           (p w) (p ((&2 / norm w) % w)) /\
         mfd_dist_in (top,atlas) (g(&0)) (IMAGE p (annulus (inv R) R))
           (p w) (p ((&2 / norm w) % w)) <= sqrt(&2 * lam) * R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0) /\ &0 < norm(w:real^3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `w:real^3` RFA_KTW_COORD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  ABBREV_TAC `c = &2 / norm(w:real^3)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = &4 * min (&1) c * (s * (w:real^3)$k)` THEN
  SUBGOAL_THEN `&0 < a /\ a / &8 < min (&1) c * (s * (w:real^3)$k)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SUBGOAL_THEN `&0 < min (&1) c * (s * (w:real^3)$k)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`;
                 `{z:real^3 | a / &8 < s * z$k}`; `segment[w:real^3,c % w]`;
                 `IMAGE (p:real^3->B) (annulus (inv R) R)`; `w:real^3`; `c % w:real^3`;
                 `&2 * lam`] RFA_KTW_SEG_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_KTW_HALF_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
      ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[VEC_COMPONENT; REAL_MUL_RZERO] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2ACM_STD_HALF_PARAM THEN
      MAP_EVERY EXISTS_TAC [`(g:real->B->real^3^3) (&0)`; `lam:real`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`w:real^3`; `c:real`; `x:real^3`] RFA_KTW_SEG_RAY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `min (&1) c * (s * (w:real^3)$k)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s * l * (w:real^3)$k = l * (s * w$k)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(SPECL [`w:real^3`; `c:real`; `x:real^3`] RFA_KTW_SEG_RAY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
      SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min (&1) c` THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
      SUBGOAL_THEN `c * norm(w:real^3) = &2` ASSUME_TAC THENL
       [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= l * norm(w:real^3) /\ l * norm w < R` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min (&1) c * norm(w:real^3)` THEN
          CONJ_TAC THENL
           [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `max (&1) c * norm(w:real^3)` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
            REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`w:real^3`; `c:real`; `x:real^3`] RFA_KTW_SEG_RAY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min (&1) c` THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `c * norm(w:real^3) = &2` ASSUME_TAC THENL
       [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min (&1) c * norm(w:real^3)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC RFA_KTW_W_BOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&2 * lam) * dist(w:real^3,c % w)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[SQRT_POS_LE] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `w - c % w:real^3 = (&1 - c) % w`; NORM_MUL] THEN
  SUBGOAL_THEN `abs(&1 - c) * norm(w:real^3) = abs(norm w - &2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `c * norm(w:real^3) = &2` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(w:real^3) - &2 = (&1 - c) * norm w` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM];
    ASM_REAL_ARITH_TAC]);;

let RFA_KTW_SPH_DIST = prove
 (`!top atlas (g:real->B->real^3^3) p lam R w1 w2.
     rfa_ktw_model (top,atlas) g p lam /\ &2 < R /\ norm w1 = &2 /\ norm w2 = &2
     ==> mfd_joinable_in (top,atlas) (IMAGE p (annulus (inv R) R)) (p w1) (p w2) /\
         mfd_dist_in (top,atlas) (g(&0)) (IMAGE p (annulus (inv R) R)) (p w1) (p w2)
         <= sqrt lam * sqrt(&2) * pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `~(w1:real^3 = vec 0) /\ ~(w2:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`annulus (&1) R:real^3->bool`; `w1:real^3`; `w2:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`;
                 `annulus (&1) R:real^3->bool`; `c0:real->real^3`; `&0`; `&1`]
                P2AZQ_PUSH_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS; REAL_LT_01] THEN CONJ_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `{y:real^3 | &1 < norm y}` THEN
      REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2AZQ_PARAM_OUT THEN
        MAP_EVERY EXISTS_TAC [`(g:real->B->real^3^3) (&0)`; `lam:real`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                    ==> ((p:real^3->B) o (c0:real->real^3)) t IN IMAGE p (annulus (inv R) R)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPECL [`subtopology euclidean (annulus (&1) R:real^3->bool)`;
                   `open_set_atlas (annulus (&1) R:real^3->bool)`; `c0:real->real^3`;
                   `&0`; `&1`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; annulus; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `(p:real^3->B) o (c0:real->real^3)` THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "annulus")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "o")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `IMAGE (p:real^3->B) (annulus (inv R) R)`;
                 `(p:real^3->B) o (c0:real->real^3)`; `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(apx_sval w1 - apx_sval w2) + sqrt(&2) * pi` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[apx_sval; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID; REAL_LE_REFL]);;

let RFA_KTW_DIAM = prove
 (`!top atlas (g:real->B->real^3^3) p lam R x1 x2.
     rfa_ktw_model (top,atlas) g p lam /\ &2 < R /\
     x1 IN IMAGE p (annulus (inv R) R) /\ x2 IN IMAGE p (annulus (inv R) R)
     ==> mfd_dist_in (top,atlas) (g(&0)) (IMAGE p (annulus (inv R) R)) x1 x2 <=
         sqrt lam * (&2 * sqrt(&2) * R + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `R:real`; `x1:B`]
                RFA_KTW_SYM_SHELL) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `R:real`; `x2:B`]
                RFA_KTW_SYM_SHELL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(p:real^3->B) w1 = x1`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(p:real^3->B) w2 = x2`)) THEN
  ABBREV_TAC `U = IMAGE (p:real^3->B) (annulus (inv R) R)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `R:real`; `w1:real^3`]
                RFA_KTW_RAD_DIST) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `R:real`; `w2:real^3`]
                RFA_KTW_RAD_DIST) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `R:real`;
                 `(&2 / norm(w1:real^3)) % w1`; `(&2 / norm(w2:real^3)) % w2`]
                RFA_KTW_SPH_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm((&2 / norm(w1:real^3)) % w1) = &2 /\ norm((&2 / norm(w2:real^3)) % w2) = &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NORM] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[NORM_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v1 = (p:real^3->B) ((&2 / norm(w1:real^3)) % w1)` THEN
  ABBREV_TAC `v2 = (p:real^3->B) ((&2 / norm(w2:real^3)) % w2)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas:((B->bool)#(B->real^3))->bool) U v2 ((p:real^3->B) w2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas:((B->bool)#(B->real^3))->bool) U v1 ((p:real^3->B) w2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `(p:real^3->B) w1`; `v1:B`;
                 `(p:real^3->B) w2`] MFD_DIST_IN_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `v1:B`; `v2:B`;
                 `(p:real^3->B) w2`] MFD_DIST_IN_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `v2:B`; `(p:real^3->B) w2`]
                MFD_DIST_IN_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&2 * lam) = sqrt(&2) * sqrt lam` SUBST_ALL_TAC THENL
   [REWRITE_TAC[SQRT_MUL]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Images under p of open sets are open; the volume of the                   *)
(* shell image p(annulus(e^-K, e^K)) is at most 6 (2K + 1) boxes of the      *)
(* model (P2ACM_SHELL_IN_BOXES, P2ACM_STD_BOX_VOL, P2ACM_VOL_UNIONS_LE; the   *)
(* counting of P2ACM_STD_BALL_UPPER).                                         *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_IMAGE_OPEN = prove
 (`!top atlas (g:real->B->real^3^3) p lam s.
     rfa_ktw_model (top,atlas) g p lam /\ open s /\ (!y. y IN s ==> ~(y = vec 0))
     ==> open_in top (IMAGE p s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (p:real^3->B) (s INTER ball(y,norm y / &2))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `ball(y:real^3,norm y / &2)`] THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
    MATCH_MP_TAC RFA_KTW_PARAM_NEAR THEN
    MAP_EVERY EXISTS_TAC [`g:real->B->real^3^3`; `lam:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

let RFA_KTW_SHELL_VOL = prove
 (`!top atlas (g:real->B->real^3^3) p lam K.
     rfa_ktw_model (top,atlas) g p lam /\ &0 <= K
     ==> ?v. mfd_has_volume (top,atlas) (g(&0)) (IMAGE p (annulus (exp(--K)) (exp K))) v /\
             v <= &6 * (&2 * K + &1) * (&31104 * pi * lam * sqrt(&32 * lam))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  ABBREV_TAC `C1 = &31104 * pi * lam * sqrt(&32 * lam)` THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LT_IMP_LE; SQRT_POS_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * K` FLOOR_POS) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `&N <= &2 * K /\ &2 * K < &N + &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&2 * K` FLOOR) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Ix = {n:num | n <= N} CROSS ({1,2,3} CROSS {&1,--(&1)})` THEN
  ABBREV_TAC `box = \i:num#num#real. IMAGE (p:real^3->B)
                      (p2acm_box (exp(--K) * exp(&(FST i))) (FST(SND i)) (SND(SND i)))` THEN
  SUBGOAL_THEN `FINITE(Ix:num#num#real->bool) /\ CARD Ix = (N + 1) * 3 * 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ix" THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LE; FINITE_INSERT; FINITE_EMPTY; CARD_CROSS;
             CARD_NUMSEG_LE; CARD_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num#num#real. i IN Ix
                    ==> 1 <= FST(SND i) /\ FST(SND i) <= 3 /\
                        (SND(SND i) = &1 \/ SND(SND i) = --(&1)) /\ FST i <= N`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ix" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_INSERT;
                                    NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num#num#real. i IN Ix
                    ==> ?w. mfd_has_volume (top,atlas) ((g:real->B->real^3^3) (&0))
                              ((box:num#num#real->B->bool) i) w /\ w <= C1`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN EXPAND_TAC "box" THEN EXPAND_TAC "C1" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC P2ACM_STD_BOX_VOL THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `IMAGE (box:num#num#real->B->bool) Ix`]
                P2ACM_VOL_UNIONS_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sum (IMAGE (box:num#num#real->B->bool) Ix)
                    (\K. mfd_volume (top,atlas:((B->bool)#(B->real^3))->bool)
                                    ((g:real->B->real^3^3) (&0)) K)
                <= &((N + 1) * 3 * 2) * C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (Ix:num#num#real->bool)
                  ((\K. mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0)) K) o box)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_IMAGE_LE THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num#num#real` o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[MFD_HAS_VOLUME_VOLUME; MFD_HAS_VOLUME_POS_LE];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `CARD(Ix:num#num#real->bool) = (N + 1) * 3 * 2`)) THEN
      ASM_SIMP_TAC[GSYM SUM_CONST] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num#num#real` o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[MFD_HAS_VOLUME_VOLUME]];
    ALL_TAC] THEN
  (* the shell image lies in the union of the boxes *)
  SUBGOAL_THEN `IMAGE (p:real^3->B) (annulus (exp(--K)) (exp K)) SUBSET
                UNIONS (IMAGE (box:num#num#real->B->bool) Ix)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`K:real`; `N:num`; `w:real^3`] P2ACM_SHELL_IN_BOXES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `(n:num,k:num,s:real)` THEN CONJ_TAC THENL
     [EXPAND_TAC "Ix" THEN REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 <= k` THEN UNDISCH_TAC `k <= 3` THEN ARITH_TAC;
      EXPAND_TAC "box" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `IMAGE (p:real^3->B) (annulus (exp(--K)) (exp K))`;
                 `UNIONS (IMAGE (box:num#num#real->B->bool) Ix)`; `u:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_KTW_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `lam:real`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
    MP_TAC(SPEC `--K` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0))
                (IMAGE (p:real^3->B) (annulus (exp(--K)) (exp K)))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&((N + 1) * 3 * 2) * C1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `(&N + &1) * &3 * &2 = &6 * (&N + &1)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The ball clause (7) of the cap.  p is continuous on real^3                *)
(* minus 0 (pasting the local parametrizations), so p of a closed shell is  *)
(* compact.  A ball of radius sqrt lam about a core point stays in the       *)
(* shell inv(2 e rho) <= |w| <= 2 e rho (height bound P2ACM_STD_CURVE_LOWER), *)
(* so its closure is compact and inside U; its volume is at least            *)
(* lam^(3/2)/40 (P2ACM_STD_UNIT_BALL for the rescaled metric inv lam g,      *)
(* MFD_BALL_SCALE, MFD_HAS_VOLUME_SCALE).                                    *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_P_CONT = prove
 (`!top atlas (g:real->B->real^3^3) p lam.
     rfa_ktw_model (top,atlas) g p lam
     ==> continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},top) p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(y = vec 0)}`; `top:B topology`;
                       `(\i:real^3. p):real^3->real^3->B`; `p:real^3->B`;
                       `\i:real^3. ball(i,norm i / &2)`; `{y:real^3 | ~(y = vec 0)}`]
                      PASTING_LEMMA) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ball(i:real^3,norm i / &2) SUBSET {y:real^3 | ~(y = vec 0)}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`i:real^3`; `z:real^3`] RFA_KTW_BALL_NZ) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `{y:real^3 | ~(y = vec 0)} INTER ball(i,norm i / &2) = ball(i,norm i / &2)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `i:real^3`]
                  RFA_KTW_PARAM_NEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN REAL_ARITH_TAC]);;

let RFA_KTW_SHELL_COMPACT = prove
 (`!top atlas (g:real->B->real^3^3) p lam r1 r2.
     rfa_ktw_model (top,atlas) g p lam /\ &0 < r1
     ==> compact_in top (IMAGE p {w:real^3 | r1 <= norm w /\ norm w <= r2})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean {y:real^3 | ~(y = vec 0)}` THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `{w:real^3 | r1 <= norm w /\ norm w <= r2} =
                    cball(vec 0,r2) DIFF ball(vec 0,r1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        GEN_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]];
    MATCH_MP_TAC RFA_KTW_P_CONT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `lam:real`] THEN
    ASM_REWRITE_TAC[]]);;

let RFA_KTW_E_LE3 = prove
 (`exp(&1) <= &3`,
  MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* A ball of radius sqrt lam about p w0, 1 <= |w0| < 2 rho, lies in the     *)
(* image of the closed shell inv(2 e rho) <= |w| <= 2 e rho.                 *)

let RFA_KTW_BALL_IN = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho w0 m.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= norm w0 /\ norm w0 < &2 * rho /\
     m IN mfd_ball (top,atlas) (g(&0)) (p w0) (sqrt lam)
     ==> m IN IMAGE p {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                   norm w <= &2 * rho * exp(&1)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `~(w0:real^3 = vec 0) /\ &0 < rho` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `(p:real^3->B) w0`; `sqrt lam`]
                  MFD_BALL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:real^3->B`; `lam:real`; `m:B`]
                P2ACM_STD_PREIM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = @z:real^3. ~(z = vec 0) /\ (p:real^3->B) z = m` THEN STRIP_TAC THEN
  UNDISCH_TAC `(m:B) IN mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                 ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) (sqrt lam)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt lam * abs(abs(apx_sval w) - abs(apx_sval w0)) <=
                mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) (p w0) m` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `gam:real->B` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2ACM_STD_CURVE_LOWER THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `p:real^3->B`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(abs(apx_sval w) - abs(apx_sval w0)) < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt lam * abs(abs(apx_sval w) - abs(apx_sval w0)) < sqrt lam * &1` MP_TAC
    THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(norm(w0:real^3)) /\ log(norm(w0:real^3)) < log(&2 * rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval w) = sqrt(&2) * abs(log(norm(w:real^3))) /\
                abs(apx_sval w0) = sqrt(&2) * log(norm(w0:real^3))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_sval; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(w:real^3))) < log(&2 * rho) + &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_CASES_TAC `abs(log(norm(w:real^3))) - log(norm(w0:real^3)) <= &0` THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 * (abs(log(norm(w:real^3))) - log(norm(w0:real^3))) <=
                  sqrt(&2) * (abs(log(norm w)) - log(norm w0))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    UNDISCH_TAC `abs(abs(apx_sval w) - abs(apx_sval w0)) < &1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * rho * exp(&1) = exp(log(&2 * rho) + &1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_ADD] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < rho ==> &0 < &2 * rho`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^3) = exp(log(norm w))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

(* Clause (7) at a core point y: only r = sqrt lam has sup R = inv(r^2).     *)

let RFA_KTW_BALL_CLAUSE = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho y r.
     rfa_ktw_model (top,atlas) g p lam /\ &2 <= rho /\
     y IN IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &2) (&2)) /\ &0 < r /\
     sup(IMAGE (mfd_scalar atlas (g(&0))) (mfd_ball (top,atlas) (g(&0)) y r)) = inv(r pow 2)
     ==> compact_in top (top closure_of mfd_ball (top,atlas) (g(&0)) y r) /\
         top closure_of mfd_ball (top,atlas) (g(&0)) y r SUBSET
           IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) /\
         ?v. mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) y r) v /\
             &1 / &40 <= v / r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`; `y:B`]
                RFA_KTW_CORE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `~(w0:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) w0 IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p2acm_std (top,atlas) ((g:real->B->real^3^3) (&0)) p lam` THEN
    REWRITE_TAC[p2acm_std] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) r
                      ==> z IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `(p:real^3->B) w0`; `r:real`] MFD_BALL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r = sqrt lam` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `sup(IMAGE (mfd_scalar atlas ((g:real->B->real^3^3) (&0)))
                     (mfd_ball (top,atlas) (g(&0)) ((p:real^3->B) w0) r)) = inv lam` MP_TAC THENL
     [MATCH_MP_TAC RFA_KTW_SUP_CONST THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(p:real^3->B) w0` THEN
        ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
        X_GEN_TAC `z:B` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_KTW_SCALAR THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `p:real^3->B`] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_EQ_INV2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&1) /\ exp(&1) <= &3` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; RFA_KTW_E_LE3]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * rho * exp(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) (sqrt lam) SUBSET
    IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                    norm w <= &2 * rho * exp(&1)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `m:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_KTW_BALL_IN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `lam:real`; `w0:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top (IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                                    norm w <= &2 * rho * exp(&1)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_KTW_SHELL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `lam:real`] THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                    norm w <= &2 * rho * exp(&1)} SUBSET
    IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN
    SUBGOAL_THEN `&2 * rho * exp(&1) < &2 * rho pow 3` ASSUME_TAC THENL
     [SUBGOAL_THEN `exp(&1) < rho pow 2` ASSUME_TAC THENL
       [SUBGOAL_THEN `(&2) pow 2 <= rho pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * rho pow 3) < inv(&2 * rho * exp(&1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) (sqrt lam) SUBSET
    IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                    norm w <= &2 * rho * exp(&1)}` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                                norm w <= &2 * rho * exp(&1)}` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                                norm w <= &2 * rho * exp(&1)}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the volume of the ball *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`;
                 `IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                                  norm w <= &2 * rho * exp(&1)}`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vs:real`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) (sqrt lam)`;
                 `IMAGE (p:real^3->B) {w:real^3 | inv(&2 * rho * exp(&1)) <= norm w /\
                                                  norm w <= &2 * rho * exp(&1)}`;
                 `vs:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0))
                (mfd_ball (top,atlas) (g(&0)) ((p:real^3->B) w0) (sqrt lam))` THEN
  ASM_REWRITE_TAC[] THEN
  (* rescaling by inv lam *)
  SUBGOAL_THEN `&0 < inv lam` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. inv lam %% (g:real->B->real^3^3) (&0) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `p2acm_std (top,atlas) (\z. inv lam %% (g:real->B->real^3^3) (&0) z) p (&1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2acm_std (top,atlas) ((g:real->B->real^3^3) (&0)) p lam` THEN
    REWRITE_TAC[p2acm_std] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_LT_01; P2B9_RFS_PULLBACK_CMUL; ETA_AX] THEN
    ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (\z. inv lam %% (g:real->B->real^3^3) (&0) z) ((p:real^3->B) w0) (&1) =
                mfd_ball (top,atlas) (g(&0)) ((p:real^3->B) w0) (sqrt lam)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `inv lam`; `(p:real^3->B) w0`; `&1`]
                  MFD_BALL_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    AP_TERM_TAC THEN REWRITE_TAC[SQRT_INV; real_div; REAL_INV_INV; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\z. inv lam %% (g:real->B->real^3^3) (&0) z`; `p:real^3->B`; `&1`;
                 `(p:real^3->B) w0`;
                 `sqrt(inv lam pow 3) * mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0))
                     (mfd_ball (top,atlas) (g(&0)) ((p:real^3->B) w0) (sqrt lam))`]
                P2ACM_STD_UNIT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) ((p:real^3->B) w0) (sqrt lam)`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0))
                      (mfd_ball (top,atlas) (g(&0)) ((p:real^3->B) w0) (sqrt lam))`;
                   `inv lam`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(inv lam pow 3) = inv(sqrt lam pow 3)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; SQRT_INV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; REAL_POW_ADD; REAL_POW_1; SQRT_MUL] THEN
    ASM_SIMP_TAC[POW_2_SQRT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_MUL_SYM]);;


(* ------------------------------------------------------------------------- *)
(* The twisted cap.  U = p(annulus(1/(2 rho^3), 2 rho^3)),                   *)
(* Y = p'(annulus(1/2,2)) with p' = p o phi, the outer neck p o (2 rho^2 .), *)
(* the inner neck p o (2 rho .), f = identity; R = 1/lam on U; all clauses  *)
(* of rfs_cap with C >= 6 rho^3 + 27000000 (1 + log rho).                    *)
(* ------------------------------------------------------------------------- *)

let RFA_KTW_NUM_BOUNDS = prove
 (`sqrt(&2) < &3 / &2 /\ pi < &4 /\ sqrt(&32) < &6 /\ log(&2) <= &1`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MP_TAC(SPEC `&1` LOG_LE_STRONG) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

(* U lies in the manifold; R = 1/lam on U and sup R = 1/lam. *)

let RFA_KTW_U_SCALAR = prove
 (`!top atlas (g:real->B->real^3^3) p lam R.
     rfa_ktw_model (top,atlas) g p lam /\ &1 < R
     ==> IMAGE p (annulus (inv R) R) SUBSET topspace top /\
         (!y. y IN IMAGE p (annulus (inv R) R) ==> mfd_scalar atlas (g(&0)) y = inv lam) /\
         sup(IMAGE (mfd_scalar atlas (g(&0))) (IMAGE p (annulus (inv R) R))) = inv lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (p:real^3->B) (annulus (inv R) R) SUBSET topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_ktw_model (top,atlas) (g:real->B->real^3^3) p lam` THEN
    REWRITE_TAC[rfa_ktw_model] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `topspace (top:B topology)`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN
    MP_TAC(SPEC `R:real` REAL_LT_INV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:B. y IN IMAGE (p:real^3->B) (annulus (inv R) R)
                      ==> mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y = inv lam`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_KTW_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `p:real^3->B`] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_KTW_SUP_CONST THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(p:real^3->B) (basis 1)` THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* The twisted alternative of rfs_cap. *)

let RFA_KTW_CAP_TWISTED = prove
 (`!top atlas (g:real->B->real^3^3) p lam eps rho.
     rfa_ktw_model (top,atlas) g p lam /\ &0 < eps /\
     exp(inv(sqrt(&2) * eps)) = rho /\ &2 <= rho
     ==> ?p' e e' z z' f f'.
           rfs_twisted_chart top atlas p' /\
           IMAGE p' (annulus (&1 / &4) (&4)) SUBSET
             IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) /\
           IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &2) (&2)) =
             IMAGE p' (annulus (&1 / &2) (&2)) /\
           rfs_neck (top,atlas) (g(&0)) eps z e /\
           IMAGE e (rfs_neck_dom eps) =
             IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) DIFF
             IMAGE p' {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
           rfs_neck (top,atlas) (g(&0)) eps z' e' /\
           IMAGE e' (rfs_neck_dom eps) SUBSET
             IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) /\
           IMAGE e' (sphere(vec 0,&1)) = IMAGE p' (sphere(vec 0,&2)) /\
           sphere_diffeo f f' /\
           (!y. y IN annulus (&2) (&4) ==> p' y = e'(radial_ext f (inv(&2) % y)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `&1 <= rho /\ &0 < rho` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (inv rho) rho` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; REAL_EXP_NEG] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis 1:real^3) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `rho < &2 * rho pow 2 /\ rho < &2 * rho` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `rho <= rho pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(p:real^3->B) o rfa_ktw_phi rho`;
    `(p:real^3->B) o (\w:real^3. (&2 * rho pow 2) % w)`;
    `(p:real^3->B) o (\w:real^3. (&2 * rho) % w)`;
    `(p:real^3->B) ((&2 * rho pow 2) % basis 1)`;
    `(p:real^3->B) ((&2 * rho) % basis 1)`;
    `\x:real^3. x`; `\x:real^3. x`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_KTW_TWISTED THEN
    MAP_EVERY EXISTS_TAC [`g:real->B->real^3^3`; `lam:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_KTW_CHART_SUB THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `lam:real`] THEN
    ASM_REWRITE_TAC[];
    REFL_TAC;
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `eps:real`;
                   `&2 * rho pow 2`; `basis 1:real^3`; `&1`] RFA_KTW_FAR_NECK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)];
    ASM_SIMP_TAC[RFA_KTW_DIL_IMG; REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`]
                  RFA_KTW_CORE_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`]
                  RFA_KTW_U_DIFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(&2 * rho pow 2) * inv rho = &2 * rho /\
                  (&2 * rho pow 2) * rho = &2 * rho pow 3` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `eps:real`;
                   `&2 * rho`; `basis 1:real^3`; `&1`] RFA_KTW_FAR_NECK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)];
    ASM_SIMP_TAC[RFA_KTW_DIL_IMG; REAL_ARITH `&0 < rho ==> &0 < &2 * rho`] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    SUBGOAL_THEN `(&2 * rho) * inv rho = &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * rho pow 3) <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * rho) * rho <= &2 * rho pow 3` ASSUME_TAC THENL
     [SUBGOAL_THEN `rho pow 2 <= rho pow 3` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_KTW_SPHERES THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SMT_SPHERE_DIFFEO_ID];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_KTW_MATCH THEN
    ASM_REWRITE_TAC[]]);;

(* The diameter clause. *)

let RFA_KTW_CAP_DIAM = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho C.
     rfa_ktw_model (top,atlas) g p lam /\ &2 <= rho /\ &6 * rho pow 3 + &6 <= C
     ==> rfs_sup_lt {mfd_dist_in (top,atlas) (g(&0))
                       (IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))) y1 y2 |
                     y1,y2 | y1 IN IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)) /\
                             y2 IN IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))}
                    (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g(&0)))
                                (IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `&16 <= &2 * rho pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&2) pow 3 <= rho pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `&2 * rho pow 3`]
                RFA_KTW_U_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[SQRT_INV; REAL_INV_INV] THEN
  MATCH_MP_TAC RFA_KTW_SUP_LT THEN
  EXISTS_TAC `sqrt lam * (&2 * sqrt(&2) * (&2 * rho pow 3) + sqrt(&2) * pi)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_KTW_DIAM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam /\ &0 < rho pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_POW_LT; REAL_ARITH `&2 <= rho ==> &0 < rho`]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * rho pow 3 < &3 / &2 * rho pow 3 /\ sqrt(&2) * pi < &3 / &2 * &4`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[RFA_KTW_NUM_BOUNDS];
      MATCH_MP_TAC REAL_LT_MUL2 THEN
      SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE; RFA_KTW_NUM_BOUNDS]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The volume of U in the form (3 + 6 log rho) 4478976 lam^(3/2). *)

let RFA_KTW_U_VOL = prove
 (`!top atlas (g:real->B->real^3^3) p lam rho.
     rfa_ktw_model (top,atlas) g p lam /\ &1 <= rho
     ==> ?v. mfd_has_volume (top,atlas) (g(&0))
               (IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))) v /\
             v <= (&3 + &6 * log rho) * &4478976 * sqrt lam pow 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `&0 < rho /\ &1 <= &2 * rho pow 3 /\ &0 < &2 * rho pow 3` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= rho pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `log(&2 * rho pow 3)`]
                RFA_KTW_SHELL_VOL) THEN
  ASM_SIMP_TAC[LOG_POS; REAL_EXP_NEG; EXP_LOG] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&6 * (&2 * log(&2 * rho pow 3) + &1) * (&31104 * pi * lam * sqrt(&32 * lam))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log(&2 * rho pow 3) = log(&2) + &3 * log rho` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `lam * sqrt(&32 * lam) = sqrt(&32) * sqrt lam pow 3` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `lam = sqrt lam pow 2`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log rho /\ &0 <= log(&2) /\ log(&2) <= &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RFA_KTW_NUM_BOUNDS] THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pi * sqrt(&32) /\ pi * sqrt(&32) <= &24` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; SQRT_POS_LE; REAL_POS];
      SUBGOAL_THEN `&24 = &4 * &6` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PI_POS_LE] THEN
      SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN MP_TAC RFA_KTW_NUM_BOUNDS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (log(&2) + &3 * log rho) + &1) * (pi * sqrt(&32)) <=
                (&3 + &6 * log rho) * &24` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&6 * x * (&31104 * pi * (q * s)) =
                          (&186624 * s) * (x * (pi * q))`;
              REAL_ARITH `(a + b) * &4478976 * s = (&186624 * s) * ((a + b) * &24)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* The cap. *)

let RFA_KTW_CAP = prove
 (`!top atlas (g:real->B->real^3^3) p lam eps rho C.
     rfa_ktw_model (top,atlas) g p lam /\ &0 < eps /\
     exp(inv(sqrt(&2) * eps)) = rho /\ &2 <= rho /\
     &6 * rho pow 3 + &27000000 * (&1 + log rho) <= C
     ==> rfs_cap (top,atlas) (g(&0)) C eps
           (IMAGE p (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3)))
           (IMAGE (p o rfa_ktw_phi rho) (annulus (&1 / &2) (&2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_KTW_G0) THEN
  SUBGOAL_THEN `&0 < rho /\ &1 <= rho /\ &0 <= log rho /\ &1 <= rho pow 3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &2 * rho pow 3 /\ &0 < inv(&2 * rho pow 3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&40 < C /\ &1 < C /\ &6 * rho pow 3 + &6 <= C /\
                (&3 + &6 * log rho) * &4478976 < C` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `&2 * rho pow 3`]
                RFA_KTW_U_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[rfs_cap] THEN REPEAT CONJ_TAC THENL
   [(* smooth *)
    ASM_REWRITE_TAC[];
    (* U open *)
    MATCH_MP_TAC RFA_KTW_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `lam:real`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
    (* the twisted alternative *)
    DISJ2_TAC THEN MATCH_MP_TAC RFA_KTW_CAP_TWISTED THEN EXISTS_TAC `lam:real` THEN
    ASM_REWRITE_TAC[];
    (* R > 0 on U *)
    ASM_SIMP_TAC[REAL_LT_INV];
    (* diameter *)
    MATCH_MP_TAC RFA_KTW_CAP_DIAM THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
    (* curvature ratio *)
    MATCH_MP_TAC RFA_KTW_SUP_LT THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_LE_REFL];
    (* volume *)
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `rho:real`]
                  RFA_KTW_U_VOL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[SQRT_INV; REAL_POW_INV; REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&3 + &6 * log rho) * &4478976 * sqrt lam pow 3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT];
    (* the ball clause *)
    EXISTS_TAC `&1 / &40` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RFA_KTW_BALL_CLAUSE THEN
      EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]];
    (* grad R *)
    MATCH_MP_TAC RFA_KTW_SUP_LT THEN EXISTS_TAC `&0` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `y:B`]
                  RFA_KTW_DERIVS) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
    SIMP_TAC[SQRT_0; real_div; REAL_MUL_LZERO; REAL_LE_REFL];
    (* Lap R and abs(Ric)^2 *)
    MATCH_MP_TAC RFA_KTW_SUP_LT THEN EXISTS_TAC `&1` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `y:B`]
                  RFA_KTW_DERIVS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&0 + &2 * inv(&2 * lam pow 2) = inv lam pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv lam pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_REFL; REAL_LT_IMP_NZ;
                 REAL_LE_REFL]]);;


(* ------------------------------------------------------------------------- *)
(* The headline.  eps2 = 1/4, so a = 1/(sqrt 2 eps) >= 1 and                 *)
(* rho = e^a >= 2; C0 = 6 rho^3 + 27000000 (1 + a).  A point x = p w with   *)
(* |w| >= 1 is the centre of the exact evolving neck p o (|w| .) when        *)
(* |w| > rho (RFA_KTW_FAR_NECK), and lies in the core of the twisted cap     *)
(* otherwise (RFA_KTW_CAP, RFA_KTW_CORE_MEM).                                *)
(* ------------------------------------------------------------------------- *)

let RFA_P2B_KNCL_TWISTED_CANON = prove
 (`!w:B->bool. P2B_KNCL_TWISTED_CANON_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_KNCL_TWISTED_CANON_STATEMENT] THEN
  EXISTS_TAC `&1 / &4` THEN CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      SUBGOAL_THEN `sqrt(&2) * eps <= sqrt(&2) * (&1 / &4)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS]; ALL_TAC] THEN
      MP_TAC RFA_KTW_NUM_BOUNDS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = exp(inv(sqrt(&2) * eps))` THEN
  SUBGOAL_THEN `log rho = inv(sqrt(&2) * eps) /\ &2 <= rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[LOG_EXP] THEN
    MP_TAC(SPEC `inv(sqrt(&2) * eps)` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&6 * rho pow 3 + &27000000 * (&1 + log rho)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= rho pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `x:B`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfa_ktw_model (top,atlas) (g:real->B->real^3^3) p lam` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfa_ktw_model]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `x:B`] RFA_KTW_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(p:real^3->B) w = x`)) THEN
  REWRITE_TAC[p2b_canon_L] THEN
  ASM_CASES_TAC `rho < norm(w:real^3)` THENL
   [(* far points: an exact evolving neck *)
    DISJ1_TAC THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(w:real^3) % (inv(norm w) % w) = w /\ norm(inv(norm w) % w) = &1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`; `eps:real`;
                   `norm(w:real^3)`; `inv(norm(w:real^3)) % w`; `L:real`] RFA_KTW_FAR_NECK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN MESON_TAC[]];
    (* core points: the twisted cap *)
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (p:real^3->B) (annulus (inv(&2 * rho pow 3)) (&2 * rho pow 3))`;
      `IMAGE ((p:real^3->B) o rfa_ktw_phi rho) (annulus (&1 / &2) (&2))`] THEN
    REWRITE_TAC[RFA_KTW_KVIEW; REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_KTW_CAP THEN EXISTS_TAC `lam:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC RFA_KTW_CORE_MEM THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `g:real->B->real^3^3`; `lam:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

