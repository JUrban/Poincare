(* ========================================================================= *)
(* Unit pc_p2b_kncapc: the constant clauses of the soul cap in piece (d) of  *)
(* the statements of pc_p2b_c994req (MT Cor 9.94 in the length-L form), case *)
(* P: the statement P2B_KNCL_CAPC_STATEMENT of pc_p2b_kncapcreq.  Main       *)
(* theorem P2BCC_KNCL_CAPC.  Notation: rho = R(p)^(-1/2),                    *)
(* B = mfd_ball p (Dst rho), R3 = R(z3), h3 = R3^(-1/2), eps0 = eps/K1.      *)
(*                                                                           *)
(* Sections: the hypotheses as one predicate and the scalar curvature bounds *)
(* on U (pinching on B, the factor 2 on the neck e3, e3 w0 in B); the        *)
(* intrinsic diameter (short curves from p stay in B; model paths in the     *)
(* slab of e3); the volume (Bishop-Gromov on a ball around p); clause 7 with *)
(* d = kappa0 (closure in U by the width hypothesis; volume by               *)
(* kappa0-noncollapsing with abs(Rm) <= R(0)/2 from the Harnack bound); the  *)
(* derivative clauses, the constant and the main theorem.                    *)
(* ========================================================================= *)

needs "src/pc_p2b_kncapcreq.ml";;
needs "src/pc_p2b_ksolcyl.ml";;
needs "src/pc_p2a_l965.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_grg_dist_in.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2b_slice.ml";;
needs "src/pc_rf_unique_a14.ml";;
needs "src/pc_rfs_sanity.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_apx_engine.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* The hypotheses as one predicate (the text of the statement), the slab of  *)
(* e3 inside its neck domain, basic facts and the scalar curvature bounds.   *)
(* ------------------------------------------------------------------------- *)

let p2bcc_hyp = new_definition
 `p2bcc_hyp (eps:real) (K1:real) (Dst:real) (D1:real) (kappa0:real) (C71:real)
            (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
            (p:B) (U:B->bool) (Y:B->bool) (z3:B) (e3:real^3->B) (w0:real^3) <=>
    &0 < eps /\ eps <= &1 / &100 /\ &4 <= K1 /\ &0 < Dst /\ &1 < D1 /\
    &0 < kappa0 /\ &0 < C71 /\
    p2b_kappa_solution kappa0 (top,atlas) g /\ ~compact_space top /\
    (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
             ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
    (!x. x IN topspace top
         ==> sqrt(rfs_scalar_grad2 atlas (g(&0)) x) <=
             C71 * mfd_scalar atlas (g(&0)) x * sqrt(mfd_scalar atlas (g(&0)) x) /\
             abs(rfs_scalar_lap atlas (g(&0)) x +
                 &2 * rfs_ric_norm2 atlas (g(&0)) x) <=
             C71 * mfd_scalar atlas (g(&0)) x pow 2) /\
    p IN topspace top /\ &0 < mfd_scalar atlas (g(&0)) p /\
    (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p
                    (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
             ~collinear {vec 0,u,v}
             ==> inv D1 * mfd_scalar atlas (g(&0)) p <
                 mfd_sectional atlas (g(&0)) x u v /\
                 mfd_sectional atlas (g(&0)) x u v <
                 D1 * mfd_scalar atlas (g(&0)) p) /\
    (?b e e' z z' f f'.
       mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
       Y = IMAGE b (ball(vec 0,&1)) /\
       rfs_neck (top,atlas) (g(&0)) eps z e /\
       IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
       rfs_neck (top,atlas) (g(&0)) eps z' e' /\
       IMAGE e' (rfs_neck_dom eps) SUBSET U /\
       IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
       sphere_diffeo f f' /\
       (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) /\
    open_in top U /\ Y SUBSET U /\
    mfd_ball (top,atlas) (g(&0)) p (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))
      SUBSET Y /\
    rfs_neck (top,atlas) (g(&0)) (eps / K1) z3 e3 /\
    U SUBSET mfd_ball (top,atlas) (g(&0)) p
               (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) UNION
             IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) /\
    IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET U /\
    w0 IN apx_slab (--inv(eps / K1)) (&3 * inv eps) /\
    e3 w0 IN mfd_ball (top,atlas) (g(&0)) p
               (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
    (!y. y IN IMAGE e3 (rfs_neck_dom (eps / K1))
         ==> mfd_scalar atlas (g(&0)) z3 / &2 <= mfd_scalar atlas (g(&0)) y /\
             mfd_scalar atlas (g(&0)) y <= &3 / &2 * mfd_scalar atlas (g(&0)) z3) /\
    (!y q. y IN Y /\ q IN topspace top /\ ~(q IN U)
           ==> ?s. s IN IMAGE e3 (rfs_neck_dom (eps / K1)) /\
                   mfd_joinable (top,atlas) y s /\
                   mfd_dist (top,atlas) (g(&0)) y s +
                   sqrt(&1 - eps / K1) * inv(sqrt(mfd_scalar atlas (g(&0)) z3)) *
                   (&2 * inv eps)
                   <= mfd_dist (top,atlas) (g(&0)) y q)`;;

let P2BCC_SLAB_IN_DOM = prove
 (`!eps K1. &0 < eps /\ &4 <= K1
            ==> apx_slab (--inv(eps / K1)) (&3 * inv eps) SUBSET rfs_neck_dom (eps / K1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_slab; rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--inv(eps / K1) / sqrt(&2) = --(inv(sqrt(&2) * (eps / K1)))` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN UNDISCH_TAC `&4 <= K1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 * inv eps) / sqrt(&2) <= inv(sqrt(&2) * (eps / K1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&3 * inv eps) / sqrt(&2) = &3 * inv(sqrt(&2) * eps) /\
                  inv(sqrt(&2) * (eps / K1)) = K1 * inv(sqrt(&2) * eps)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN UNDISCH_TAC `&4 <= K1` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `exp(--inv(eps / K1) / sqrt(&2)) < norm(y:real^3)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp((&3 * inv eps) / sqrt(&2))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]);;

let P2BCC_BASIC = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
         riemannian_metric atlas (g(&0)) /\ mfd_complete (top,atlas) (g(&0)) /\
         (!x. x IN mfd_ball (top,atlas) (g(&0)) p
                           (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))
              ==> x IN topspace top) /\
         p IN mfd_ball (top,atlas) (g(&0)) p (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
         p IN U /\ U SUBSET topspace top /\
         IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET
         IMAGE e3 (rfs_neck_dom (eps / K1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bcc_hyp] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  SUBGOAL_THEN `p IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p
                       (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`] MFD_DIST_REFL) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ASM SET_TAC[];
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC P2BCC_SLAB_IN_DOM THEN ASM_REWRITE_TAC[]]);;

let P2BCC_SCALAR_PINCH = prove
 (`!top atlas (h:B->real^3^3) x a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v}
            ==> a <= mfd_sectional atlas h x u v /\ mfd_sectional atlas h x u v <= b)
     ==> &6 * a <= mfd_scalar atlas h x /\ mfd_scalar atlas h x <= &6 * b`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `h:B->real^3^3`; `x:B`; `a:real`] P2BS_MFD_SCALAR_SECT);
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `h:B->real^3^3`; `x:B`; `b:real`] P2BS_MFD_SCALAR_SECT)] THEN
  ASM_SIMP_TAC[]);;

let P2BCC_R_BOUNDS = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0
     ==> (!y. y IN mfd_ball (top,atlas) (g(&0)) p
                           (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))
              ==> &6 * (inv D1 * mfd_scalar atlas (g(&0)) p) <= mfd_scalar atlas (g(&0)) y /\
                  mfd_scalar atlas (g(&0)) y <= &6 * (D1 * mfd_scalar atlas (g(&0)) p)) /\
         &4 * (inv D1 * mfd_scalar atlas (g(&0)) p) <= mfd_scalar atlas (g(&0)) z3 /\
         mfd_scalar atlas (g(&0)) z3 <= &12 * (D1 * mfd_scalar atlas (g(&0)) p) /\
         (!y. y IN U
              ==> &2 * (inv D1 * mfd_scalar atlas (g(&0)) p) <= mfd_scalar atlas (g(&0)) y /\
                  mfd_scalar atlas (g(&0)) y <= &18 * (D1 * mfd_scalar atlas (g(&0)) p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2BCC_BASIC th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[p2bcc_hyp] th)) THEN
  ABBREV_TAC `Rp = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` THEN
  ABBREV_TAC `Bp = mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (Dst * inv(sqrt Rp))` THEN
  SUBGOAL_THEN `&0 < inv D1 * Rp /\ &0 < D1 * Rp` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN Bp
        ==> &6 * (inv D1 * Rp) <= mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y /\
            mfd_scalar atlas (g(&0)) y <= &6 * (D1 * Rp)`
  (LABEL_TAC "rb") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC P2BCC_SCALAR_PINCH THEN
    EXISTS_TAC `top:B topology` THEN ASM_SIMP_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a < x /\ x < b ==> a <= x /\ x <= b`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e3:real^3->B) w0 IN IMAGE e3 (rfs_neck_dom (eps / K1))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`] P2BCC_SLAB_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w0:real^3) IN apx_slab (--inv(eps / K1)) ((&3 * inv eps))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "rn" o check (fun th ->
    let has c = can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false))
                    (concl th) in
    is_forall (concl th) && has "rfs_neck_dom" && not (has "mfd_dist"))) THEN
  SUBGOAL_THEN `&4 * (inv D1 * Rp) <= mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3 /\
                mfd_scalar atlas (g(&0)) z3 <= &12 * (D1 * Rp)` STRIP_ASSUME_TAC THENL
   [USE_THEN "rb" (MP_TAC o C MP (ASSUME `(e3:real^3->B) w0 IN Bp`) o SPEC `(e3:real^3->B) w0`) THEN
    USE_THEN "rn" (MP_TAC o C MP (ASSUME `(e3:real^3->B) w0 IN IMAGE e3 (rfs_neck_dom (eps / K1))`)
                   o SPEC `(e3:real^3->B) w0`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN Bp \/ y IN IMAGE (e3:real^3->B) (rfs_neck_dom (eps / K1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN U` THEN
    UNDISCH_TAC `U SUBSET Bp UNION IMAGE (e3:real^3->B) (apx_slab (--inv(eps / K1)) (&3 * inv eps))` THEN
    UNDISCH_TAC `IMAGE (e3:real^3->B) (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET
                 IMAGE e3 (rfs_neck_dom (eps / K1))` THEN
    SET_TAC[];
    USE_THEN "rb" (MP_TAC o C MP (ASSUME `(y:B) IN Bp`) o SPEC `y:B`) THEN ASM_REAL_ARITH_TAC;
    USE_THEN "rn" (MP_TAC o C MP (ASSUME `(y:B) IN IMAGE e3 (rfs_neck_dom (eps / K1))`)
                   o SPEC `y:B`) THEN
    ASM_REAL_ARITH_TAC]);;



(* ------------------------------------------------------------------------- *)
(* The intrinsic diameter of U.  Curves from p shorter than Dst rho stay in  *)
(* B, inside U, so B is within Dst rho of p in U; a point e3 v of the slab   *)
(* is joined to e3 w0 (in B) by the image of a model path inside the slab    *)
(* (APX_MODEL_PATH, APX_NECK_CURVE_LENGTH).                                  *)
(* ------------------------------------------------------------------------- *)

let P2BCC_SHORT_CURVES = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 (gamma:real->B).
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma (&0) = p /\
     mfd_length atlas (g(&0)) gamma (&0) (&1) <
     Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BCC_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bcc_hyp] th)) STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->B) s IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p
                  (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))` MP_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `gamma:real->B`; `&0`; `s:real`; `&1`]
                  MFD_LENGTH_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->B) s IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `&0`; `&1`] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas ((g:real->B->real^3^3) (&0)) gamma (&0) s` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (&0)`; `gamma:real->B`; `&0`; `s:real`]
                    MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (&0)`; `gamma:real->B`; `s:real`; `&1`]
                    MFD_LENGTH_POS_LE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p
                   (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) SUBSET Y` THEN
    UNDISCH_TAC `(Y:B->bool) SUBSET U` THEN SET_TAC[]]);;

let P2BCC_SLAB_PATH = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 v.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\
     v IN apx_slab (--inv(eps / K1)) (&3 * inv eps)
     ==> mfd_joinable_in (top,atlas) U (e3 w0) (e3 v) /\
         mfd_dist_in (top,atlas) (g(&0)) U (e3 w0) (e3 v) <=
         sqrt(&1 + eps / K1) * inv(sqrt(mfd_scalar atlas (g(&0)) z3)) *
         (abs(apx_sval w0 - apx_sval v) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BCC_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bcc_hyp] th)) ASSUME_TAC) THEN
  ABBREV_TAC `S = apx_slab (--inv(eps / K1)) (&3 * inv eps)` THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET rfs_neck_dom (eps / K1)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2BCC_SLAB_IN_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (rfs_neck_dom (eps / K1))` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `w0:real^3`; `v:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((w0:real^3) = vec 0) /\ ~((v:real^3) = vec 0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(v:real^3) IN S` THEN UNDISCH_TAC `(w0:real^3) IN S` THEN
      EXPAND_TAC "S" THEN SIMP_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN
    UNDISCH_TAC `(v:real^3) IN S` THEN UNDISCH_TAC `(w0:real^3) IN S` THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `rfs_neck_dom (eps / K1)`; `c:real->real^3`;
                 `&0`; `&1`] P2BF_C1_CURVE_OPEN_MONO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `eps / K1`; `z3:B`; `e3:real^3->B`;
                 `c:real->real^3`; `&0`; `&1`] APX_NECK_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < K1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (e3:real^3->B) ((c:real->real^3) t) IN U`
  (LABEL_TAC "inU") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:real->real^3) t IN S` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e3:real^3->B) S SUBSET U` THEN
    UNDISCH_TAC `(c:real->real^3) t IN S` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `(e3:real^3->B) o (c:real->real^3)` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `(e3:real^3->B) o (c:real->real^3)`;
                 `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas ((g:real->B->real^3^3) (&0)) ((e3:real^3->B) o (c:real->real^3)) (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps / K1) * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) *
              mfd_length (open_set_atlas (rfs_neck_dom (eps / K1))) (cylinder_flow (&0))
                         c (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      SUBGOAL_THEN `&0 < eps / K1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) (eps / K1) z3 e3` THEN
      SIMP_TAC[rfs_neck; REAL_LT_IMP_LE]];
    ASM_REWRITE_TAC[]]);;

let P2BCC_H3_BOUND = prove
 (`!Rp R3 D1. &0 < Rp /\ &1 < D1 /\ &4 * (inv D1 * Rp) <= R3
              ==> inv(sqrt R3) <= D1 / &2 * inv(sqrt Rp)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv D1 * Rp` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&4 * (inv D1 * Rp))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `inv(&4 * (inv D1 * Rp)) = D1 / &4 * inv Rp` SUBST1_TAC THENL
     [UNDISCH_TAC `&1 < D1` THEN UNDISCH_TAC `&0 < Rp` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(D1 / &2) pow 2 * x = (D1 pow 2 / &4) * x`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `D1 <= D1 * D1 ==> D1 / &4 <= (D1 * D1) / &4`) THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * D1 <= D1 * D1 ==> D1 <= D1 * D1`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC]]);;

let P2BCC_DIST_IN_P = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 y.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\ y IN U
     ==> mfd_joinable_in (top,atlas) U p y /\
         mfd_dist_in (top,atlas) (g(&0)) U p y <=
         (Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)) *
         inv(sqrt(mfd_scalar atlas (g(&0)) p))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_R_BOUNDS) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  ABBREV_TAC `Rp = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` THEN
  ABBREV_TAC `rho = inv(sqrt Rp)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `Bp = mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (Dst * rho)` THEN
  SUBGOAL_THEN
   `!q. q IN Bp ==> mfd_joinable_in (top,atlas) U p q /\
                    mfd_dist_in (top,atlas) ((g:real->B->real^3^3) (&0)) U p q < Dst * rho`
  (LABEL_TAC "ball") THENL
   [X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas) p (q:B) /\
                  mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p q < Dst * rho`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:B) IN Bp` THEN EXPAND_TAC "Bp" THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `p:B`; `q:B`; `Dst * rho`]
                  P2BC_DIST_IN_SHORT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BCC_SHORT_CURVES THEN
      MAP_EVERY EXISTS_TAC [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`;
                            `C71:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `g:real->B->real^3^3`; `p:B`; `Y:B->bool`; `z3:B`; `e3:real^3->B`;
                            `w0:real^3`] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[REAL_LET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D1 * (K1 * inv eps + &3 * inv eps + &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= K1 * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN Bp \/ ?v. v IN apx_slab (--inv(eps / K1)) (&3 * inv eps) /\
                                   y = (e3:real^3->B) v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN U` THEN
    UNDISCH_TAC `U SUBSET Bp UNION
                 IMAGE (e3:real^3->B) (apx_slab (--inv(eps / K1)) (&3 * inv eps))` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN MESON_TAC[];
    USE_THEN "ball" (MP_TAC o C MP (ASSUME `(y:B) IN Bp`) o SPEC `y:B`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `Dst * rho` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                `e3:real^3->B`; `w0:real^3`; `v:real^3`] P2BCC_SLAB_PATH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ball" (MP_TAC o C MP (ASSUME `(e3:real^3->B) w0 IN Bp`) o SPEC `(e3:real^3->B) w0`) THEN
  STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `p:B`; `(e3:real^3->B) w0`;
                 `(e3:real^3->B) v`] MFD_DIST_IN_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&1 + eps / K1) * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) *
                (abs(apx_sval (w0:real^3) - apx_sval (v:real^3)) + sqrt(&2) * pi) <=
                D1 * (K1 * inv eps + &3 * inv eps + &5) * rho` MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `mfd_dist_in (top,atlas) ((g:real->B->real^3^3) (&0)) U p
                   ((e3:real^3->B) w0) < Dst * rho` THEN
    UNDISCH_TAC `mfd_dist_in (top,atlas) ((g:real->B->real^3^3) (&0)) U
                   ((e3:real^3->B) w0) (e3 (v:real^3)) <=
                 sqrt(&1 + eps / K1) * inv(sqrt(mfd_scalar atlas (g(&0)) z3)) *
                 (abs(apx_sval w0 - apx_sval v) + sqrt(&2) * pi)` THEN
    REAL_ARITH_TAC] THEN
  (* the neck part of the bound *)
  SUBGOAL_THEN `&0 < K1 /\ &0 < eps / K1 /\ eps / K1 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= K1 ==> &0 < K1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps / K1) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) <= D1 / &2 * rho`
  ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC P2BCC_H3_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval (w0:real^3) - apx_sval (v:real^3)) + sqrt(&2) * pi <=
                K1 * inv eps + &3 * inv eps + &5` ASSUME_TAC THENL
   [MP_TAC APX_SQRT2_PI THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (--inv(eps / K1)) (&3 * inv eps)` THEN
    UNDISCH_TAC `(w0:real^3) IN apx_slab (--inv(eps / K1)) (&3 * inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `inv(eps / K1) = K1 * inv eps` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < K1` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) /\
                &0 <= abs(apx_sval (w0:real^3) - apx_sval (v:real^3)) + sqrt(&2) * pi /\
                &0 <= sqrt(&1 + eps / K1)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) (eps / K1) z3 e3` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (D1 / &2 * rho) * (K1 * inv eps + &3 * inv eps + &5)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let P2BCC_SUP_R = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0
     ==> (!y. y IN U ==> mfd_scalar atlas (g(&0)) y <=
                         sup(IMAGE (mfd_scalar atlas (g(&0))) U)) /\
         &0 < sup(IMAGE (mfd_scalar atlas (g(&0))) U) /\
         sup(IMAGE (mfd_scalar atlas (g(&0))) U) <=
         &18 * (D1 * mfd_scalar atlas (g(&0)) p) /\
         inv(sqrt(&18 * D1)) * inv(sqrt(mfd_scalar atlas (g(&0)) p)) <=
         inv(sqrt(sup(IMAGE (mfd_scalar atlas (g(&0))) U)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_R_BOUNDS) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  ABBREV_TAC `Rp = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` THEN
  ABBREV_TAC `SR = IMAGE (mfd_scalar atlas ((g:real->B->real^3^3) (&0))) U` THEN
  MP_TAC(ISPEC `SR:real->bool` SUP) THEN ANTS_TAC THENL
   [EXPAND_TAC "SR" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `&18 * (D1 * Rp)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "least")) THEN
  SUBGOAL_THEN `!y. y IN U ==> mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y <= sup SR`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN EXPAND_TAC "SR" THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sup SR <= &18 * (D1 * Rp)` ASSUME_TAC THENL
   [USE_THEN "least" MATCH_MP_TAC THEN EXPAND_TAC "SR" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sup SR` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Rp:real` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Rp" THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &18 * D1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let P2BCC_DIAM_ARITH = prove
 (`!M q Q rho C t. &0 <= M /\ &0 < q /\ q <= Q /\ &2 * M * Q < C /\ &0 < rho /\
                   inv q * rho <= t
                   ==> &2 * M * rho < C * t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv q * rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * M * rho = (&2 * M * q) * (inv q * rho)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&2 * M * Q) * (inv q * rho)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= M * (Q - q) ==> &2 * M * q <= &2 * M * Q`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `C * (inv q * rho)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= &2 * M * Q /\ &2 * M * Q < C ==> &0 <= C`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= M * Q ==> &0 <= &2 * M * Q`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let P2BCC_DIAM = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 C.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\
     &2 * (Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)) * (&18 * D1) < C
     ==> rfs_sup_lt {mfd_dist_in (top,atlas) (g(&0)) U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U}
                    (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g(&0))) U))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_SUP_R) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  ABBREV_TAC `M = Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)` THEN
  ABBREV_TAC `rho = inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p))` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv eps /\ &0 <= K1 * inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC RFS_CAP_DIAM_BOUND THEN EXISTS_TAC `&2 * M * rho` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y1:B`; `y2:B`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y1:B`] P2BCC_DIST_IN_P) THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y2:B`] P2BCC_DIST_IN_P) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `y1:B`; `p:B`; `y2:B`]
                  MFD_DIST_IN_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `y1:B`; `p:B`] MFD_DIST_IN_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2BCC_DIAM_ARITH THEN
    MAP_EVERY EXISTS_TAC [`sqrt(&18 * D1)`; `&18 * D1`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &18 * D1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;



(* ------------------------------------------------------------------------- *)
(* The volume clause.  U lies in the ball of radius 2 M rho about p          *)
(* (previous section), whose volume is at most 4/3 pi (2 M rho)^3 by         *)
(* Bishop-Gromov (sec >= 0, complete); sup R <= 18 D1 R(p) turns this into C *)
(* sup R^(-3/2).                                                             *)
(* ------------------------------------------------------------------------- *)

let P2BCC_PI_LE = prove
 (`pi <= &16 / &5`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2BCC_VOL_ARITH = prove
 (`!M q Q rho C t pp. &0 <= M /\ &0 < q /\ q <= Q /\ &35 * M pow 3 * Q pow 3 < C /\
                      &0 < rho /\ inv q * rho <= t /\ &0 <= pp /\ pp <= &16 / &5
                      ==> &4 / &3 * pp * (&2 * M * rho) pow 3 < C * t pow 3`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = inv q * rho` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `rho = q * a` SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M pow 3 /\ &0 <= q pow 3 /\ q pow 3 <= Q pow 3 /\ &0 < a pow 3 /\
                a pow 3 <= t pow 3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &3 * pp * (&2 * M * q * a) pow 3 =
                (&32 / &3 * pp * M pow 3 * q pow 3) * a pow 3` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&32 / &3 * pp * M pow 3 * q pow 3 <= &512 / &15 * M pow 3 * Q pow 3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `pp * (M pow 3 * q pow 3) <= &16 / &5 * (M pow 3 * Q pow 3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M pow 3 * Q pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&32 / &3 * pp * M pow 3 * q pow 3 < C` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `C * a pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BCC_VOL = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 C.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\
     &35 * (Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)) pow 3 * (&18 * D1) pow 3 < C
     ==> ?v. mfd_has_volume (top,atlas) (g(&0)) U v /\
             v < C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g(&0))) U))) pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_SUP_R) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  ABBREV_TAC `M = Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)` THEN
  ABBREV_TAC `rho = inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p))` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv eps /\ &0 <= K1 * inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Bb = mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&2 * M * rho)` THEN
  SUBGOAL_THEN `U SUBSET (Bb:B->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y:B`] P2BCC_DIST_IN_P) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "Bb" THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_IMP]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist_in (top,atlas) ((g:real->B->real^3^3) (&0)) U p y` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M * rho` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x < &2 * x`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (top,atlas) ((g:real->B->real^3^3) (&0)) Bb
                  (mfd_volume (top,atlas) (g(&0)) Bb)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN EXISTS_TAC `top closure_of (Bb:B->bool)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Bb" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `U:B->bool`; `Bb:B->bool`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0)) Bb`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(SPEC `UNIV:B->bool` CMP_T3_BISHOP_GROMOV_P2B) THEN
  REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `(g:real->B->real^3^3) (&0)`; `p:B`; `&2 * M * rho`;
                             `&2 * M * rho`;
                             `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0)) Bb`;
                             `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0)) Bb`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &2 * x`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) (&0)) U` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&4 / &3 * pi * (&2 * M * rho) pow 3` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BCC_VOL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`sqrt(&18 * D1)`; `&18 * D1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; PI_POS_LE; P2BCC_PI_LE] THEN
  SUBGOAL_THEN `&1 <= &18 * D1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;



(* ------------------------------------------------------------------------- *)
(* Clause 7 of the cap with d = kappa0.  For y in Y and a ball B(y,r) with   *)
(* sup R = r^-2: the closure is compact (completeness); it lies in U, since  *)
(* a point q of the closure outside U would give, by the width hypothesis, a *)
(* point s of the neck e3 in the ball with R(s) >= R3/2, so r <= sqrt 2 h3,  *)
(* against r >= d(y,q) >= 100 h3; the volume is at least kappa0 r^3 by       *)
(* kappa0-noncollapsing, as abs(Rm)(s,.) <= R(0,.)/2 <= r^-2.                *)
(* ------------------------------------------------------------------------- *)

let P2BCC_C7_ARITH = prove
 (`!r R3 W. &0 < r /\ &0 < R3 /\ &100 * inv(sqrt R3) <= W /\ W <= r /\
            R3 / &2 <= inv(r pow 2) ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv R3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&10000 * inv R3 <= r pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&10000 * inv R3 = (&100 * inv(sqrt R3)) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 <= &2 * inv R3` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `inv(inv x) = x /\ inv(R3 / &2) = &2 * inv R3 /\
                             inv(inv x) <= inv(R3 / &2) ==> x <= &2 * inv R3`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_INV_INV];
      UNDISCH_TAC `&0 < R3` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BCC_C7 = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 y r.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\
     y IN Y /\ &0 < r /\
     (?Bd. !z. z IN mfd_ball (top,atlas) (g(&0)) y r ==> mfd_scalar atlas (g(&0)) z <= Bd) /\
     sup(IMAGE (mfd_scalar atlas (g(&0))) (mfd_ball (top,atlas) (g(&0)) y r)) = inv(r pow 2)
     ==> compact_in top (top closure_of mfd_ball (top,atlas) (g(&0)) y r) /\
         top closure_of mfd_ball (top,atlas) (g(&0)) y r SUBSET U /\
         ?v. mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) y r) v /\
             kappa0 <= v / r pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Bd:real`) ASSUME_TAC)))) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN Y` THEN UNDISCH_TAC `(Y:B->bool) SUBSET U` THEN
    UNDISCH_TAC `(U:B->bool) SUBSET topspace top` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) y r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `y:B`] MFD_DIST_REFL) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `Bl = mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) y r` THEN
  SUBGOAL_THEN `!z. z IN Bl ==> mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z <= inv(r pow 2)`
  (LABEL_TAC "rsup") THENL
   [X_GEN_TAC `zb:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
       can (find_term (fun u -> try fst(dest_const u) = "sup" with Failure _ -> false))
           (concl th))) THEN
    MP_TAC(ISPEC `IMAGE (mfd_scalar atlas ((g:real->B->real^3^3) (&0))) Bl` SUP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; EXISTS_TAC `Bd:real` THEN ASM_SIMP_TAC[]];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Bl" THEN MATCH_MP_TAC RFU_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) y q <= r` ASSUME_TAC THENL
     [SUBGOAL_THEN `top closure_of (Bl:B->bool) SUBSET
                    mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) y r` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
        ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN EXPAND_TAC "Bl" THEN
        REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `(y:B) IN Y`)
                                   (CONJ (ASSUME `(q:B) IN topspace top`) (ASSUME `~((q:B) IN U)`))) o
                SPECL [`y:B`; `q:B`] o check (fun th ->
      let has c = can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false))
                      (concl th) in
      is_forall (concl th) && has "rfs_neck_dom" && has "mfd_dist")) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:B` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `W = sqrt(&1 - eps / K1) *
                    inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) * (&2 * inv eps)` THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) (eps / K1) z3 e3` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    SUBGOAL_THEN `&100 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) <= W`
    ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN
      SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - eps / K1) /\ &200 <= &2 * inv eps` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RSQRT THEN
          SUBGOAL_THEN `eps / K1 <= &1 / &4` MP_TAC THENL
           [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= K1 ==> &0 < K1`] THEN
            ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC];
          MATCH_MP_TAC(REAL_ARITH `&100 <= x ==> &200 <= &2 * x`) THEN
          MATCH_MP_TAC REAL_LE_RINV THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3))`
      ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 / &2 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3)) * &200` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) y s` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:B) IN Bl` ASSUME_TAC THENL
     [EXPAND_TAC "Bl" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < W` MP_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&100 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BCC_C7_ARITH THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z3`;
                          `W:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MP (ASSUME `(s:B) IN IMAGE e3 (rfs_neck_dom (eps / K1))`) o
                  SPEC `s:B` o check (fun th ->
        let has c = can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false))
                        (concl th) in
        is_forall (concl th) && has "rfs_neck_dom" && not (has "mfd_dist"))) THEN
      REAL_ARITH_TAC;
      USE_THEN "rsup" (MP_TAC o C MP (ASSUME `(s:B) IN Bl`) o SPEC `s:B`) THEN REWRITE_TAC[]];
    (* the volume *)
    FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) =
          "rfs_kappa_noncollapsed" with Failure _ -> false)) THEN
    REWRITE_TAC[rfs_flow_view; rfs_kappa_noncollapsed] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `y:B`; `r:real`]) THEN
    REWRITE_TAC[rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Bl" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`s:real`; `zb:B`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(zb:B) IN Bl` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(zb:B) IN topspace top` ASSUME_TAC THENL
         [UNDISCH_TAC `(zb:B) IN Bl` THEN EXPAND_TAC "Bl" THEN
          REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`UNIV:B->bool`; `kappa0:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `s:real`; `zb:B`] P2AL65_KSOL_RM_LE0) THEN
        ASM_REWRITE_TAC[P2BKC_KSOL_DRDT] THEN
        USE_THEN "rsup" (MP_TAC o C MP (ASSUME `(zb:B) IN Bl`) o SPEC `zb:B`) THEN
        SUBGOAL_THEN `&0 < inv(r pow 2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
          REAL_ARITH_TAC]];
      DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `v:real` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < r pow 3` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]]);;



(* ------------------------------------------------------------------------- *)
(* The ratio and derivative clauses, the constant C and the main theorem.    *)
(* ------------------------------------------------------------------------- *)

let P2BCC_RATIO = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 y1 y2.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\ y1 IN U /\ y2 IN U
     ==> mfd_scalar atlas (g(&0)) y2 / mfd_scalar atlas (g(&0)) y1 <= &9 * D1 pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") STRIP_ASSUME_TAC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_R_BOUNDS) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  ABBREV_TAC `Rp = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` THEN
  SUBGOAL_THEN `&0 < inv D1 * Rp` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `(y2:B) IN U`) o SPEC `y2:B` o check (fun th ->
    is_forall (concl th) && can (find_term (fun u -> u = `&18`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `(y1:B) IN U`) o SPEC `y1:B` o check (fun th ->
    is_forall (concl th) && can (find_term (fun u -> u = `&18`)) (concl th))) THEN
  ABBREV_TAC `a = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y1` THEN
  ABBREV_TAC `b = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y2` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&18 * (D1 * Rp)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&18 * (D1 * Rp) = (&9 * D1 pow 2) * (&2 * (inv D1 * Rp))` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 < D1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &9 * x`) THEN REWRITE_TAC[REAL_LE_POW_2]);;

let P2BCC_DERIV = prove
 (`!eps K1 Dst D1 kappa0 C71 top atlas (g:real->B->real^3^3) p U Y z3 e3 w0 y.
     p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0 /\ y IN U
     ==> sqrt(rfs_scalar_grad2 atlas (g(&0)) y) /
         (mfd_scalar atlas (g(&0)) y * sqrt(mfd_scalar atlas (g(&0)) y)) <= C71 /\
         abs(rfs_scalar_lap atlas (g(&0)) y + &2 * rfs_ric_norm2 atlas (g(&0)) y) /
         mfd_scalar atlas (g(&0)) y pow 2 <= C71`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_R_BOUNDS) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bcc_hyp]) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(y:B) IN U`) o SPEC `y:B` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `&18`)) (concl th))) THEN
    SUBGOAL_THEN `&0 < inv D1 * mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(y:B) IN topspace top`) o SPEC `y:B` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "rfs_scalar_grad2" with Failure _ -> false))
        (concl th))) THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R * sqrt R /\ &0 < R pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let P2BCC_MAIN = prove
 (`!eps K1 Dst D1 kappa0 C71.
     &0 < eps /\ eps <= &1 / &100 /\ &4 <= K1 /\ &0 < Dst /\ &1 < D1 /\
     &0 < kappa0 /\ &0 < C71
     ==> ?C. &1 < C /\
             !top atlas (g:real->B->real^3^3) p U Y z3 e3 w0.
               p2bcc_hyp eps K1 Dst D1 kappa0 C71 top atlas g p U Y z3 e3 w0
               ==> rfs_cap (top,atlas) (g(&0)) C eps U Y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = Dst + D1 * (K1 * inv eps + &3 * inv eps + &5)` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv eps /\ &0 <= K1 * inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `C = &2 * M * (&18 * D1) + &35 * M pow 3 * (&18 * D1) pow 3 +
                  &9 * D1 pow 2 + inv kappa0 + C71 + &2` THEN
  SUBGOAL_THEN `&0 <= &2 * M * (&18 * D1) /\ &0 <= &35 * M pow 3 * (&18 * D1) pow 3 /\
                &0 <= &9 * D1 pow 2 /\ &0 < inv kappa0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &35 * x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &9 * x`) THEN REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[REAL_LT_INV_EQ]];
    ALL_TAC] THEN
  EXISTS_TAC `C:real` THEN CONJ_TAC THENL [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_BASIC) THEN
  USE_THEN "H" (STRIP_ASSUME_TAC o MATCH_MP P2BCC_R_BOUNDS) THEN
  USE_THEN "H" (fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun c -> not (is_exists (concl c))) (CONJUNCTS(REWRITE_RULE[p2bcc_hyp] th)))) THEN
  REWRITE_TAC[rfs_cap] THEN
  USE_THEN "H" (fun th -> REWRITE_TAC[REWRITE_RULE[p2bcc_hyp] th]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* R > 0 on U *)
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(y:B) IN U`) o SPEC `y:B` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `&18`)) (concl th))) THEN
    SUBGOAL_THEN `&0 < inv D1 * mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    (* diameter *)
    MATCH_MP_TAC P2BCC_DIAM THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`;
                          `C71:real`; `p:B`; `Y:B->bool`; `z3:B`; `e3:real^3->B`;
                          `w0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC;
    (* ratio *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `&9 * D1 pow 2` THEN
    CONJ_TAC THENL [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BCC_RATIO THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `K1:real`; `Dst:real`; `kappa0:real`;
                          `C71:real`; `top:B topology`; `p:B`; `U:B->bool`; `Y:B->bool`;
                          `z3:B`; `e3:real^3->B`; `w0:real^3`] THEN
    ASM_REWRITE_TAC[];
    (* volume *)
    REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC P2BCC_VOL THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`;
                          `C71:real`; `p:B`; `Y:B->bool`; `z3:B`; `e3:real^3->B`;
                          `w0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC;
    (* clause 7 *)
    EXISTS_TAC `kappa0:real` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `kappa0 = inv(inv kappa0)` (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
       [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y:B`; `r:real`] P2BCC_C7) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    (* derivative clauses *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `C71:real` THEN
    CONJ_TAC THENL [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y:B`] P2BCC_DERIV) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `C71:real` THEN
    CONJ_TAC THENL [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`;
                  `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                  `e3:real^3->B`; `w0:real^3`; `y:B`] P2BCC_DERIV) THEN
    ASM_SIMP_TAC[]]);;

let P2BCC_KNCL_CAPC = prove
 (`!w:B->bool. P2B_KNCL_CAPC_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_KNCL_CAPC_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `K1:real`; `Dst:real`; `D1:real`; `kappa0:real`; `C71:real`]
               (INST_TYPE [`:B`,`:B`] P2BCC_MAIN)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `C:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`; `U:B->bool`; `Y:B->bool`; `z3:B`;
                       `e3:real^3->B`; `w0:real^3`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:B`; `z3:B`; `e3:real^3->B`; `w0:real^3`] THEN
  ASM_REWRITE_TAC[p2bcc_hyp]);;

