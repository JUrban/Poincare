(* ========================================================================= *)
(* pc_p2a_kap0: MT Prop 9.58 (universal kappa0 for non-round 3-dimensional   *)
(* kappa-solutions) in route form, on the L-geometry constants FL6 (MT Thm   *)
(* 8.1) and FL7 (scaling), MT Cor 9.10 in integrated form                    *)
(* (P2B_COR_9_10_STATEMENT), a based asymptotic soliton and MT Cor 9.44      *)
(* (shift form).  Proof (MT pp. 220-221): at (p,t0) shift time; the based    *)
(* asymptotic soliton has l(q k,tau k) <= 3/2; a compact round limit         *)
(* contradicts non-roundness by Cor 9.44; otherwise the limit is a cylinder  *)
(* model, whose unit balls have volume >= 1/40 (pc_p2a_cylm), so by          *)
(* LIM_VOL the balls B(q k, 2 sqrt(tau k)) at -tau k have                    *)
(* volume >= tau k^(3/2) / 80, l <= 9 on them by Cor 9.10, and FL6           *)
(* for the flow rescaled by 1/tau k (FL7) gives kappa0-noncollapsing at      *)
(* (p,t0) on scales <= sqrt(tau k).                                          *)
(* The statement texts (the based asymptotic soliton, Cor 9.44 in shift form *)
(* and the route) are those of Part 2B.                                      *)
(* ========================================================================= *)

needs "src/pc_p2a_cylm.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_p2b_w920g.ml";;
needs "src/pc_p2b_c910.ml";;
needs "src/pc_p2b_c914.ml";;
needs "src/pc_p2a_flow.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_p2a_fldefs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Time shifts of kappa-solutions.                                           *)
(* ========================================================================= *)

(* A Ricci flow on (a,b) is a flow on (a,t1] smooth up to t1, for t1 < b. *)

let P2AK0_FLOW_UPTO_OF_ON = prove
 (`!top atlas a b (g:real->B->real^3^3) t1.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < b
     ==> rfs_flow_upto (top,atlas) a t1 g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`b - t1`;
      `\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
         (metric_local atlas c ((g:real->B->real^3^3) (drop(fstcart z))) (sndcart z))`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_ARITH `t1 + (b - t1) = b`; FSTCART_PASTECART;
                 SNDCART_PASTECART; LIFT_DROP]]);;

(* The shift g(t + t0), t0 <= 0, of a kappa-solution is a kappa-solution. *)

let P2AK0_KSOL_SHIFT = prove
 (`!kappa top atlas (g:real->B->real^3^3) t0.
     p2b_kappa_solution kappa (top,atlas) g /\ t0 <= &0
     ==> p2b_kappa_solution kappa (top,atlas) (\t. g(t + t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t0 = &0` THENL
   [ASM_REWRITE_TAC[REAL_ADD_RID; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `t0 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "cpl")
   (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
   (CONJUNCTS_THEN2 (LABEL_TAC "nf") (LABEL_TAC "kn")))))))))))
   (LABEL_TAC "slab")) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* flow up to 0 *)
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `a + t0 - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
    DISCH_THEN(MP_TAC o SPEC `--t0` o MATCH_MP RICCI_FLOW_TRANSLATE) THEN
    REWRITE_TAC[REAL_SUB_RNEG; REAL_ADD_LID] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AK0_FLOW_UPTO_OF_ON THEN EXISTS_TAC `--t0` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`(a + t0 - &1) + --t0`; `--t0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    (* completeness *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "cpl" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* sectional curvature *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* bounded curvature on slices *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "bd" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* non-flat slices *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "nf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* kappa-noncollapsing *)
    X_GEN_TAC `r0:real` THEN USE_THEN "kn" (MP_TAC o SPEC `r0:real`) THEN
    REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_vball; rfs_parabolic_exists;
                rfs_persists; IN_ELIM_THM] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
    ASM_CASES_TAC `t <= &0` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par") (LABEL_TAC "curv"))))) THEN
    SUBGOAL_THEN `t + t0 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t + t0`; `x:B`; `r:real`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        REMOVE_THEN "par" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_LE_REFL] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 < r2 ==> t - r2 < t`) THEN ASM_SIMP_TAC[REAL_POW_LT];
          ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
        REMOVE_THEN "curv" (MP_TAC o SPECL [`s - t0:real`; `y:B`]) THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[]];
    (* curvature bounded on compact time intervals *)
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "slab" (MP_TAC o SPEC `a + t0`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `K:real` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The reduced length on the balls about the q k (Cor 9.10), and the slices *)
(* of the view of a kappa-solution.                                         *)
(* ========================================================================= *)

let P2AK0_SQRT_BOUNDS = prove
 (`sqrt(&3 / &2) <= &5 / &4 /\ sqrt(&3) <= &7 / &4`,
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let P2AK0_SQRT_PROD = prove
 (`!tau. &0 < tau ==> sqrt(&3 / (&4 * tau)) * (&2 * sqrt tau) = sqrt(&3)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 / (&4 * tau)) /\ &0 <= sqrt tau` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `sqrt(&3 / (&4 * tau)) pow 2 = &3 / (&4 * tau) /\ sqrt tau pow 2 = tau`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD);;

(* l <= 9 on the ball of radius 2 sqrt(tau) about a point with l <= 3/2. *)

let P2AK0_LBALL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p tau q y.
     P2B_COR_9_10_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\ &0 < tau /\ q IN topspace top /\
     p2b_klx (top,atlas) g p tau q <= &3 / &2 /\
     y IN mfd_ball (top,atlas) (g(--tau)) q (&2 * sqrt tau)
     ==> p2b_klx (top,atlas) g p tau y <= &9`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_COR_9_10_STATEMENT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`;
                                `g:real->B->real^3^3`; `p:B`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l0") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (K ALL_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(--tau)`; `q:B`; `&2 * sqrt tau`] MFD_BALL_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3)(--tau)) q y < &2 * sqrt tau`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3)(--tau)) q (&2 * sqrt tau)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPECL [`tau:real`; `q:B`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "l0" (MP_TAC o SPECL [`tau:real`; `q:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "l0" (MP_TAC o SPECL [`tau:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p tau q) <= &5 / &4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&3 / &2)` THEN
    REWRITE_TAC[P2AK0_SQRT_BOUNDS] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3 / (&4 * tau)) * mfd_dist (top,atlas) ((g:real->B->real^3^3)(--tau)) q y
                <= &7 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&3 / (&4 * tau)) * (&2 * sqrt tau)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[P2AK0_SQRT_PROD; P2AK0_SQRT_BOUNDS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p tau y) <= &3` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(p2b_klx (top,atlas) (g:real->B->real^3^3) p tau y) pow 2 =
                p2b_klx (top,atlas) g p tau y` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&9 = &3 pow 2` SUBST1_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* The slices of the view of a kappa-solution. *)

let P2AK0_KVIEW_SLICE = prove
 (`!top atlas (g:real->B->real^3^3) tau.
     tau <= &0
     ==> rfs_vtop (p2b_kview (top,atlas) g) tau = top /\
         rfs_vatlas (p2b_kview (top,atlas) g) tau = atlas /\
         rfs_vmetric (p2b_kview (top,atlas) g) tau = g tau`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM]);;

let P2AK0_KVIEW_REG = prove
 (`!kappa top atlas (g:real->B->real^3^3) tau.
     p2b_kappa_solution kappa (top,atlas) g /\
     ~(topspace(rfs_vtop (p2b_kview (top,atlas) g) tau) = {})
     ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top,atlas) g) tau)
                               (rfs_vatlas (p2b_kview (top,atlas) g) tau) /\
         riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) tau)
                           (rfs_vmetric (p2b_kview (top,atlas) g) tau)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  ASM_CASES_TAC `tau <= &0` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* FL6 at taub = 1, l0 = 9, V0 = 1/80 and its application to the flow        *)
(* rescaled by 1/tk.                                                         *)
(* ========================================================================= *)

let p2ak0_fl6 = new_definition
 `p2ak0_fl6 (u:B->bool) (kappa0:real) <=>
    !top atlas a b g p r tau0 B.
       p2a_cbflow (top,atlas:((B->bool)#(B->real^3))->bool) a b g /\
       connected_space top /\ p IN topspace top /\
       &0 < tau0 /\ tau0 <= &1 /\ tau0 < b - a /\ &0 < r /\ r pow 2 <= tau0 /\
       (!s y. b - r pow 2 < s /\ s <= b /\ y IN mfd_ball (top,atlas) (g b) p r
              ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2)) /\
       open_in top B /\
       (?v. mfd_has_volume (top,atlas) (g (b - tau0)) B v /\ &1 / &80 <= v) /\
       (!q. q IN B
            ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 q <= &9)
       ==> ?v. mfd_has_volume (top,atlas) (g b) (mfd_ball (top,atlas) (g b) p r) v /\
               kappa0 * r pow 3 <= v`;;

let P2AK0_FL6_KAPPA0 = prove
 (`!w:B->bool. P2A_FLOW_THM_8_1_STATEMENT w (:3) ==> ?kappa0. &0 < kappa0 /\ p2ak0_fl6 w kappa0`,
  GEN_TAC THEN REWRITE_TAC[P2A_FLOW_THM_8_1_STATEMENT; p2ak0_fl6; DIMINDEX_3] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `&9`; `&1 / &80`]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[]);;

(* Small facts of the rescaling by Q = 1 / tk. *)

let P2AK0_RESCALE_ARITH = prove
 (`!tk. &0 < tk
       ==> inv tk * --(&2 * tk) = --(&2) /\ inv tk * &0 = &0 /\ inv tk * tk = &1 /\
           &0 / inv tk = &0 /\ (&0 - &1) / inv tk = --tk /\ &0 - --(&2) = &2 /\
           sqrt(inv tk pow 3) = inv tk * sqrt(inv tk)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv tk` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div; REAL_MUL_LZERO];
    UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `x pow 3 = x pow 2 * x`] THEN
    ASM_SIMP_TAC[SQRT_MUL; REAL_POW_LE; REAL_LT_IMP_LE; POW_2_SQRT]]);;

let P2AK0_RESCALE_FL6 = prove
 (`!(w:B->bool) kappa0 kappa top atlas (h:real->B->real^3^3) p r tk q vk.
     P2A_FLOW_SCALING_STATEMENT w (:3) /\ p2ak0_fl6 w kappa0 /\
     p2b_kappa_solution kappa (top,atlas) h /\ p IN topspace top /\
     &0 < r /\ r pow 2 <= tk /\ q IN topspace top /\
     (!s y. --(r pow 2) < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (h(&0)) p r
            ==> mfd_rm_norm atlas (h s) y <= inv(r pow 2)) /\
     mfd_has_volume (top,atlas) (h(--tk)) (mfd_ball (top,atlas) (h(--tk)) q (&2 * sqrt tk)) vk /\
     &1 / &80 <= inv tk * sqrt(inv tk) * vk /\
     (!y. y IN mfd_ball (top,atlas) (h(--tk)) q (&2 * sqrt tk)
          ==> p2b_klx (top,atlas) h p tk y <= &9)
     ==> ?v. mfd_has_volume (top,atlas) (h(&0)) (mfd_ball (top,atlas) (h(&0)) p r) v /\
             kappa0 * r pow 3 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl7") (CONJUNCTS_THEN2 (LABEL_TAC "fl6")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "curv")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))))))))))) THEN
  SUBGOAL_THEN `&0 < tk` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AK0_RESCALE_ARITH) THEN
  SUBGOAL_THEN `&0 < inv tk /\ &0 < sqrt(inv tk)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2 * tk)) (&0) (h:real->B->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_KSOL_CBFLOW THEN EXISTS_TAC `kappa:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r' = r * sqrt(inv tk)` THEN
  SUBGOAL_THEN `&0 < r' /\ r' pow 2 <= &1 /\ r' / sqrt(inv tk) = r /\
                inv(r pow 2) / inv tk = inv(r' pow 2) /\ r' pow 2 * tk = r pow 2 /\
                r' pow 3 = r pow 3 * (inv tk * sqrt(inv tk))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN
    SUBGOAL_THEN `sqrt(inv tk) pow 2 = inv tk` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < sqrt(inv tk)` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN
      UNDISCH_TAC `&0 < tk` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `sqrt(inv tk) pow 2 = inv tk` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  ABBREV_TAC `G = \t x. inv tk %% (h:real->B->real^3^3) (t / inv tk) x` THEN
  SUBGOAL_THEN `(G:real->B->real^3^3) (&0) = (\x. inv tk %% h (&0) x) /\
                G (&0 - &1) = (\x. inv tk %% h (--tk) x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (\x. inv tk %% (h:real->B->real^3^3) (&0) x) p r' =
                mfd_ball (top,atlas) (h(&0)) p r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(h:real->B->real^3^3)(&0)`; `inv tk`; `p:B`; `r':real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* (S1) the rescaled flow *)
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2)) (&0) (G:real->B->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `--(&2 * tk)`; `&0`; `h:real->B->real^3^3`; `inv tk`] P2AU_CBFLOW_RESCALE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  (* (S2) curvature on the rescaled parabolic ball *)
  SUBGOAL_THEN
   `!s y. &0 - r' pow 2 < s /\ s <= &0 /\
          y IN mfd_ball (top,atlas) ((G:real->B->real^3^3) (&0)) p r'
          ==> mfd_rm_norm atlas (G s) y <= inv(r' pow 2)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN mfd_ball (top,atlas) ((h:real->B->real^3^3)(&0)) p r` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(h:real->B->real^3^3)(&0)`; `p:B`; `r:real`] MFD_BALL_OPEN) THEN
      ASM_SIMP_TAC[REAL_LE_REFL] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s / inv tk <= &0 /\ --(r pow 2) < s / inv tk` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `s / inv tk = s * tk` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < tk` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= --s * tk ==> s * tk <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `r pow 2 = r' pow 2 * tk` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < (s + r2) * tk ==> --(r2 * tk) < s * tk`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real->B->real^3^3) s = (\x. inv tk %% h (s / inv tk) x)` SUBST1_TAC THENL
     [EXPAND_TAC "G" THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(r' pow 2) = inv(r pow 2) / inv tk` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN REWRITE_TAC[ETA_AX] THEN
    EXISTS_TAC `top:B topology` THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH] THEN
    USE_THEN "curv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* (S3) the ball about q is open *)
  SUBGOAL_THEN `open_in top (mfd_ball (top,atlas) ((h:real->B->real^3^3)(--tk)) q (&2 * sqrt tk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_SIMP_TAC[REAL_ARITH `&0 < tk ==> --tk <= &0`];
    ALL_TAC] THEN
  (* (S4) its rescaled volume *)
  SUBGOAL_THEN
   `?v. mfd_has_volume (top,atlas) ((G:real->B->real^3^3) (&0 - &1))
          (mfd_ball (top,atlas) (h(--tk)) q (&2 * sqrt tk)) v /\ &1 / &80 <= v`
  ASSUME_TAC THENL
   [EXISTS_TAC `inv tk * sqrt(inv tk) * vk` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(h:real->B->real^3^3)(--tk)`;
                   `mfd_ball (top,atlas) ((h:real->B->real^3^3)(--tk)) q (&2 * sqrt tk)`;
                   `vk:real`; `inv tk`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_SIMP_TAC[DIMINDEX_3; REAL_ARITH `&0 < tk ==> --tk <= &0`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  (* (S5) l <= 9 on the ball in the rescaled flow (FL7) *)
  SUBGOAL_THEN
   `!q'. q' IN mfd_ball (top,atlas) ((h:real->B->real^3^3)(--tk)) q (&2 * sqrt tk)
         ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[--(&2),&0]) (G:real->B->real^3^3))
                    (&0) p (&1) q' <= &9`
  ASSUME_TAC THENL
   [X_GEN_TAC `q':B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q':B) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in top (mfd_ball (top,atlas) ((h:real->B->real^3^3)(--tk)) q (&2 * sqrt tk))` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fl7" (MP_TAC o SPECL
      [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(&2 * tk)`; `&0`;
       `h:real->B->real^3^3`; `p:B`; `inv tk`; `tk:real`; `q':B`] o
      REWRITE_RULE[P2A_FLOW_SCALING_STATEMENT]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM p2b_klx] THEN USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* FL6 for G at tau0 = 1 *)
  USE_THEN "fl6" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(&2)`; `&0`;
     `G:real->B->real^3^3`; `p:B`; `r':real`; `&1`;
     `mfd_ball (top,atlas) ((h:real->B->real^3^3)(--tk)) q (&2 * sqrt tk)`] o
    REWRITE_RULE[p2ak0_fl6]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v / (inv tk * sqrt(inv tk))` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(h:real->B->real^3^3)(&0)`; `mfd_ball (top,atlas) ((h:real->B->real^3^3)(&0)) p r`;
                   `v / (inv tk * sqrt(inv tk))`; `inv tk`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_SIMP_TAC[DIMINDEX_3; REAL_LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(inv tk * sqrt(inv tk)) * v / (inv tk * sqrt(inv tk)) = v` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < tk` THEN UNDISCH_TAC `&0 < sqrt(inv tk)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_has_volume (top,atlas) ((G:real->B->real^3^3) (&0))
                   (mfd_ball (top,atlas) (G (&0)) p r') v` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
    UNDISCH_TAC `kappa0 * r' pow 3 <= v` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Volume of the balls B(q k, 2 sqrt(tau k)) from the limit by LIM_VOL, and *)
(* the noncollapsing core at (p,t0).                                        *)
(* ========================================================================= *)

let P2AK0_LIMVOL_LOWER = prove
 (`!kappa kappa' top atlas (h:real->B->real^3^3) tau q (top':B topology) atlas' g' xl.
     p2b_kappa_solution kappa (top,atlas) h /\
     (!k. &0 < tau k) /\ (!k. q k IN topspace top) /\
     p3_flow_limit_on (\k. p2b_kview (top,atlas) h) q (\k. --(tau k))
                      (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
     p2b_kappa_solution kappa' (top',atlas') (\t. g'(t + &1 / &2)) /\
     (!v. mfd_has_volume (top',atlas') (g'(&0)) (mfd_ball (top',atlas') (g'(&0)) xl (&1)) v
          ==> &1 / &40 <= v)
     ==> ?k0. !k. k0 <= k
                  ==> ?vk. mfd_has_volume (top,atlas) (h(--(tau k)))
                             (mfd_ball (top,atlas) (h(--(tau k))) (q k) (&2 * sqrt(tau k))) vk /\
                           &1 / &80 <= inv(tau k) * sqrt(inv(tau k)) * vk`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v1")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `h:real->B->real^3^3`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hs'") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm'") (K ALL_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KSOL_BASIC o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "cp'") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0)) /\
                mfd_complete (top',atlas') (g'(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rm'" (MP_TAC o SPEC `--(&1 / &2)`);
      USE_THEN "cp'" (MP_TAC o SPEC `--(&1 / &2)`)] THEN
    BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p3_flow_limit_on (\k. p2b_kview (top,atlas) (h:real->B->real^3^3)) (q:num->B)
                 (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                 (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                 (g':real->B->real^3^3) (xl:B)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(GEN_REWRITE_RULE I [P2C_FLOW_LIMIT_ON_WITH] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_TAC `phi:num->B->B`)) THEN
  SUBGOAL_THEN `(xl:B) IN topspace top' /\ (!k. (phi:num->B->B) k xl = q k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_flow_limit_with (\k. p2b_kview (top,atlas) (h:real->B->real^3^3)) (q:num->B)
                   (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->B)` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `&1`] MFD_HAS_VOLUME_BALL) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `&2`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`B:B->bool`; `B:B->bool`] LIM_VOL) THEN REWRITE_TAC[LIM_VOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`\k:num. p2b_kview (top,atlas) (h:real->B->real^3^3)`; `q:num->B`; `\k:num. --(tau k:real)`;
     `\k:num. inv(tau k:real)`; `{s:real | s < &1}`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`; `&1`; `&2`;
     `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl (&1))`;
     `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl (&2))`;
     `&1 / &80`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AK0_KVIEW_REG THEN
      EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
      ASM_SIMP_TAC[P2AK0_KVIEW_SLICE; REAL_ARITH `&0 < x ==> --x <= &0`]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[P2AK0_KVIEW_SLICE; REAL_ARITH `&0 < x ==> --x <= &0`] THEN
  SUBGOAL_THEN `&2 * inv(sqrt(inv(tau(k:num)))) = &2 * sqrt(tau k)` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_INV; REAL_INV_INV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk1:real` (X_CHOOSE_THEN `vk2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `vk2:real` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "v1" (MP_TAC o SPEC
    `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl (&1))`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Kappa0-noncollapsing at (p,t0) and the route theorem for MT Prop 9.58.    *)
(* ========================================================================= *)

let P2AK0_CORE = prove
 (`!(w:B->bool) kappa0.
     P2B_ASYM_SOLITON_AT_STATEMENT w /\ P2B_COR_9_44_STATEMENT w /\
     P2B_COR_9_10_STATEMENT w /\ P2A_FLOW_SCALING_STATEMENT w (:3) /\ p2ak0_fl6 w kappa0
     ==> !kappa top atlas (g:real->B->real^3^3) t0 p r.
           p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
           ~p2b_round (top,atlas) (g(&0)) /\ t0 <= &0 /\ p IN topspace top /\ &0 < r /\
           (!s y. t0 - r pow 2 < s /\ s <= t0 /\ y IN mfd_ball (top,atlas) (g t0) p r
                  ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2))
           ==> ?v. mfd_has_volume (top,atlas) (g t0) (mfd_ball (top,atlas) (g t0) p r) v /\
                   kappa0 * r pow 3 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "asym") (CONJUNCTS_THEN2 (LABEL_TAC "c944")
   (CONJUNCTS_THEN2 (LABEL_TAC "c910") (CONJUNCTS_THEN2 (LABEL_TAC "fl7") (LABEL_TAC "fl6"))))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))))))) THEN
  SUBGOAL_THEN `p2b_kappa_solution kappa (top,atlas) (\t. (g:real->B->real^3^3)(t + t0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK0_KSOL_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "asym" (MP_TAC o SPECL
    [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
     `\t. (g:real->B->real^3^3)(t + t0)`; `p:B`] o
    REWRITE_RULE[P2B_ASYM_SOLITON_AT_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `f:B->real` MP_TAC))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inf")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "l32")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)))))))) THEN
  (* the limit slice g'(0) is a Riemannian metric (the kappa-solution      *)
  (* clause at t = -1/2), as Cor 9.44 requires                            *)
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2BX_KSOL_FACTS o
      check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_kappa_solution"))
                           (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `--(&1 / &2)` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
   [(* compact round soliton: Cor 9.44 gives g(0) round *)
    USE_THEN "c944" (MP_TAC o SPECL
      [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
       `g:real->B->real^3^3`; `t0:real`; `tau:num->real`; `q:num->B`; `top':B topology`;
       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`] o
      REWRITE_RULE[P2B_COR_9_44_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the cylinder model in standard form at s = 0 *)
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_kappa_solution"))
                         (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (K ALL_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2b_cyl_model] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_cyl_model"))
                         (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `pm:real^3->B` (X_CHOOSE_THEN `lam:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `pm:real^3->B`; `lam:real`; `--(&1 / &2)`]
                P2ACM_CYL_STD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--(&1 / &2)`; `y:real^3`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "cylinder_flow"))
                           (concl th))) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `qs:real^3->B`) THEN
  SUBGOAL_THEN `!v. mfd_has_volume (top',atlas') ((g':real->B->real^3^3)(&0))
                      (mfd_ball (top',atlas') (g'(&0)) xl (&1)) v ==> &1 / &40 <= v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2ACM_STD_UNIT_BALL THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(g':real->B->real^3^3)(&0)`; `qs:real^3->B`;
                          `lam - --(&1 / &2)`; `xl:B`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `p3_flow_limit_on (\k. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + t0)))
                   (q:num->B) (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (xl:B)` THEN
    REWRITE_TAC[p3_flow_limit_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t. (g:real->B->real^3^3)(t + t0)`; `tau:num->real`; `q:num->B`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`] P2AK0_LIMVOL_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  USE_THEN "inf" (MP_TAC o SPEC `r pow 2`) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k0 + N:num` o check (fun th ->
    can (find_term ((=) `k0:num`)) (concl th))) THEN
  REWRITE_TAC[LE_ADD] THEN DISCH_THEN(X_CHOOSE_THEN `vk:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r pow 2 <= tau(k0 + N:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `\t. (g:real->B->real^3^3)(t + t0)`;
                 `p:B`; `r:real`; `tau(k0 + N:num):real`; `q(k0 + N:num):B`; `vk:real`]
                P2AK0_RESCALE_FL6) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
      USE_THEN "curv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC P2AK0_LBALL THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `q(k0 + N:num):B`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

(* The route theorem. *)

let P2AK0_PROP_9_58_ROUTE = prove
 (`!w:B->bool. P2B_PROP_9_58_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_58_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `kappa0:real` STRIP_ASSUME_TAC o MATCH_MP P2AK0_FL6_KAPPA0) THEN
  REWRITE_TAC[P2B_PROP_9_58_STATEMENT] THEN EXISTS_TAC `kappa0:real` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
    check (fun th -> can (find_term ((=) `kappa:real`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_kappa_solution"))
                         (concl th))) THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r0:real` THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_vball; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
  ASM_CASES_TAC `t <= &0` THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`] P2AK0_CORE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]);;

