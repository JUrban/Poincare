(* ========================================================================= *)
(* Unit pc_p2b_cylnecks: piece (h) of the statements of pc_p2b_c994req       *)
(* (MT Thm 9.93 / Cor 9.94 in the length-L form): the one-to-one cylinder    *)
(* model has evolving delta-necks of every length L at every (x,t),          *)
(* P2BCY_CYL_MODEL_NECKS |- !w. P2B_CYL_MODEL_NECKS_STATEMENT w.  At         *)
(* x = p y0 and time t the neck is p composed with the radial power map      *)
(* of exponent c = sqrt((lam - t)/lam) and the dilation by |y0|;             *)
(* R(x) = 1/(lam - t) and the normalized family R g(t + s/R) is exactly      *)
(* cylinder_flow s in that chart, so all closeness distances are 0.          *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_979.ml";;      (* P2B9_EVOLVING_NECK_ALT, P2B9_PARAM_LSCALAR_SCALED *)
needs "src/pc_smt_product.ml";;  (* MFP_PARAM_LOCAL *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Copies, under new names, of small lemmas from units outside the load      *)
(* closure of this unit; each block names its source.  The cylinder-type     *)
(* fields p2bcy_cab A B and their power-map pullback come from pc_p2b_x2     *)
(* (whose needs line would add 131 files to the closure).                    *)
(* ========================================================================= *)

(* Copy of P2BL_LNABLA_ITER_ZERO (pc_p2b_ltr.ml). *)

let P2BCY_LNABLA_ITER_ZERO = prove
 (`!k l (G:real^N->real^N^N). lnabla_iter k l G (\x u. &0) = (\x u. &0)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[lnabla_iter] THEN
  REWRITE_TAC[FUN_EQ_THM; LRG_LNABLA_ZERO]);;

(* Copy of P2BL_LCK_DIST2_REFL (pc_p2b_ltr.ml). *)

let P2BCY_LCK_DIST2_REFL = prove
 (`!k (G:real^N->real^N^N) y. lck_dist2 k G G y = &0`,
  REWRITE_TAC[lck_dist2; REAL_SUB_REFL] THEN
  REWRITE_TAC[ETA_AX; GSYM(REWRITE_CONV[ETA_AX] `\x:real^N u:num->real^N. &0`)] THEN
  REWRITE_TAC[P2BCY_LNABLA_ITER_ZERO; ltnorm2; REAL_MUL_LZERO; SUM_0]);;

(* Copy of P2ACM_MPULLBACK_PT (pc_p2a_cylm.ml). *)

let P2BCY_MPULLBACK_PT = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) G' y.
     G (h y) = G' (h y) ==> mpullback h G y = mpullback h G' y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mpullback]);;

(* Copy of P2BX2_RFS_PULLBACK_PRECOMP (pc_p2b_x2.ml). *)

let P2BCY_RFS_PULLBACK_PRECOMP = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) t (h:real^N->real^N) h' v.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     diffeomorphism_on t s h h' /\ v IN t
     ==> rfs_pullback atlas (e o h) g v = mpullback h (rfs_pullback atlas e g) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) v IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on t s (h:real^N->real^N) h'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas t ((e:real^N->A) o (h:real^N->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `s:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->A)(h(v:real^N)) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)(h(v:real^N))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A)(h(v:real^N)))`,
           `ch:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `t:real^N->bool`; `(e:real^N->A) o (h:real^N->real^N)`; `V:A->bool`;
                 `psi:A->real^N`; `v:real^N`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas (e:real^N->A) (g:A->real^N^N) (h(v:real^N)) =
                mpullback (psi o e) (metric_local atlas (V,psi) g) (h v)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mpullback (h:real^N->real^N) (rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)) v =
                mpullback h (mpullback (psi o e) (metric_local atlas (V,psi) g)) v`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[mpullback]; ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^N->bool` THEN
    UNDISCH_TAC `diffeomorphism_on t s (h:real^N->real^N) h'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N`
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN V}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* Copy of p2bx2_cab (pc_p2b_x2.ml). *)

let p2bcy_cab = new_definition
 `p2bcy_cab (A:real) (B:real) (z:real^3) =
    (&2 / norm z pow 2) %%
    (A %% mat 1 + ((B - A) / norm z pow 2) %% ((lambda i j. z$i * z$j):real^3^3))`;;

(* Copy of P2BX2_CAB_CYL (pc_p2b_x2.ml). *)

let P2BCY_CAB_CYL = prove
 (`!lam u z:real^3.
     ~(lam = &0) ==> lam %% cylinder_flow (u / lam) z = p2bcy_cab (lam - u) lam z`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; cylinder_flow; p2bcy_cab; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  UNDISCH_TAC `~(lam = &0)` THEN CONV_TAC REAL_FIELD);;

(* Copy of P2BX2_PW_PULLBACK_CAB (pc_p2b_x2.ml). *)

let P2BCY_PW_PULLBACK_CAB = prove
 (`!e A B y:real^3.
     ~(y = vec 0)
     ==> mpullback (\z:real^3. ((norm z pow 2) rpow e) % z) (p2bcy_cab A B) y =
         p2bcy_cab A ((&2 * e + &1) pow 2 * B) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  ASM_REWRITE_TAC[p2bcy_cab; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < ((y:real^3) dot y) rpow e` MP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The model computation.  Cylinder-type fields p2bcy_cab A B scale linearly *)
(* in (A,B), are invariant under dilations, and the neck map z |-> rho       *)
(* (|z|^2)^e z (a dilation after the radial power map of pc_rf_basic) pulls  *)
(* p2bcy_cab A B back to p2bcy_cab A ((2e+1)^2 B).                           *)
(* ========================================================================= *)

let P2BCY_CAB_CMUL = prove
 (`!c A B (z:real^3). c %% p2bcy_cab A B z = p2bcy_cab (c * A) (c * B) z`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; p2bcy_cab; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[real_div] THEN
  CONV_TAC REAL_RING);;

let P2BCY_CAB_DIAG = prove
 (`!A (z:real^3). p2bcy_cab A A z = A %% cylinder_flow (&0) z`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; p2bcy_cab; cylinder_flow; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[real_div] THEN
  CONV_TAC REAL_RING);;

let P2BCY_CAB_DIL = prove
 (`!rho A B (w:real^3).
     &0 < rho /\ ~(w = vec 0)
     ==> p2bcy_cab A B (rho % w) = inv(rho pow 2) %% p2bcy_cab A B w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; p2bcy_cab; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT; VECTOR_MUL_COMPONENT; NORM_MUL] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN COND_CASES_TAC THEN
  UNDISCH_TAC `&0 < norm(w:real^3)` THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD);;

(* The dilations of real^3 minus the origin. *)

let P2BCY_SCALE_DIFFEO = prove
 (`!c. &0 < c
       ==> diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
             (\w. c % w) (\w. inv c % w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(inv c = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0];
      DISCH_TAC THEN EXISTS_TAC `inv c % y:real^3` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID; VECTOR_MUL_EQ_0]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0];
      DISCH_TAC THEN EXISTS_TAC `c % y:real^3` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID; VECTOR_MUL_EQ_0]];
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `c:real`; `\w:real^3. w`]
                  SMOOTH_MAP_ON_CMUL_OPEN) THEN
    SIMP_TAC[SMOOTH_MAP_ON_ID; OPEN_DELETE; OPEN_UNIV];
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `inv c`; `\w:real^3. w`]
                  SMOOTH_MAP_ON_CMUL_OPEN) THEN
    SIMP_TAC[SMOOTH_MAP_ON_ID; OPEN_DELETE; OPEN_UNIV]]);;

(* Dilations preserve cylinder-type fields. *)

let P2BCY_DIL_PULLBACK = prove
 (`!rho A B (w:real^3).
     &0 < rho /\ ~(w = vec 0)
     ==> mpullback (\z:real^3. rho % z) (p2bcy_cab A B) w = p2bcy_cab A B w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\z:real^3. rho % z) has_derivative (\v. rho % v)) (at w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. z`; `\v:real^3. v`; `at(w:real^3)`; `rho:real`]
                  HAS_DERIVATIVE_CMUL) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR o check (fun th ->
    is_comb(concl th) && is_comb(rator(concl th)))) THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN ASM_SIMP_TAC[P2BCY_CAB_DIL] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `~(rho = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* The neck map: a dilation after the radial power map. *)

let P2BCY_NECKMAP_PULLBACK = prove
 (`!rho e A B (y:real^3).
     &0 < rho /\ ~(y = vec 0)
     ==> mpullback ((\w:real^3. rho % w) o (\z:real^3. ((norm z pow 2) rpow e) % z))
                   (p2bcy_cab A B) y =
         p2bcy_cab A ((&2 * e + &1) pow 2 * B) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. ((norm z pow 2) rpow e) % z`; `\w:real^3. rho % w`;
                 `p2bcy_cab A B`; `y:real^3`] P2A_MPULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\v:real^3. ((norm(y:real^3) pow 2) rpow e) % v +
                             (e * (norm y pow 2) rpow (e - &1) * &2 * (y dot v)) % y` THEN
      MATCH_MP_TAC RFB_PW_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[differentiable] THEN EXISTS_TAC `\v:real^3. rho % v` THEN
      MP_TAC(ISPECL [`\z:real^3. z`; `\v:real^3. v`;
                     `at(((norm(y:real^3) pow 2) rpow e) % y)`; `rho:real`]
                    HAS_DERIVATIVE_CMUL) THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (\z:real^3. ((norm z pow 2) rpow e) % z) (p2bcy_cab A B) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BCY_MPULLBACK_PT THEN BETA_TAC THEN
    MATCH_MP_TAC P2BCY_DIL_PULLBACK THEN ASM_SIMP_TAC[RFB_PW_NONZERO];
    ASM_SIMP_TAC[P2BCY_PW_PULLBACK_CAB]]);;

(* The power map fixes the unit sphere. *)

let P2BCY_PW_UNIT = prove
 (`!e z:real^3. z IN sphere(vec 0,&1) ==> ((norm z pow 2) rpow e) % z = z`,
  REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; RPOW_ONE; VECTOR_MUL_LID]);;

(* ========================================================================= *)
(* Piece (h).  At x = p y0 and time t <= 0 let c = 2 e0 + 1 > 0 with c^2 lam *)
(* = lam - t and e = p o hm, hm z = |y0| (|z|^2)^e0 z.  Then e pulls g(tau)  *)
(* back to p2bcy_cab (lam - tau) (lam - t) for tau <= 0, so R(x) = 1/(lam -  *)
(* t) and R g(t + s/R) is exactly cylinder_flow s in the chart e: every      *)
(* closeness distance is 0.                                                  *)
(* ========================================================================= *)

(* The neck domains avoid the origin. *)

let P2BCY_NECK_DOM_NZ = prove
 (`!eps. rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; rfs_neck_dom; annulus; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `exp(--inv(sqrt(&2) * eps)) < norm(vec 0:real^3)` THEN
  REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `--inv(sqrt(&2) * eps)` REAL_EXP_POS_LT) THEN
  REAL_ARITH_TAC);;

(* The main theorem. *)

let P2BCY_CYL_MODEL_NECKS = prove
 (`!w:B->bool. P2B_CYL_MODEL_NECKS_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_CYL_MODEL_NECKS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rm") (CONJUNCTS_THEN2 (LABEL_TAC "img")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "pb"))))))) THEN
  MAP_EVERY X_GEN_TAC [`delta:real`; `L:real`; `t:real`; `x:B`] THEN STRIP_TAC THEN
  (* x = p y0 *)
  SUBGOAL_THEN `?y0:real^3. ~(y0 = vec 0) /\ (p:real^3->B) y0 = x`
  (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(x:B) IN topspace top` THEN
    USE_THEN "img" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* p is a parametrization of real^3 minus the origin *)
  SUBGOAL_THEN `mfd_param top atlas ((:real^3) DELETE vec 0) (p:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFP_PARAM_LOCAL THEN ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN CONJ_TAC THENL
     [USE_THEN "inj" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `~(z:real^3 = vec 0)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(z:real^3,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `v:real^3` THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(z:real^3,vec 0) < r` THEN REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the exponent *)
  SUBGOAL_THEN `&0 < lam - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `--t / (lam - t)` RFB_CYL_EXPONENT) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&2 * e0 + &1) pow 2 * lam = lam - t` ASSUME_TAC THENL
   [UNDISCH_TAC `(&2 * e0 + &1) pow 2 * (&1 - --t / (lam - t)) = &1` THEN
    UNDISCH_TAC `&0 < lam - t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the neck map *)
  ABBREV_TAC `rho = norm(y0:real^3)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `hm = (\w:real^3. rho % w) o (\z:real^3. ((norm z pow 2) rpow e0) % z)` THEN
  ABBREV_TAC `hm' = (\z:real^3. ((norm z pow 2) rpow (--e0 / (&2 * e0 + &1))) % z) o
                    (\w:real^3. inv rho % w)` THEN
  SUBGOAL_THEN `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) hm hm'`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hm"; "hm'"] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFB_PW_DIFFEO THEN UNDISCH_TAC `&0 < &2 * e0 + &1` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC P2BCY_SCALE_DIFFEO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> ~((hm:real^3->real^3) z = vec 0)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                   (hm:real^3->real^3) hm'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `(hm:real^3->real^3) z`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas ((:real^3) DELETE vec 0) ((p:real^3->B) o hm)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`;
                          `hm':real^3->real^3`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  (* the pullbacks of the slices by the neck chart *)
  SUBGOAL_THEN
   `!tau z. tau <= &0 /\ ~(z = vec 0)
            ==> rfs_pullback atlas ((p:real^3->B) o hm) ((g:real->B->real^3^3) tau) z =
                p2bcy_cab (lam - tau) (lam - t) z`
  (LABEL_TAC "pf") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) tau`; `(:real^3) DELETE vec 0`; `p:real^3->B`;
                   `(:real^3) DELETE vec 0`; `hm:real^3->real^3`; `hm':real^3->real^3`;
                   `z:real^3`] P2BCY_RFS_PULLBACK_PRECOMP) THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (hm:real^3->real^3) (p2bcy_cab (lam - tau) lam) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BCY_MPULLBACK_PT THEN
      SUBGOAL_THEN `~((hm:real^3->real^3) z = vec 0)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "pb" (fun th -> ASM_SIMP_TAC[th]) THEN
      MATCH_MP_TAC P2BCY_CAB_CYL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "hm" THEN ASM_SIMP_TAC[P2BCY_NECKMAP_PULLBACK]];
    ALL_TAC] THEN
  (* the centre: x = e z0 with z0 on the unit sphere *)
  SUBGOAL_THEN `inv rho % (y0:real^3) IN sphere(vec 0,&1) /\
                ((p:real^3->B) o hm) (inv rho % y0) = x` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `inv rho % (y0:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "hm" THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[P2BCY_PW_UNIT] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  (* the scalar curvature at x *)
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) t) x = inv(lam - t)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `((p:real^3->B) o (hm:real^3->real^3)) (inv rho % (y0:real^3)) = (x:B)`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `(:real^3) DELETE vec 0`;
                   `(p:real^3->B) o (hm:real^3->real^3)`; `inv rho % (y0:real^3)`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[IN_DELETE; IN_UNIV] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lscalar (\z:real^3. (lam - t) %% cylinder_flow (&0) z) (inv rho % y0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "pf" (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]) THEN
      REWRITE_TAC[P2BCY_CAB_DIAG];
      MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`; `lam - t`;
                     `inv rho % (y0:real^3)`] LSCALAR_SCALE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01; IN_DELETE; IN_UNIV] THEN
        ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
        DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`&0`; `inv rho % (y0:real^3)`] RFB_CYL_SCALAR) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LT_01] THEN
        ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
        DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `&0 < lam - t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the normalized family is the shrinking cylinder *)
  SUBGOAL_THEN
   `!s z. s <= &0 /\ ~(z = vec 0)
          ==> inv(lam - t) %%
              rfs_pullback atlas ((p:real^3->B) o hm)
                           ((g:real->B->real^3^3) (t + s / inv(lam - t))) z =
              cylinder_flow s z`
  (LABEL_TAC "fam") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t + s / inv(lam - t) <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_INV] THEN
      MATCH_MP_TAC(REAL_ARITH `t <= &0 /\ s * l <= &0 ==> t + s * l <= &0`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= --s * l ==> s * l <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "pf" (fun th -> ASM_SIMP_TAC[th]) THEN REWRITE_TAC[P2BCY_CAB_CMUL] THEN
    MP_TAC(ISPECL [`&1`; `s:real`; `z:real^3`] P2BCY_CAB_CYL) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; REAL_DIV_1; MATRIX_CMUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN BINOP_TAC THEN
    UNDISCH_TAC `&0 < lam - t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the evolving neck *)
  EXISTS_TAC `(p:real^3->B) o (hm:real^3->real^3)` THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar;
              IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open (rfs_neck_dom delta) /\
                rfs_neck_dom delta SUBSET (:real^3) DELETE vec 0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_NECK_DOM_OPEN; P2BCY_NECK_DOM_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom delta ==> ~(y = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck_dom delta SUBSET (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* each closeness distance vanishes *)
  SUBGOAL_THEN
   `!s k y. s <= &0 /\ y IN rfs_neck_dom delta
            ==> lck_dist2 k (cylinder_flow s)
                  (\z. inv(lam - t) %%
                       rfs_pullback atlas ((p:real^3->B) o hm)
                                    ((g:real->B->real^3^3) (t + s / inv(lam - t))) z) y = &0`
  (LABEL_TAC "zero") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `cylinder_flow s`; `cylinder_flow s`; `cylinder_flow s`;
                   `\z. inv(lam - t) %%
                        rfs_pullback atlas ((p:real^3->B) o hm)
                                     ((g:real->B->real^3^3) (t + s / inv(lam - t))) z`;
                   `(:real^3) DELETE vec 0`; `y:real^3`] LCK_DIST2_LOCAL) THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      USE_THEN "fam" (fun th -> ASM_SIMP_TAC[th]);
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[P2BCY_LCK_DIST2_REFL]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the neck at time t *)
    REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `inv rho % (y0:real^3)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `&0` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "zero" (MP_TAC o SPECL [`&0`; `rfs_kreg delta`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL])];
    (* 0 < L *)
    ASM_REAL_ARITH_TAC;
    (* persistence *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s <= &0` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `(:real^3) DELETE vec 0`] THEN
    ASM_REWRITE_TAC[];
    (* the family closeness *)
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "zero" (MP_TAC o SPECL [`s:real`; `rfs_kreg delta`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL])]);;

