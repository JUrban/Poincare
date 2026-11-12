(* ========================================================================= *)
(* pc_z2x_neck: exact static necks of the two-to-one Z/2 cylinder model      *)
(* (p2azq_model of pc_p2a_zq): for every unit vector u and                   *)
(* rho > exp(inv(sqrt 2 eps)), p o (rho %) is an eps-neck at p(rho u) with   *)
(* closeness distance 0 (Z2X_MODEL_NECK).  Used by the Z/2 exclusion         *)
(* (pc_z2x_excl) and by the twisted model (pc_rfa_ktw).                      *)
(* ========================================================================= *)

needs "src/pc_p2a_zq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The static necks of the two-to-one model.  For the model p of             *)
(* p2azq_model with pullback lam cylinder_flow(0), the map e = p o (rho %)   *)
(* with rho > exp(inv(sqrt 2 eps)) is an eps-neck at p(rho u) for every      *)
(* unit vector u: the dilated neck domain lies in norm y > 1, where p is a   *)
(* parametrization (P2AZQ_PARAM_OUT); cylinder_flow(0) is dilation invariant *)
(* and has scalar curvature 1, so R = inv lam at the centre, the normalized  *)
(* pullback is exactly cylinder_flow(0) and every closeness distance is 0.   *)
(* Two 3-line copies of lemmas of pc_p2b_ltr keep the dependencies of this   *)
(* file those of pc_p2a_zq: Z2X_LNABLA_ITER_ZERO = P2BL_LNABLA_ITER_ZERO and *)
(* Z2X_LCK_DIST2_REFL = P2BL_LCK_DIST2_REFL.                                 *)
(* ========================================================================= *)

let Z2X_LNABLA_ITER_ZERO = prove
 (`!k l (G:real^N->real^N^N). lnabla_iter k l G (\x u. &0) = (\x u. &0)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[lnabla_iter] THEN
  REWRITE_TAC[FUN_EQ_THM; LRG_LNABLA_ZERO]);;

let Z2X_LCK_DIST2_REFL = prove
 (`!k (G:real^N->real^N^N) y. lck_dist2 k G G y = &0`,
  REWRITE_TAC[lck_dist2; REAL_SUB_REFL] THEN
  REWRITE_TAC[ETA_AX; GSYM(REWRITE_CONV[ETA_AX] `\x:real^N u:num->real^N. &0`)] THEN
  REWRITE_TAC[Z2X_LNABLA_ITER_ZERO; ltnorm2; REAL_MUL_LZERO; SUM_0]);;

let Z2X_CYL0 = prove
 (`!y:real^3. cylinder_flow (&0) y = (&2 / norm y pow 2) %% mat 1`,
  GEN_TAC THEN REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID]);;

let Z2X_CYL0_DIL = prove
 (`!lam rho v:real^3.
     &0 < rho /\ ~(v = vec 0)
     ==> (rho pow 2) %% (lam %% cylinder_flow (&0) (rho % v)) = lam %% cylinder_flow (&0) v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[Z2X_CYL0; MATRIX_CMUL_ASSOC; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^3)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD);;

let Z2X_NECK_DOM_FACTS = prove
 (`!eps. &0 < eps
         ==> &0 < inv(sqrt(&2) * eps) /\
             rfs_neck_dom eps = {w:real^3 | exp(--(inv(sqrt(&2) * eps))) < norm w /\
                                            norm w < exp(inv(sqrt(&2) * eps))} /\
             open(rfs_neck_dom eps) /\
             (!u:real^3. norm u = &1 ==> u IN rfs_neck_dom eps) /\
             sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < &1 /\ &1 < exp(inv(sqrt(&2) * eps))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_neck_dom; annulus; APX_NECK_DOM_OPEN] THEN
  REWRITE_TAC[GSYM rfs_neck_dom; APX_NECK_DOM_OPEN] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; SUBSET; IN_SPHERE_0] THEN
  ASM_SIMP_TAC[]);;

let Z2X_MODEL_NECK = prove
 (`!top atlas (g:B->real^3^3) p lam eps rho (u:real^3).
     p2azq_model (top,atlas) g p lam /\ &0 < eps /\ exp(inv(sqrt(&2) * eps)) < rho /\
     norm u = &1
     ==> rfs_neck (top,atlas) g eps (p (rho % u)) (p o (\w. rho % w)) /\
         mfd_scalar atlas g (p (rho % u)) = inv lam /\
         mfd_param top atlas {y:real^3 | &1 < norm y} p /\
         (!w:real^3. w IN rfs_neck_dom eps ==> &1 < norm(rho % w)) /\
         (!v:real^3. v IN rfs_neck_dom eps
                     ==> rfs_pullback atlas (p o (\w. rho % w)) g v =
                         lam %% cylinder_flow (&0) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AZQ_PARAM_OUT) THEN
  UNDISCH_TAC `p2azq_model (top,atlas) (g:B->real^3^3) p lam` THEN
  REWRITE_TAC[p2azq_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "img")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "pb"))))))) THEN
  MP_TAC(SPEC `eps:real` Z2X_NECK_DOM_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nd")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `exp(inv(sqrt(&2) * eps))` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  (* the dilated neck domain lies in norm > 1 *)
  SUBGOAL_THEN `!w:real^3. w IN rfs_neck_dom eps ==> &1 < norm(rho % w)` (LABEL_TAC "out") THENL
   [X_GEN_TAC `w:real^3` THEN USE_THEN "nd" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `exp(inv(sqrt(&2) * eps)) * exp(--(inv(sqrt(&2) * eps))) = &1`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0]; ALL_TAC] THEN
    SUBGOAL_THEN `exp(inv(sqrt(&2) * eps)) * exp(--(inv(sqrt(&2) * eps))) <
                  rho * exp(--(inv(sqrt(&2) * eps)))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `rho * exp(--(inv(sqrt(&2) * eps))) < rho * norm(w:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "nd" (K ALL_TAC) THEN
  (* the neck map is a parametrization *)
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((p:real^3->B) o (\w. rho % w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`{y:real^3 | &1 < norm y}`;
                          `IMAGE (\w:real^3. rho % w) (rfs_neck_dom eps)`;
                          `\y:real^3. inv rho % y`] THEN
    ASM_SIMP_TAC[MFP_SCALE_DIFFEO] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    USE_THEN "out" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the pullback *)
  SUBGOAL_THEN `!v:real^3. v IN rfs_neck_dom eps
                           ==> rfs_pullback atlas ((p:real^3->B) o (\w. rho % w)) g v =
                               lam %% cylinder_flow (&0) v` (LABEL_TAC "pf") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `{y:real^3 | &1 < norm y}`; `rfs_neck_dom eps`;
                   `p:real^3->B`; `rho:real`] APX_RFS_PULLBACK_DILATE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "out" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:real^3) IN rfs_neck_dom eps`)]) THEN
    SUBGOAL_THEN `&1 < norm(rho % v:real^3)` ASSUME_TAC THENL
     [USE_THEN "out" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(v:real^3 = vec 0) /\ ~(rho % v:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `&1 < norm(rho % v:real^3)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "pb" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(rho % v:real^3 = vec 0)`)]) THEN
    MATCH_MP_TAC Z2X_CYL0_DIL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the scalar curvature at the centre *)
  SUBGOAL_THEN `(u:real^3) IN rfs_neck_dom eps /\ ~(u = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!u:real^3. norm u = &1 ==> u IN rfs_neck_dom eps`) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((p:real^3->B) o (\w. rho % w)) u = p (rho % u)` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) ((p:real^3->B) (rho % u)) = inv lam` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `((p:real^3->B) o (\w. rho % w)) u = p (rho % u)`)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `rfs_neck_dom eps`; `(p:real^3->B) o (\w. rho % w)`; `u:real^3`]
                  APX_PULLBACK_SCALAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lscalar (\z:real^3. lam %% cylinder_flow (&0) z) u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "pf" ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`; `lam:real`;
                   `u:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01; IN_DELETE; IN_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`&0`; `u:real^3`] RFB_CYL_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the neck *)
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:real^3` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    TRANS_TAC EQ_TRANS
      `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (cylinder_flow (&0)) (y:real^3)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[Z2X_LCK_DIST2_REFL]] THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    USE_THEN "pf" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN rfs_neck_dom eps`)]) THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    SUBGOAL_THEN `inv lam * lam = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_LID]]);;

